import ACS12.PressureMaximum
import ACS12.PureCMoments
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! The exact full line-law debit used in the maximum-root comparison. -/
namespace ACS12.Pressure

open Set Filter MeasureTheory CenteredCircle.AllN
open GammaMeasure (powerTail powerTail_summable powerTail_shift pureIntegral_scale)
open GammaDeficit (lineDensity lineDensity_exp_integral)

noncomputable def lineMaximumDebit (p Q : ℝ) : ℝ :=
  ∫ s : ℝ in Ioi 0, lineDensity p s * (s * pressureBose Q s ^ 2)

noncomputable def boseDebit (p : ℝ) : ℝ := p * (powerTail p 1 - powerTail (p + 1) 1)

private theorem geometric_square_tsum {q : ℝ} (hq : 0 ≤ q) (hq₁ : q < 1) :
    (q / (1 - q)) ^ 2 = ∑' j : ℕ, ((j : ℝ) + 1) * q ^ (j + 2) := by
  let f (j : ℕ) := q ^ j
  have hF := hasSum_geometric_of_lt_one hq hq₁
  have hNorm : Summable (fun j => ‖f j‖) := by
    simpa only [f,Real.norm_of_nonneg (pow_nonneg hq _)] using hF.summable
  have h := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hNorm hNorm
  change (∑' j, q ^ j) * (∑' j, q ^ j) = _ at h
  rw [hF.tsum_eq,← pow_two] at h
  calc
    _ = q ^ 2 * ((1 - q)⁻¹ ^ 2) := by rw [div_eq_mul_inv,mul_pow]
    _ = q ^ 2 * ∑' n : ℕ, ∑ x ∈ Finset.antidiagonal n, f x.1 * f x.2 := by rw [h]
    _ = _ := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro j
      have hTerm (x : ℕ × ℕ) (hx : x ∈ Finset.antidiagonal j) : f x.1 * f x.2 = q ^ j := by
        dsimp only [f]
        rw [← pow_add,Finset.mem_antidiagonal.mp hx]
      rw [Finset.sum_congr rfl hTerm,Finset.sum_const,Finset.Nat.card_antidiagonal,nsmul_eq_mul,
        Nat.cast_add,Nat.cast_one,pow_add q j 2]
      ring

private theorem lineMaximumDebit_one_eq {p : ℝ} (hp : 1 < p) : lineMaximumDebit p 1 = boseDebit p := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  let f (j : ℕ) (s : ℝ) := p * (((j : ℝ) + 1) *
    (lineDensity (p + 1) s * Real.exp (-s * ((j : ℝ) + 2))))
  let G (j : ℕ) := p * (((j : ℝ) + 2) ^ (-p) - ((j : ℝ) + 2) ^ (-(p + 1)))
  have hp₀ := zero_lt_one.trans hp
  have hDensity {s : ℝ} (hs : 0 < s) : lineDensity p s * s = p * lineDensity (p + 1) s := by
    unfold lineDensity
    rw [Real.Gamma_add_one hp₀.ne',add_sub_cancel_right,Real.rpow_sub_one hs.ne']
    field_simp [hs.ne',hp₀.ne',(Real.Gamma_pos_of_pos hp₀).ne']
  have hI (j : ℕ) : Integrable (f j) μ := by
    have h := (GammaDeficit.lineDensity_exp_integrable (by positivity : 0 < p + 1)
      (by positivity : 0 < (j : ℝ) + 2)).const_mul (p * ((j : ℝ) + 1))
    apply h.congr
    exact Eventually.of_forall fun s => by dsimp only [f]; ring
  have hG (j : ℕ) : (∫ s : ℝ, f j s ∂μ) = G j := by
    dsimp only [f,G]
    rw [integral_const_mul,integral_const_mul,lineDensity_exp_integral (by positivity : 0 < p + 1)
      (by positivity : 0 < (j : ℝ) + 2),show -p = -(p + 1) + 1 by ring,
      Real.rpow_add_one (by positivity : (j : ℝ) + 2 ≠ 0)]
    ring
  have hGSum : Summable G := by
    have h := ((powerTail_summable hp 2).sub (powerTail_summable (by linarith : 1 < p + 1) 2)).mul_left p
    exact h.congr fun j => by dsimp only [G]; push_cast; ring_nf
  have hNorm (j : ℕ) : (∫ s : ℝ, ‖f j s‖ ∂μ) = ∫ s : ℝ, f j s ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0 < s := hs
    exact Real.norm_of_nonneg (by dsimp only [f,lineDensity]; positivity)
  have hSum : Summable (fun j => ∫ s : ℝ, ‖f j s‖ ∂μ) := by
    simp_rw [hNorm,hG]
    exact hGSum
  have hInt := integral_tsum_of_summable_integral_norm hI hSum
  simp_rw [hG] at hInt
  have hPoint (s : ℝ) (hs : 0 < s) : lineDensity p s * (s * pressureBose 1 s ^ 2) = ∑' j, f j s := by
    have hB := geometric_square_tsum (Real.exp_pos (-s)).le (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hs))
    have hB' : pressureBose 1 s = Real.exp (-s) / (1 - Real.exp (-s)) := by
      simp only [pressureBose,periodicDen,mul_one,one_mul]
    rw [hB',hB,← mul_assoc,hDensity hs,← tsum_mul_left]
    apply tsum_congr
    intro j
    dsimp only [f]
    rw [← Real.exp_nat_mul,show ((j + 2 : ℕ) : ℝ) * -s = -s * ((j : ℝ) + 2) by push_cast; ring]
    ring
  unfold lineMaximumDebit
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s hs => hPoint s hs)]
  change (∫ s : ℝ, ∑' j, f j s ∂μ) = _
  rw [← hInt]
  unfold G
  rw [tsum_mul_left]
  have hE (j : ℕ) : (j : ℝ) + 2 = ((2 : ℕ) : ℝ) + j := by push_cast; ring
  simp_rw [hE]
  rw [(powerTail_summable hp 2).tsum_sub (powerTail_summable (by linarith : 1 < p + 1) 2)]
  change p * (powerTail p 2 - powerTail (p + 1) 2) = boseDebit p
  rw [powerTail_shift hp 1,powerTail_shift (by linarith : 1 < p + 1) 1,boseDebit]
  simp only [Nat.cast_one,Real.one_rpow]
  ring

theorem lineMaximumDebit_eq {p Q : ℝ} (hp : 1 < p) (hQ : 0 < Q) :
    lineMaximumDebit p Q = Q ^ (1 - p) * boseDebit p := by
  let g (s : ℝ) := s * pressureBose 1 s ^ 2
  have hB (s : ℝ) : pressureBose Q s = Q * pressureBose 1 (Q * s) := by
    simp only [pressureBose,periodicDen,one_mul,mul_one,neg_mul,mul_comm s Q]
  unfold lineMaximumDebit
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun s => Q * (lineDensity p s * g (Q * s)))
    (fun s _ => by rw [hB]; dsimp only [g]; ring),integral_const_mul,pureIntegral_scale hQ]
  change Q * (Q ^ (-p) * lineMaximumDebit p 1) = _
  rw [lineMaximumDebit_one_eq hp,← mul_assoc]
  have hPow : Q * Q ^ (-p) = Q ^ (1 - p) := by
    nth_rw 1 [← Real.rpow_one Q]
    rw [← Real.rpow_add hQ]
    ring_nf
  rw [hPow]

theorem lineMaximumDebit_integrable {p Q : ℝ} (hp : 1 < p) (hQ : 0 < Q) :
    IntegrableOn (fun s => lineDensity p s * (s * pressureBose Q s ^ 2)) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  change lineMaximumDebit p Q ≠ 0
  rw [lineMaximumDebit_eq hp hQ]
  have hP : powerTail (p + 1) 1 < powerTail p 1 := by
    apply (powerTail_summable (by linarith : 1 < p + 1) 1).tsum_lt_tsum
      (fun i : ℕ => Real.rpow_le_rpow_of_exponent_le
        (show (1 : ℝ) ≤ (1 : ℕ) + (i : ℝ) by simpa only [Nat.cast_one] using le_add_of_nonneg_right (Nat.cast_nonneg i))
        (by linarith))
      (i := 1) _ (powerTail_summable hp 1)
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  exact (mul_pos (Real.rpow_pos_of_pos hQ _) (mul_pos (zero_lt_one.trans hp) (sub_pos.mpr hP))).ne'

end ACS12.Pressure

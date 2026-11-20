import ACS12.JointGapK
import ACS12.GammaBinomialLaw

/-! The full squared Bose moments used by the sharp far-corner prices. -/
namespace ACS12.GammaMeasure

open MeasureTheory Set Filter
open scoped BigOperators
open GammaDeficit (lineDensity gamma_exp_integral)
open CenteredCircle.AllN (expHead_den_pos)

theorem boseSquaredMoment_integral {r : ℝ} (hr : 1 < r) {m : ℕ} (hm : 0 < m) :
    (∫ s : ℝ in Ioi 0, s ^ r * (Real.exp (-s * m) / (1 - Real.exp (-s)) ^ 2)) =
      Real.Gamma (r + 1) * (powerTail r m - ((m : ℝ) - 1) * powerTail (r + 1) m) := by
  let f (j : ℕ) (s : ℝ) := ((j : ℝ) + 1) * (s ^ r * Real.exp (-((m : ℝ) + j) * s))
  let μ := volume.restrict (Ioi (0 : ℝ))
  have hm₀ : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hr₀ := zero_lt_one.trans hr
  have hj (j : ℕ) : 0 < (m : ℝ) + (j : ℝ) := by positivity
  have hGamma (j : ℕ) :
      (∫ s : ℝ, f j s ∂μ) =
        Real.Gamma (r + 1) * (((m : ℝ) + j) ^ (-r) - ((m : ℝ) - 1) * ((m : ℝ) + j) ^ (-(r + 1))) := by
    unfold f
    have h := gamma_exp_integral (by positivity : 0 < r + 1) (hj j)
    rw [show r + 1 - 1 = r by ring] at h
    rw [integral_const_mul,h]
    rw [show -(r + 1) = -r - 1 by ring,Real.rpow_sub_one (hj j).ne']
    field_simp [(hj j).ne']
    ring
  have hI (j : ℕ) : Integrable (f j) μ := by
    have h := (GammaDeficit.integrable_gamma_exp (by positivity : 0 < r + 1) (hj j)).const_mul ((j : ℝ) + 1)
    simpa only [f,show r + 1 - 1 = r by ring] using h
  have hNorm (j : ℕ) : (∫ s : ℝ, ‖f j s‖ ∂μ) = ∫ s : ℝ, f j s ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0 < s := hs
    exact Real.norm_of_nonneg (by unfold f; positivity)
  have hA := powerTail_summable hr m
  have hB := (powerTail_summable (by linarith only [hr] : 1 < r + 1) m).mul_left ((m : ℝ) - 1)
  have hS : Summable (fun j => ∫ s : ℝ, ‖f j s‖ ∂μ) := by
    simp_rw [hNorm,hGamma]
    exact (hA.sub hB).mul_left (Real.Gamma (r + 1))
  have h := integral_tsum_of_summable_integral_norm hI hS
  simp_rw [hGamma] at h
  rw [tsum_mul_left,hA.tsum_sub hB,tsum_mul_left] at h
  refine (integral_congr_ae ?_).trans h.symm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs₀ : 0 < s := hs
  let X := Real.exp (-s)
  have hX : 0 < X := Real.exp_pos _
  have hX₁ : X < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hs₀)
  have hB := (gammaBinomial_hasSum (p := 2) (by norm_num) hX.le hX₁).mul_left (s ^ r * Real.exp (-s * m))
  rw [Real.Gamma_two,one_mul,Real.rpow_neg (sub_nonneg.mpr hX₁.le),Real.rpow_two] at hB
  have hTerm (j : ℕ) : s ^ r * Real.exp (-s * m) *
      (Real.Gamma (2 + (j : ℝ)) * X ^ j / (j.factorial : ℝ)) = f j s := by
    have hF : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    rw [show (2 : ℝ) + j = ((j + 1 : ℕ) : ℝ) + 1 by push_cast; ring,Real.Gamma_nat_eq_factorial,
      Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    unfold X f
    rw [← Real.exp_nat_mul,show -((m : ℝ) + j) * s = -s * m + (j : ℝ) * -s by ring,Real.exp_add]
    field_simp [hF]
  simp_rw [hTerm] at hB
  exact (show _ = s ^ r * Real.exp (-s * m) * ((1 - X) ^ 2)⁻¹ by rw [div_eq_mul_inv]; ring).trans hB.tsum_eq.symm

theorem boseSquaredMoment_integrable {r : ℝ} (hr : 1 < r) {m : ℕ} (hm : 0 < m) :
    IntegrableOn (fun s : ℝ => s ^ r * (Real.exp (-s * m) / (1 - Real.exp (-s)) ^ 2)) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [boseSquaredMoment_integral hr hm]
  have hm₀ : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have h (j : ℕ) : ((m : ℝ) + j) ^ (-r) - ((m : ℝ) - 1) * ((m : ℝ) + j) ^ (-(r + 1)) =
      ((j : ℝ) + 1) * ((m : ℝ) + j) ^ (-(r + 1)) := by
    have hX : 0 < (m : ℝ) + j := by positivity
    rw [show -(r + 1) = -r - 1 by ring,Real.rpow_sub_one hX.ne']
    field_simp [hX.ne']
    ring
  have hA := powerTail_summable hr m
  have hB := (powerTail_summable (by linarith only [hr] : 1 < r + 1) m).mul_left ((m : ℝ) - 1)
  have hEq : (∑' j : ℕ, ((j : ℝ) + 1) * ((m : ℝ) + j) ^ (-(r + 1))) =
      powerTail r m - ((m : ℝ) - 1) * powerTail (r + 1) m := by
    simp_rw [← h]
    rw [hA.tsum_sub hB,tsum_mul_left]
    rfl
  rw [← hEq]
  have hS : Summable (fun j : ℕ => ((j : ℝ) + 1) * ((m : ℝ) + j) ^ (-(r + 1))) := by
    simp_rw [← h]
    exact hA.sub hB
  have hT : 0 < ∑' j : ℕ, ((j : ℝ) + 1) * ((m : ℝ) + j) ^ (-(r + 1)) :=
    hS.tsum_pos (fun j => by positivity) 0 (by positivity)
  exact (mul_pos (Real.Gamma_pos_of_pos (by linarith only [hr])) hT).ne'

end ACS12.GammaMeasure

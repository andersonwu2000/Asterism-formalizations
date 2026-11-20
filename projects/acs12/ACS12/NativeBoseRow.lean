import ACS12.NativeCellAnalytic

/-! The complete analytic row agrees with the original Bose row after one literal self subtraction. -/
namespace ACS12.NativeCells

open MeasureTheory Set Filter
open GammaMeasure (gammaDensity)

noncomputable def boseRow (p N : ℝ) : ℝ :=
  ∫ s : ℝ in Ioi 0,
    2 * gammaDensity p s * (2 * Real.sinh (Real.pi * s) / (Real.exp (2 * Real.pi * s / N) - 1))

theorem boseRow_frequency_eq {N s : ℝ} (hN : 0 < N) (hs : 0 < s) :
    2 * Real.sinh (Real.pi * s) / (Real.exp (2 * Real.pi * s / N) - 1) =
      rowAtFrequency N⁻¹ s + Real.exp (-(Real.pi * s)) := by
  let a := Real.pi * s
  let b := a / N
  have ha : 0 < a := mul_pos Real.pi_pos hs
  have hb : 0 < b := div_pos ha hN
  have hA : s * (Real.pi - Real.pi * N⁻¹) = a - b := by dsimp only [a,b,div_eq_mul_inv]; ring
  have hB : s * (Real.pi * N⁻¹) = b := by dsimp only [a,b,div_eq_mul_inv]; ring
  have hC : 2 * Real.pi * s / N = b + b := by dsimp only [b,a]; ring
  unfold rowAtFrequency
  rw [hA,hB,hC,Real.exp_add]
  change 2 * Real.sinh a / (Real.exp b * Real.exp b - 1) =
    Real.sinh (a - b) / Real.sinh b + Real.exp (-a)
  rw [Real.sinh_eq, Real.sinh_eq,Real.sinh_eq, Real.exp_sub,
    show -(a - b) = b - a by ring,Real.exp_sub]
  simp only [Real.exp_neg]
  have hExp : Real.exp b ≠ 0 := Real.exp_ne_zero _
  have hEa : Real.exp a ≠ 0 := Real.exp_ne_zero _
  have hDen : Real.exp b * Real.exp b - 1 ≠ 0 := by
    rw [← Real.exp_add]
    exact sub_ne_zero.mpr (ne_of_gt (Real.one_lt_exp_iff.mpr (add_pos hb hb)))
  have hDen' : Real.exp b - (Real.exp b)⁻¹ ≠ 0 := by
    have h := Real.sinh_pos_iff.mpr hb
    rw [Real.sinh_eq,Real.exp_neg] at h
    exact ne_of_gt (by linarith only [h])
  have hDen₂ : Real.exp b ^ 2 - 1 ≠ 0 := by simpa only [pow_two] using hDen
  have hFact : Real.exp b - (Real.exp b)⁻¹ = (Real.exp b ^ 2 - 1) / Real.exp b := by
    field_simp [hExp]
  rw [← pow_two,hFact]
  field_simp [hExp,hEa,hDen₂]
  ring

private theorem selfRow_integrable {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun s => 2 * gammaDensity p s * Real.exp (-(Real.pi * s))) (Ioi 0) := by
  have h := gammaCosh_integrable hp (y := 0) (by simpa only [abs_zero] using Real.pi_pos)
  simp only [mul_zero,Real.cosh_zero,mul_one] at h
  have hM : AEStronglyMeasurable (fun s => 2 * gammaDensity p s * Real.exp (-(Real.pi * s)))
      (volume.restrict (Ioi 0)) := (((GammaMeasure.continuous_gammaDensity hp).const_mul 2).mul
    (by fun_prop : Continuous (fun s : ℝ => Real.exp (-(Real.pi * s))))).aestronglyMeasurable
  apply h.mono' hM
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs₀ : 0 < s := hs
  have hρ : 0 ≤ 2 * gammaDensity p s := mul_nonneg (by norm_num) (GammaMeasure.gammaDensity_pos hp s).le
  rw [Real.norm_of_nonneg (mul_nonneg hρ (Real.exp_pos _).le)]
  exact mul_le_of_le_one_right hρ (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg Real.pi_pos.le hs₀.le)))

theorem boseRow_sub_self {p N : ℝ} (hp : 0 < p) (hN : 1 < N) :
    boseRow p N - boseRow p 1 = analyticRow p N := by
  have hI := analyticRow_integrable hp hN
  have hSelf := selfRow_integrable hp
  have hOne : boseRow p 1 =
      ∫ s : ℝ in Ioi 0, 2 * gammaDensity p s * Real.exp (-(Real.pi * s)) := by
    unfold boseRow
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    dsimp only
    rw [boseRow_frequency_eq zero_lt_one hs]
    simp [rowAtFrequency]
  rw [hOne]
  have hE : boseRow p N = analyticRow p N + ∫ s : ℝ in Ioi 0, 2 * gammaDensity p s * Real.exp (-(Real.pi * s)) := by
    unfold boseRow analyticRow
    rw [← integral_add hI hSelf]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    dsimp only
    rw [boseRow_frequency_eq (zero_lt_one.trans hN) hs,mul_add]
  rw [hE,add_sub_cancel_right]

end ACS12.NativeCells

import ACS12.NativeLiteralRows

/-! The complete original Bose row after scaling its real Gamma integral. -/
namespace ACS12.NativeCells

open MeasureTheory Set Filter
open GammaMeasure
open CenteredCircle.AllN (expTail_den_pos)

private noncomputable def boseIntegrand (p N x : ℝ) : ℝ :=
  2 * gammaDensity p x * (2 * Real.sinh (Real.pi * x) / (Real.exp (2 * Real.pi * x / N) - 1))

private theorem boseIntegrand_integrable {p N : ℝ} (hp : 0 < p) (hN : 0 < N) :
    IntegrableOn (boseIntegrand p N) (Ioi 0) := by
  let R := max 2 N
  have hR : 1 < R := (by norm_num : (1 : ℝ) < 2).trans_le (le_max_left _ _)
  have hI := analyticRow_integrable hp hR
  let g (x : ℝ) := 2 * gammaDensity p x * Real.exp (-(Real.pi * x))
  have hG : IntegrableOn g (Ioi 0) := by
    have h := gammaCosh_integrable hp (y := 0) (by simpa only [abs_zero] using Real.pi_pos)
    simp only [mul_zero,Real.cosh_zero,mul_one] at h
    have hM : Continuous g := ((continuous_gammaDensity hp).const_mul 2).mul
      (by fun_prop : Continuous (fun x : ℝ => Real.exp (-(Real.pi * x))))
    apply h.mono' hM.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx₀ : 0 < x := hx
    have hρ := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (gammaDensity_pos hp x).le
    rw [Real.norm_of_nonneg (mul_nonneg hρ (Real.exp_pos _).le)]
    exact mul_le_of_le_one_right hρ (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg Real.pi_pos.le hx₀.le)))
  have hIR : IntegrableOn (boseIntegrand p R) (Ioi 0) := by
    apply (hI.add hG).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change 2 * gammaDensity p x * rowAtFrequency R⁻¹ x + g x = boseIntegrand p R x
    unfold boseIntegrand g
    rw [boseRow_frequency_eq (zero_lt_one.trans hR) hx,mul_add]
  have hM : Measurable (boseIntegrand p N) := by
    have h : Measurable (fun x : ℝ => 2 * gammaDensity p x) :=
      ((continuous_gammaDensity hp).const_mul 2).measurable
    exact h.mul (by fun_prop : Measurable (fun x : ℝ =>
      2 * Real.sinh (Real.pi * x) / (Real.exp (2 * Real.pi * x / N) - 1)))
  apply hIR.mono' hM.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx₀ : 0 < x := hx
  have hA : 0 < 2 * Real.pi * x := by positivity
  have hD : 0 < Real.exp (2 * Real.pi * x / R) - 1 := expTail_den_pos (div_pos hA (zero_lt_one.trans hR))
  have hD' : Real.exp (2 * Real.pi * x / R) - 1 ≤ Real.exp (2 * Real.pi * x / N) - 1 :=
    sub_le_sub_right (Real.exp_le_exp.mpr (div_le_div_of_nonneg_left hA.le hN (le_max_right _ _))) _
  have hS : 0 ≤ 2 * Real.sinh (Real.pi * x) := (mul_pos (by norm_num)
    (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hx₀))).le
  unfold boseIntegrand
  have hρ := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (gammaDensity_pos hp x).le
  rw [Real.norm_of_nonneg (mul_nonneg hρ (div_nonneg hS (hD.le.trans hD')))]
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hS hD hD') hρ

noncomputable def nativeGammaScale (p : ℝ) : ℝ := (2 : ℝ) ^ (p - 1) / Real.Gamma p

private theorem gammaDensity_sinh_ratio {p x : ℝ} (hp : 0 < p) (hx : 0 < x) :
    gammaDensity p x * Real.sinh (Real.pi * x) = nativeGammaScale p * x * gammaModulusRatio (p / 2) x := by
  have h := imageDensity_two (L := 2 * Real.pi) (by positivity) hx
  rw [imageDensity_eq_spectral 2 (by positivity : 0 < 2 * Real.pi)] at h
  have h₀ : Real.pi / (2 * Real.pi) = 1 / 2 := by field_simp [Real.pi_ne_zero]
  have h₁ : 2 * Real.pi * x / (2 * Real.pi) = x := by field_simp [Real.pi_ne_zero]
  have h₂ : 2 * Real.pi * x / 2 = Real.pi * x := by ring
  rw [h₀,h₁,h₂,show (2 : ℝ) - 1 = 1 by norm_num,Real.rpow_one] at h
  let A := ‖Complex.Gamma (gammaArgument (p / 2) x)‖ ^ 2
  let B := ‖Complex.Gamma (gammaArgument 1 x)‖ ^ 2
  let S := Real.sinh (Real.pi * x)
  let D := nativeGammaScale p
  have hB : B ≠ 0 := pow_ne_zero _ (norm_gamma_argument_ne zero_lt_one x)
  have hE : B * S = Real.pi * x := by
    unfold gammaDensity at h
    simp only [show (2 : ℝ) - 1 = 1 by norm_num,Real.rpow_one,
      show (2 : ℝ) / 2 = 1 by norm_num,Real.Gamma_two,mul_one] at h
    change (1 / 2) * (2 * B / Real.pi) * S = x at h
    field_simp [Real.pi_ne_zero] at h
    linarith only [h]
  change ((2 : ℝ) ^ (p - 1) * A / (Real.pi * Real.Gamma p)) * S = D * x * (A / B)
  have hD : (2 : ℝ) ^ (p - 1) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  have hG : Real.Gamma p ≠ 0 := (Real.Gamma_pos_of_pos hp).ne'
  unfold D nativeGammaScale
  field_simp [hB,Real.pi_ne_zero,hG]
  linear_combination A * hE

noncomputable def baseBose (x : ℝ) : ℝ := x / (Real.exp (2 * Real.pi * x) - 1)

private theorem baseBose_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ baseBose x :=
  div_nonneg hx.le (expTail_den_pos (by positivity : 0 < 2 * Real.pi * x)).le

theorem baseBose_calibration :
    IntegrableOn baseBose (Ioi 0) ∧ (∫ x : ℝ in Ioi 0, baseBose x) = 1 / 24 := by
  have hP : nativeGammaScale 2 = 2 := by norm_num [nativeGammaScale,Real.rpow_one]
  have hEq (x : ℝ) (hx : 0 < x) : boseIntegrand 2 1 x = 8 * baseBose x := by
    have h := gammaDensity_sinh_ratio (p := 2) zero_lt_two hx
    simp only [hP,show (2 : ℝ) / 2 = 1 by norm_num,gammaModulusRatio,
      div_self (pow_ne_zero _ (norm_gamma_argument_ne zero_lt_one x)),mul_one] at h
    unfold boseIntegrand baseBose
    rw [div_one]
    linear_combination (4 / (Real.exp (2 * Real.pi * x) - 1)) * h
  have hI : IntegrableOn (fun x => 8 * baseBose x) (Ioi 0) := by
    apply (boseIntegrand_integrable zero_lt_two zero_lt_one).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hEq x hx
  have hI' : IntegrableOn baseBose (Ioi 0) := by
    have h := hI.const_mul (1 / 8 : ℝ)
    exact h.congr (Eventually.of_forall fun x => by ring)
  have hL := boseRow_two_eq (N := 1) zero_lt_one
  change (∫ x : ℝ in Ioi 0, boseIntegrand 2 1 x) = _ at hL
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => hEq x hx),integral_const_mul] at hL
  exact ⟨hI',by linarith only [hL]⟩

theorem boseRow_scaled_ratio {p N : ℝ} (hp : 0 < p) (hN : 0 < N) :
    IntegrableOn (fun x => baseBose x * gammaModulusRatio (p / 2) (N * x)) (Ioi 0) ∧
    boseRow p N / N ^ 2 = 4 * nativeGammaScale p *
      ∫ x : ℝ in Ioi 0, baseBose x * gammaModulusRatio (p / 2) (N * x) := by
  let f := boseIntegrand p N
  let g (x : ℝ) := baseBose x * gammaModulusRatio (p / 2) (N * x)
  let C := 4 * nativeGammaScale p * N
  have hC : 0 < C := by unfold C nativeGammaScale; positivity
  have hPoint (x : ℝ) (hx : 0 < x) : f (N * x) = C * g x := by
    unfold f boseIntegrand g baseBose C
    have h := gammaDensity_sinh_ratio hp (mul_pos hN hx)
    rw [show 2 * Real.pi * (N * x) / N = 2 * Real.pi * x by field_simp [hN.ne']]
    linear_combination (4 / (Real.exp (2 * Real.pi * x) - 1)) * h
  have hI : IntegrableOn (fun x => f (N * x)) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff f 0 hN).mpr
    simpa only [mul_zero] using boseIntegrand_integrable hp hN
  have hI' : IntegrableOn g (Ioi 0) := by
    apply (hI.const_mul C⁻¹).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [hPoint x hx,← mul_assoc,inv_mul_cancel₀ hC.ne',one_mul]
  refine ⟨hI',?_⟩
  have h := integral_comp_mul_left_Ioi f 0 hN
  rw [mul_zero,smul_eq_mul,setIntegral_congr_fun measurableSet_Ioi (fun x hx => hPoint x hx),
    integral_const_mul] at h
  change (∫ x : ℝ in Ioi 0, f x) / N ^ 2 = 4 * nativeGammaScale p * ∫ x : ℝ in Ioi 0, g x
  unfold C at h
  field_simp [hN.ne'] at h ⊢
  linarith only [h]

end ACS12.NativeCells

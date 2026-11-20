import CenteredCircle.KernelCalculus
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! The signed sine bracket has positive integral against every Gaussian. -/

namespace ACS12.GaussianSine

open MeasureTheory Set Filter
open scoped Topology

private noncomputable def gaussian (A t : ℝ) : ℝ := Real.exp (-A * t ^ 2)

private noncomputable def sineIntegral (A U : ℝ) : ℝ :=
  ∫ t : ℝ in Ioi 0, gaussian A t * Real.sin (U * t)

private noncomputable def cosMoment (A U : ℝ) : ℝ :=
  ∫ t : ℝ in Ioi 0, t * gaussian A t * Real.cos (U * t)

private theorem sine_integrable {A : ℝ} (hA : 0 < A) (U : ℝ) :
    IntegrableOn (fun t : ℝ => gaussian A t * Real.sin (U * t)) (Ioi 0) := by
  refine (integrable_exp_neg_mul_sq hA).integrableOn.mono' ?_ ?_
  · unfold gaussian
    exact (by fun_prop : Continuous (fun t : ℝ => Real.exp (-A * t ^ 2) *
      Real.sin (U * t))).aestronglyMeasurable
  · exact Eventually.of_forall fun t => by
      rw [gaussian, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      simpa only [gaussian, mul_one] using mul_le_mul_of_nonneg_left
        (Real.abs_sin_le_one (U * t)) (Real.exp_pos (-A * t ^ 2)).le

private theorem cos_integrable {A : ℝ} (hA : 0 < A) (U : ℝ) :
    IntegrableOn (fun t : ℝ => t * gaussian A t * Real.cos (U * t)) (Ioi 0) := by
  refine (integrable_mul_exp_neg_mul_sq hA).integrableOn.mono' ?_ ?_
  · unfold gaussian
    exact (by fun_prop : Continuous (fun t : ℝ => t * Real.exp (-A * t ^ 2) *
      Real.cos (U * t))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    rw [gaussian, Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg ht.le (Real.exp_pos _).le)]
    simpa only [gaussian, mul_one] using mul_le_mul_of_nonneg_left
      (Real.abs_cos_le_one (U * t)) (mul_nonneg ht.le (Real.exp_pos (-A * t ^ 2)).le)

private theorem hasDerivAt_sineIntegral {A : ℝ} (hA : 0 < A) (U : ℝ) :
    HasDerivAt (sineIntegral A) (cosMoment A U) U := by
  have hbound : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), ∀ V ∈ (univ : Set ℝ),
      ‖t * gaussian A t * Real.cos (V * t)‖ ≤ t * gaussian A t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    intro V _
    rw [gaussian, Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg ht.le (Real.exp_pos _).le)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (V * t))
      (mul_nonneg ht.le (Real.exp_pos (-A * t ^ 2)).le)
  have hderiv : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), ∀ V ∈ (univ : Set ℝ),
      HasDerivAt (fun V => gaussian A t * Real.sin (V * t))
        (t * gaussian A t * Real.cos (V * t)) V := by
    apply Eventually.of_forall
    intro t V _
    convert (((hasDerivAt_id V).mul_const t).sin).const_mul (gaussian A t) using 1
    dsimp
    ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ))) (s := univ) (Filter.univ_mem : univ ∈ 𝓝 U)
    (Eventually.of_forall fun V => (sine_integrable hA V).aestronglyMeasurable)
    (sine_integrable hA U) (cos_integrable hA U).aestronglyMeasurable
    hbound (integrable_mul_exp_neg_mul_sq hA).integrableOn hderiv
  exact h.2

private theorem gaussian_cos_limit {A : ℝ} (hA : 0 < A) (U : ℝ) :
    Tendsto (fun t : ℝ => gaussian A t * Real.cos (U * t)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlim : Tendsto (fun t : ℝ => Real.exp (-A * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hA))
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  rw [gaussian, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ gaussian A t * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (U * t)) (Real.exp_pos _).le
    _ ≤ _ := by
      rw [mul_one, gaussian]
      apply Real.exp_le_exp.mpr
      have h := mul_nonneg hA.le (mul_nonneg (show 0 ≤ t by linarith) (sub_nonneg.mpr ht))
      nlinarith

private theorem gaussian_sine_relation {A : ℝ} (hA : 0 < A) (U : ℝ) :
    2 * A * cosMoment A U + U * sineIntegral A U = 1 := by
  have hder (t : ℝ) : HasDerivAt (fun t : ℝ => gaussian A t * Real.cos (U * t))
      (-(2 * A) * (t * gaussian A t * Real.cos (U * t)) -
        U * (gaussian A t * Real.sin (U * t))) t := by
    have hg := (((hasDerivAt_id t).pow 2).const_mul (-A)).exp
    have hc := ((hasDerivAt_id t).const_mul U).cos
    convert hg.mul hc using 1
    dsimp [gaussian]
    ring
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := 0) (fun t _ => hder t)
    (((cos_integrable hA U).const_mul (-(2 * A))).sub ((sine_integrable hA U).const_mul U))
    (gaussian_cos_limit hA U)
  rw [integral_sub ((cos_integrable hA U).const_mul (-(2 * A)))
    ((sine_integrable hA U).const_mul U), integral_const_mul, integral_const_mul] at h
  simp only [gaussian, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, Real.exp_zero, Real.cos_zero,
    mul_one, zero_sub] at h
  unfold cosMoment sineIntegral gaussian
  linarith

private theorem sineIntegral_eq_unit {A U : ℝ} (hA : 0 < A) :
    sineIntegral A U = U / (2 * A) *
      ∫ y : ℝ in (0 : ℝ)..1, Real.exp (-(U ^ 2 / (4 * A)) * (1 - y ^ 2)) := by
  let E := U ^ 2 / (4 * A)
  let w (v : ℝ) := Real.exp (v ^ 2 / (4 * A))
  have hder (v : ℝ) : HasDerivAt (fun v => w v * sineIntegral A v) ((2 * A)⁻¹ * w v) v := by
    have hw := ((((hasDerivAt_id v).pow 2).div_const (4 * A)).exp)
    convert hw.mul (hasDerivAt_sineIntegral hA v) using 1
    have hM : cosMoment A v = (1 - v * sineIntegral A v) / (2 * A) :=
      (eq_div_iff (by positivity : (2 * A) ≠ 0)).mpr
        (by linarith [gaussian_sine_relation hA v])
    dsimp [w]
    rw [hM]
    field_simp [hA.ne'] <;> ring
  have hi : IntervalIntegrable (fun v => (2 * A)⁻¹ * w v) volume 0 U := by
    apply Continuous.intervalIntegrable
    unfold w
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hder v) hi
  have hzero : sineIntegral A 0 = 0 := by simp [sineIntegral]
  rw [intervalIntegral.integral_const_mul, hzero, mul_zero, sub_zero] at h
  have hscale := intervalIntegral.smul_integral_comp_mul_right (a := 0) (b := 1) w U
  simp only [smul_eq_mul, zero_mul, one_mul] at hscale
  have hprod : Real.exp (-E) * w U = 1 := by
    dsimp [w, E]
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc
    _ = Real.exp (-E) * (w U * sineIntegral A U) := by rw [← mul_assoc, hprod, one_mul]
    _ = Real.exp (-E) * ((2 * A)⁻¹ * (U * ∫ y : ℝ in (0 : ℝ)..1, w (y * U))) := by
      rw [← h, ← hscale]
    _ = (U / (2 * A)) * (Real.exp (-E) * ∫ y : ℝ in (0 : ℝ)..1, w (y * U)) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      apply intervalIntegral.integral_congr
      intro y _
      dsimp only [w]
      rw [← Real.exp_add]
      congr 1
      dsimp [E]
      ring

private theorem interval_weight_identity (E : ℝ) :
    (∫ y : ℝ in (0 : ℝ)..1, (1 + 2 * E * y ^ 2) * Real.exp (-E * (1 - y ^ 2))) = 1 := by
  have hder (y : ℝ) : HasDerivAt (fun y => y * Real.exp (-E * (1 - y ^ 2)))
      ((1 + 2 * E * y ^ 2) * Real.exp (-E * (1 - y ^ 2))) y := by
    have h := ((((hasDerivAt_const y (1 : ℝ)).sub
      ((hasDerivAt_id y).pow 2)).const_mul (-E)).exp)
    convert (hasDerivAt_id y).mul h using 1
    dsimp
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hder y)
    (by apply Continuous.intervalIntegrable; fun_prop : IntervalIntegrable
      (fun y : ℝ => (1 + 2 * E * y ^ 2) * Real.exp (-E * (1 - y ^ 2))) volume 0 1)
  simpa using h

/-- The Gaussian sine bracket is positive even though the bracket itself
can have both signs on the positive axis. -/
theorem integral_sine_bracket_pos {A U : ℝ} (hA : 0 < A) (hU : 0 < U) :
    0 < ∫ t : ℝ in Ioi 0, Real.exp (-A * t ^ 2) *
      (Real.sin (U * t) - U * t * Real.cos (U * t)) := by
  let E := U ^ 2 / (4 * A)
  let ψ (y : ℝ) := Real.exp (-E * (1 - y ^ 2))
  let L := ∫ y : ℝ in (0 : ℝ)..1, ψ y
  let P := ∫ y : ℝ in (0 : ℝ)..1, (1 - y ^ 2) * ψ y
  have hE : 0 < E := by dsimp [E]; positivity
  have hP : 0 < P := by
    apply intervalIntegral.integral_pos (by norm_num)
    · apply Continuous.continuousOn
      unfold ψ
      fun_prop
    · intro y hy
      change 0 < y ∧ y ≤ 1 at hy
      apply mul_nonneg _ (Real.exp_pos _).le
      nlinarith [mul_nonneg (sub_nonneg.mpr hy.2) (show 0 ≤ 1 + y by linarith [hy.1])]
    · exact ⟨0, by simp, by simpa [ψ] using Real.exp_pos (-E)⟩
  have hdiff : (1 + 2 * E) * L - 1 = 2 * E * P := by
    have h₁ : IntervalIntegrable (fun y : ℝ => (1 + 2 * E) * ψ y) volume 0 1 := by
      apply Continuous.intervalIntegrable
      unfold ψ
      fun_prop
    have h₂ : IntervalIntegrable (fun y : ℝ => (1 + 2 * E * y ^ 2) * ψ y) volume 0 1 := by
      apply Continuous.intervalIntegrable
      unfold ψ
      fun_prop
    have hweight : (∫ y : ℝ in (0 : ℝ)..1, (1 + 2 * E * y ^ 2) * ψ y) = 1 :=
      interval_weight_identity E
    calc
      _ = (∫ y : ℝ in (0 : ℝ)..1, (1 + 2 * E) * ψ y) -
          ∫ y : ℝ in (0 : ℝ)..1, (1 + 2 * E * y ^ 2) * ψ y := by
        rw [hweight, intervalIntegral.integral_const_mul (1 + 2 * E) ψ]
      _ = ∫ y : ℝ in (0 : ℝ)..1, ((1 + 2 * E) * ψ y - (1 + 2 * E * y ^ 2) * ψ y) :=
        (intervalIntegral.integral_sub h₁ h₂).symm
      _ = _ := by
        change _ = 2 * E * ∫ y : ℝ in (0 : ℝ)..1, (1 - y ^ 2) * ψ y
        rw [← intervalIntegral.integral_const_mul (2 * E) (fun y => (1 - y ^ 2) * ψ y)]
        apply intervalIntegral.integral_congr
        intro y _
        ring
  have hI : sineIntegral A U = U / (2 * A) * L := sineIntegral_eq_unit hA
  have hM : cosMoment A U = (1 - U * sineIntegral A U) / (2 * A) :=
    (eq_div_iff (by positivity : (2 * A) ≠ 0)).mpr
      (by linarith [gaussian_sine_relation hA U])
  have heq : (∫ t : ℝ in Ioi 0, Real.exp (-A * t ^ 2) *
      (Real.sin (U * t) - U * t * Real.cos (U * t))) =
        sineIntegral A U - U * cosMoment A U := by
    change _ = (∫ t : ℝ in Ioi 0, gaussian A t * Real.sin (U * t)) -
      U * ∫ t : ℝ in Ioi 0, t * gaussian A t * Real.cos (U * t)
    rw [← integral_const_mul U (fun t : ℝ => t * gaussian A t * Real.cos (U * t)),
      ← integral_sub (sine_integrable hA U) ((cos_integrable hA U).const_mul U)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    unfold gaussian
    ring
  rw [heq]
  calc
    0 < (U / (2 * A)) * (2 * E * P) := by positivity
    _ = (U / (2 * A)) * ((1 + 2 * E) * L - 1) := by rw [hdiff]
    _ = _ := by
      rw [hM, hI]
      dsimp [E]
      field_simp [hA.ne'] <;> ring

end ACS12.GaussianSine

import ACS12.PowerSine
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! The logarithmic form of the damped cosine difference. -/

namespace ACS12.GammaMeasure

open MeasureTheory Set Filter
open scoped Topology

noncomputable def cosineDifference (r y x t : ℝ) : ℝ :=
  Real.exp (-r * t) * (Real.cos (y * t) - Real.cos (x * t)) / t

private theorem norm_cosineDifference_le (r y x : ℝ) {t : ℝ} (ht : 0 < t) :
    ‖cosineDifference r y x t‖ ≤ |y - x| * Real.exp (-r * t) := by
  rw [cosineDifference, norm_div, norm_mul, Real.norm_of_nonneg ht.le,
    Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs (Real.cos _ - Real.cos _)]
  apply (div_le_iff₀ ht).mpr
  have h := Real.abs_cos_sub_cos_le (y * t) (x * t)
  rw [← sub_mul, abs_mul, abs_of_pos ht] at h
  exact (mul_le_mul_of_nonneg_left h (Real.exp_pos _).le).trans_eq (by ring)

theorem cosineDifference_integrable {r : ℝ} (hr : 0 < r) (y x : ℝ) :
    IntegrableOn (cosineDifference r y x) (Ioi 0) := by
  apply ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hr) 0).const_mul |y - x|).mono'
  · unfold cosineDifference
    exact (by fun_prop : Measurable _).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_cosineDifference_le r y x ht

private theorem hasDerivAt_integral_cosineDifference {r : ℝ} (hr : 0 < r) (y x : ℝ) :
    HasDerivAt (fun x => ∫ t : ℝ in Ioi 0, cosineDifference r y x t)
      (x / (r ^ 2 + x ^ 2)) x := by
  have hDer : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), ∀ z ∈ (univ : Set ℝ),
      HasDerivAt (fun w => cosineDifference r y w t)
        (Real.exp (-r * t) * Real.sin (z * t)) z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro z _
    have ht₀ : 0 < t := ht
    have h := ((((hasDerivAt_id z).mul_const t).cos.const_sub (Real.cos (y * t))).const_mul
      (Real.exp (-r * t))).div_const t
    convert h using 1
    dsimp only [id_eq, one_mul]
    field_simp [ht₀.ne']
  have hBound : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), ∀ z ∈ (univ : Set ℝ),
      ‖Real.exp (-r * t) * Real.sin (z * t)‖ ≤ Real.exp (-r * t) := by
    exact Eventually.of_forall fun t z _ => by
      rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_sin_le_one _)
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ))) (s := univ) (Filter.univ_mem : univ ∈ 𝓝 x)
    (Eventually.of_forall fun z => (cosineDifference_integrable hr y z).aestronglyMeasurable)
    (cosineDifference_integrable hr y x)
    (by fun_prop : Measurable (fun t : ℝ => Real.exp (-r * t) * Real.sin (x * t))).aestronglyMeasurable
    hBound (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hr) 0) hDer).2
  rw [GammaDeficit.exp_sine_integral hr x] at h
  exact h

theorem integral_cosineDifference {r : ℝ} (hr : 0 < r) (y x : ℝ) :
    (∫ t : ℝ in Ioi 0, Real.exp (-r * t) * (Real.cos (y * t) - Real.cos (x * t)) / t) =
      (Real.log (r ^ 2 + x ^ 2) - Real.log (r ^ 2 + y ^ 2)) / 2 := by
  let f (x : ℝ) := ∫ t : ℝ in Ioi 0, cosineDifference r y x t
  let g (x : ℝ) := (Real.log (r ^ 2 + x ^ 2) - Real.log (r ^ 2 + y ^ 2)) / 2
  have hD (x : ℝ) : HasDerivAt g (x / (r ^ 2 + x ^ 2)) x := by
    have hN : r ^ 2 + x ^ 2 ≠ 0 := by positivity
    have h := (((((hasDerivAt_id x).pow 2).const_add (r ^ 2)).log hN).sub_const
      (Real.log (r ^ 2 + y ^ 2))).div_const 2
    convert h using 1
    simp only [Pi.pow_apply, id_eq, show (2 - 1 : ℕ) = 1 by decide, pow_one, Nat.cast_ofNat]
    ring
  have hEq : EqOn f g univ :=
    isOpen_univ.eqOn_of_deriv_eq isPreconnected_univ
      (fun z _ => (hasDerivAt_integral_cosineDifference hr y z).differentiableAt.differentiableWithinAt)
      (fun z _ => (hD z).differentiableAt.differentiableWithinAt)
      (fun z _ => (hasDerivAt_integral_cosineDifference hr y z).deriv.trans (hD z).deriv.symm)
      (mem_univ y) (by simp [f, g, cosineDifference])
  exact hEq (mem_univ x)

end ACS12.GammaMeasure

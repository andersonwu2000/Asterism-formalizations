import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-! The real positive square substitution, with its complete Jacobian. -/
namespace ACS12
open MeasureTheory Set

theorem integral_positiveSquare (g : ℝ → ℝ) :
    (∫ s : ℝ in Ioi 0, g s) = ∫ t : ℝ in Ioi 0, 2*t*g (t^2) := by
  let f (t : ℝ) := t^2
  have hImg : f '' Ioi (0:ℝ) = Ioi 0 := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      change 0 < t at ht
      exact sq_pos_of_pos ht
    · intro hx
      exact ⟨Real.sqrt x,Real.sqrt_pos.mpr hx,Real.sq_sqrt hx.le⟩
  have hD (t : ℝ) : HasDerivAt f (2*t) t := by
    simpa only [Nat.cast_ofNat,show (2:ℕ)-1=1 by decide,pow_one] using hasDerivAt_pow 2 t
  have hInj : (Ioi (0:ℝ)).InjOn f := by
    intro x hx y hy h
    exact (sq_eq_sq₀ hx.le hy.le).mp h
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun t _ => (hD t).hasDerivWithinAt) hInj g
  rw [hImg] at h
  rw [h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht₀ : 0 < t := ht
  change |2*t| • g (t^2) = 2*t*g (t^2)
  rw [abs_of_pos (mul_pos zero_lt_two ht₀),smul_eq_mul]

theorem integrableOn_positiveSquare_iff (g : ℝ → ℝ) :
    IntegrableOn g (Ioi 0) ↔ IntegrableOn (fun t : ℝ => 2*t*g (t^2)) (Ioi 0) := by
  let f (t : ℝ) := t^2
  have hImg : f '' Ioi (0:ℝ) = Ioi 0 := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact sq_pos_of_pos (show 0 < t from ht)
    · intro hx
      exact ⟨Real.sqrt x,Real.sqrt_pos.mpr hx,Real.sq_sqrt hx.le⟩
  have hD (t : ℝ) : HasDerivAt f (2*t) t := by
    simpa only [Nat.cast_ofNat,show (2:ℕ)-1=1 by decide,pow_one] using hasDerivAt_pow 2 t
  have hInj : (Ioi (0:ℝ)).InjOn f := by
    intro x hx y hy h
    exact (sq_eq_sq₀ hx.le hy.le).mp h
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun t _ => (hD t).hasDerivWithinAt) hInj g
  rw [hImg] at h
  refine h.trans (integrableOn_congr_fun ?_ measurableSet_Ioi)
  intro t ht
  change |2*t| • g (t^2) = 2*t*g (t^2)
  rw [abs_of_pos (mul_pos zero_lt_two (show 0<t from ht)),smul_eq_mul]

end ACS12

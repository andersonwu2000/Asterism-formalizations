import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic.Linarith

/-! Actual angular coordinates for the physical circle, with all scale factors. -/

namespace CenteredCircle.AllN

set_option backward.isDefEq.respectTransparency false

noncomputable def unitRay (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

theorem unitRay_periodic (θ : ℝ) : unitRay (θ + 2 * Real.pi) = unitRay θ := by
  simpa only [unitRay, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat] using
    Complex.exp_mul_I_periodic (θ : ℂ)

theorem unitRay_add (θ η : ℝ) : unitRay (θ + η) = unitRay θ * unitRay η := by
  simp only [unitRay, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem unitRay_zero : unitRay 0 = 1 := by simp [unitRay]

theorem norm_unitRay (θ : ℝ) : ‖unitRay θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

noncomputable def positiveAngle (z : ℂ) : ℝ :=
  if Complex.arg z < 0 then Complex.arg z + 2 * Real.pi else Complex.arg z

theorem positiveAngle_range (z : ℂ) :
    0 ≤ positiveAngle z ∧ positiveAngle z < 2 * Real.pi := by
  unfold positiveAngle
  split_ifs with h
  · constructor <;> linarith [Complex.neg_pi_lt_arg z, Real.pi_pos]
  · constructor <;> linarith [Complex.arg_le_pi z, Real.pi_pos]

theorem positiveAngle_ray {z : ℂ} (hz : ‖z‖ = 1) : unitRay (positiveAngle z) = z := by
  have he : unitRay (Complex.arg z) = z := by
    simpa only [hz, Complex.ofReal_one, one_mul, unitRay] using Complex.norm_mul_exp_arg_mul_I z
  unfold positiveAngle
  split_ifs with h
  · rw [unitRay_periodic]
    exact he
  · exact he

end CenteredCircle.AllN

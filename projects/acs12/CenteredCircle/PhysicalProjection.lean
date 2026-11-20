import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Radial projection of an equal-radius chord. -/

namespace CenteredCircle.AllN

open scoped BigOperators

theorem equal_radius_chord_projection {u v : ℂ} {R : ℝ}
    (hu : ‖u‖ = R) (hv : ‖v‖ = R) :
    ((v - u) * star u).re = -‖v - u‖ ^ 2 / 2 := by
  have hu' := Complex.normSq_eq_norm_sq u
  have hv' := Complex.normSq_eq_norm_sq v
  rw [hu, Complex.normSq_apply] at hu'
  rw [hv, Complex.normSq_apply] at hv'
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.sub_re, Complex.sub_im]
  nlinarith

end CenteredCircle.AllN

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-! The complete signed high-source current kernel and both full hump-atom prices. -/
namespace ACS12.HighCurrent

noncomputable def currentHump (τ z : ℝ) : ℝ := if z ≤ τ then τ * z ^ 3 * (τ - z) else 0

theorem signed_current_kernel_identity (τ x z : ℝ) :
    (τ - z) * (x + z ^ 2) ^ 2 - τ * x ^ 2 =
      τ * z ^ 3 * (τ - z) - z * (x - z * (τ - z)) ^ 2 := by ring

theorem signed_current_kernel_upper {τ x z : ℝ} (hτ : 0 ≤ τ) (hz : 0 ≤ z) :
    (τ - z) * (x + z ^ 2) ^ 2 - τ * x ^ 2 ≤ currentHump τ z := by
  rw [signed_current_kernel_identity]
  unfold currentHump
  split_ifs with h
  · exact sub_le_self _ (mul_nonneg hz (sq_nonneg _))
  · have hSign : τ * z ^ 3 * (τ - z) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (sub_nonpos.mpr (lt_of_not_ge h).le)
    have hSquare := mul_nonneg hz (sq_nonneg (x - z * (τ - z)))
    linarith only [hSign,hSquare]

theorem currentHump_nonneg {τ z : ℝ} (hτ : 0 ≤ τ) (hz : 0 ≤ z) : 0 ≤ currentHump τ z := by
  unfold currentHump
  split_ifs with h
  · exact mul_nonneg (by positivity) (sub_nonneg.mpr h)
  · exact le_rfl

theorem currentHump_max {τ z : ℝ} (hτ : 0 ≤ τ) (hz : 0 ≤ z) :
    currentHump τ z ≤ 27 * τ ^ 5 / 256 := by
  have hEq : 27 * τ ^ 5 / 256 - τ * z ^ 3 * (τ - z) =
      τ * (z - 3 * τ / 4) ^ 2 * (z ^ 2 + τ * z / 2 + 3 * τ ^ 2 / 16) := by ring
  have hNon : 0 ≤ τ * (z - 3 * τ / 4) ^ 2 * (z ^ 2 + τ * z / 2 + 3 * τ ^ 2 / 16) := by positivity
  unfold currentHump
  split_ifs with h
  · linarith only [hEq,hNon]
  · positivity

theorem current_rational_tangent {x μ z : ℝ} (hx : 0 < x) (hμ : 0 ≤ μ) (hz : 0 ≤ z) :
    z / (x + z) ≤ μ / (x + μ) + x / (x + μ) ^ 2 * (z - μ) := by
  have hEq : μ / (x + μ) + x / (x + μ) ^ 2 * (z - μ) - z / (x + z) =
      x * (z - μ) ^ 2 / ((x + μ) ^ 2 * (x + z)) := by
    field_simp [show x + μ ≠ 0 by positivity,show x + z ≠ 0 by positivity]
    <;> ring
  have hNon : 0 ≤ x * (z - μ) ^ 2 / ((x + μ) ^ 2 * (x + z)) := by positivity
  linarith only [hEq,hNon]

end ACS12.HighCurrent

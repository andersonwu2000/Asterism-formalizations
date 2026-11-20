import CenteredCircle.RegularPolygon

/-! Translated, scaled and rotated regular polygons. -/

namespace CenteredCircle.AllN

open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def regularPosition (n : ℕ) (O : ℂ) (R θ : ℝ) (k : Fin n) : ℂ :=
  O + ((R : ℂ) * unitRay θ) * regularPoint n k

theorem regularPosition_phase (n : ℕ) (O : ℂ) (R θ : ℝ) (k : Fin n) :
    regularPosition n O R θ k = O + (R : ℂ) * unitRay (θ + 2 * Real.pi * (k : ℝ) / (n : ℝ)) := by
  rw [regularPosition, regularPoint_phase, mul_assoc, ← unitRay_add]

theorem regular_rotation_norm {R : ℝ} (hR : 0 < R) (θ : ℝ) :
    ‖(R : ℂ) * unitRay θ‖ = R := by
  rw [norm_mul, norm_unitRay, mul_one, Complex.norm_real, Real.norm_of_nonneg hR.le]

theorem regularPosition_injective {n : ℕ} (hn : n ≠ 0) (O : ℂ) {R : ℝ} (hR : 0 < R) (θ : ℝ) :
    Function.Injective (regularPosition n O R θ) := by
  have hγ : (R : ℂ) * unitRay θ ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [regular_rotation_norm hR]
    exact ne_of_gt hR
  intro i j hij
  exact (regularPoint_injective hn) (mul_left_cancel₀ hγ (add_left_cancel hij))

theorem regularPosition_on_circle (n : ℕ) (O : ℂ) {R : ℝ} (hR : 0 < R) (θ : ℝ) (i : Fin n) :
    ‖regularPosition n O R θ i - O‖ = R := by
  rw [regularPosition, add_sub_cancel_left, norm_mul, regular_rotation_norm hR,
    regularPoint_norm, mul_one]

theorem regularPosition_centered {n : ℕ} (hn : 2 ≤ n) (O : ℂ) (m R θ : ℝ) :
    (∑ i : Fin n, m • (regularPosition n O R θ i - O)) = 0 := by
  simp only [regularPosition, add_sub_cancel_left]
  rw [← Finset.smul_sum, ← Finset.mul_sum, regularPoint_sum hn, mul_zero, smul_zero]

end CenteredCircle.AllN

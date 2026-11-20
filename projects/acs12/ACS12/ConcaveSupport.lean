import Mathlib.Analysis.Convex.Deriv

/-! Tangent support at any point of a concave interval. -/

namespace ACS12

theorem concave_tangent_upper {s : Set ℝ} {f : ℝ → ℝ} {x y d : ℝ}
    (h : ConcaveOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s) (hd : HasDerivAt f d y) :
    f x ≤ f y + d * (x - y) := by
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have hS := h.le_slope_of_hasDerivAt hx hy hxy hd
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hxy)] at hS
    linarith only [hS]
  · simp
  · have hS := h.slope_le_of_hasDerivAt hy hx hyx hd
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hyx)] at hS
    linarith only [hS]

theorem strictConcave_tangent_upper {s : Set ℝ} {f : ℝ → ℝ} {x y d : ℝ}
    (h : StrictConcaveOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s)
    (hxy : x ≠ y) (hd : HasDerivAt f d y) :
    f x < f y + d * (x - y) := by
  rcases lt_or_gt_of_ne hxy with hxy | hyx
  · have hS := h.lt_slope_of_hasDerivAt hx hy hxy hd
    rw [slope_def_field, lt_div_iff₀ (sub_pos.mpr hxy)] at hS
    linarith only [hS]
  · have hS := h.slope_lt_of_hasDerivAt hy hx hyx hd
    rw [slope_def_field, div_lt_iff₀ (sub_pos.mpr hyx)] at hS
    linarith only [hS]

end ACS12

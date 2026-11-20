import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity

namespace ACS12.GammaMeasure

noncomputable def adjacentCap (p u : ℝ) : ℝ :=
  u * (5 / 7 + (2304 / 8575) * u ^ 2 + (3 / 20) * (9 / 5 - p))

theorem adjacentCap_pos {p u : ℝ} (hP : p ≤ 9 / 5) (hu : 0 < u) :
    0 < adjacentCap p u := by
  unfold adjacentCap
  exact mul_pos hu (by
    have h := sub_nonneg.mpr hP
    positivity)

end ACS12.GammaMeasure

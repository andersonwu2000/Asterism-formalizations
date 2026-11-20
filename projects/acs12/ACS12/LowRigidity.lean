import ACS12.GammaDefectComparison
import ACS12.GammaPacking

/-! The low positive range of the forward ACS12 implication. -/

namespace ACS12

open GammaMeasure GammaDeficit

theorem Configuration.rigidity_low {n : ℕ} {p : ℝ} (F : Configuration n p)
    (hn : 2 ≤ n) (hp : 0 < p) (hp₁ : p ≤ 1) : IsEqualMassRegular F := by
  obtain ⟨C⟩ := F.exists_normalized_chart hn
  let L := C.source.period
  let b := C.source.mass C.source.neighbor
  have hL : 0 < L := C.source.period_pos
  have hb : 0 < b := C.source.mass_pos _
  have hb₁ : b ≤ 1 := C.source.mass_neighbor_le_one
  have hp₂ : p ≤ 2 := hp₁.trans (by norm_num)
  apply F.regular_of_anchor_mass_one hn hp hp₂ C
  by_contra hne
  have hQ := F.anchored_massPolynomial_pos hp hp₂ C (imageSlope_le_corrected hp hp₁ hL)
  have hMass := LowScalar.two_thirds_lt_of_massPolynomial_pos hp₁ hb hQ
  have hCircle := F.circleDefect_nonneg hp hp₂ C
  have hCmp := circleDefect_le_line hp hp₁ hL hMass.le hb₁
  have hLine : 0 ≤ LowScalar.lineValue p b := by
    by_contra! hneg
    exact (not_lt_of_ge (hCircle.trans hCmp)) (div_neg_of_neg_of_pos hneg (Real.Gamma_pos_of_pos hp))
  exact hne (LowScalar.line_bounds_force_one hp hp₁ hb hb₁ hQ hLine)

end ACS12

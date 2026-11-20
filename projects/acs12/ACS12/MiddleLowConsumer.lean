import ACS12.PureAdjacentCap
import ACS12.PureAdjacentValue
import ACS12.AdjacentReturn
import ACS12.MiddleComparison
import ACS12.PressureIncident

/-! The common outer and inner operators consume the complete lower-gap estimate. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN Set

private theorem adjacentLawValue_pure_root_neg {p L u m : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hL : 0 < L) (huL : 2 / 3 ≤ u) (hu' : u ≤ 7 / 8)
    (hm : 0 < m) (hRoot : adjacentDiagonal p L 0 u m = 0) :
    adjacentLawValue p L 0 u m < 0 := by
  have hp₂ := hP.trans (by norm_num : (9 / 5 : ℝ) ≤ 2)
  have hu : 0 < u := (by norm_num : (0 : ℝ) < 2 / 3).trans_le huL
  have hθ : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have hCap := adjacentCap_pos hP hu
  have hNeg := pureAdjacentCap_neg hp hP hL hu hu'
  have hM : m ≤ adjacentCap p u := by
    by_contra! h
    have hA := adjacentDiagonal_strictAnti hp hp₂ hL hθ hu hCap hm h
    exact (hA.trans hNeg).ne hRoot
  have hK := lawRightClip_quadratureData (u := u) hp hp₂ hL hθ hu
  have h := hK.head_mono u le_rfl hm hCap hM
  exact (add_le_add le_rfl h).trans_lt
    (pure_adjacent_middle_value_neg hp hP hL huL hu')

theorem adjacentLawValue_actual_root_neg {p L u m : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hL : 0 < L) (huL : 2 / 3 ≤ u) (hu' : u ≤ 7 / 8)
    (hm : 0 < m) (hRoot : adjacentDiagonal p L 1 u m = 0)
    (hG : 0 < lawRightTest p L 1 u u) :
    adjacentLawValue p L 1 u m < 0 := by
  have hu₁ := hu'.trans_lt (by norm_num : (7 / 8 : ℝ) < 1)
  have hu : 0 < u := (by norm_num : (0 : ℝ) < 2 / 3).trans_le huL
  have h0 : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨r, hr, hR, hGap, _⟩ := exists_adjacentDiagonal_root hp hP hL h0 hu hu₁
  exact (adjacentLawValue_lt_of_roots hp hP hL h0 h1 zero_lt_one hu hu₁ hr hm hGap.le hR hRoot hG).trans
    (adjacentLawValue_pure_root_neg hp hP hL huL hu' hr.1 hR)

theorem _root_.ACS12.Configuration.first_gap_gt_sevenEighths {n : ℕ} {p : ℝ} (F : Configuration n p)
    (hn : 2 ≤ n) (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi)) {j k : Fin n}
    (hj : C.source.IsNext C.source.neighbor j) (hk : C.source.IsNext j k)
    (hu₁ : C.source.forwardDistance C.source.neighbor j < 1) :
    7 / 8 < C.source.forwardDistance C.source.neighbor j := by
  let S := C.source
  let L := S.period
  let u := S.forwardDistance S.neighbor j
  have hL : 0 < L := S.period_pos
  have hu : 0 < u := S.forwardDistance_pos _ _
  have hp₂ := hP.trans_lt (by norm_num : (9 / 5 : ℝ) < 2)
  have hNeighbor := ACS12.Pressure.incident_neighbor_gt_two_thirds hp hp₂.le F C
  have hj' : S.neighbor ≠ j := fun he => (lt_irrefl _) (he ▸ hj.1)
  have huL : 2 / 3 < u := hNeighbor.trans_le (S.forwardDistance_caps C.circular_caps hj').1
  have h1 : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  by_contra! hU
  change u ≤ 7 / 8 at hU
  obtain ⟨m, hm, hRoot, _, hMax⟩ := exists_adjacentDiagonal_root hp hP hL h1 hu hu₁
  have hG : 0 < lawRightTest p L 1 u u := by
    rw [lawRightTest_one (zero_lt_one.trans_le hp) hL hu]
    exact F.rightTest_active hn (zero_lt_one.trans_le hp) hp₂.le C hj hk hu₁.le
  have hNeg := adjacentLawValue_actual_root_neg hp hP hL huL.le hU hm.1 hRoot hG
  have hAct := F.adjacent_mesh_necessary hn hp hp₂.le C hj hk hu₁.le hMax
  change 0 ≤ adjacentLawValue p L 1 u m at hAct
  exact hNeg.not_ge hAct

end ACS12.GammaMeasure

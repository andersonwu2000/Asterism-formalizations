import ACS12.GammaPacking
import ACS12.ChartPackedArc
import ACS12.ChartNext

/-! Original next-gap descent, before any scalar source comparison. -/

namespace ACS12

open CenteredCircle.AllN
open GammaMeasure

private theorem forwardDistance_neighbor_eq {ι : Type*} [DecidableEq ι]
    (S : AnchoredCircleSource ι) (j : ι) :
    S.forwardDistance S.neighbor j = S.rightDistance j := by
  by_cases hn : j = S.neighbor
  · simp [hn, AnchoredCircleSource.rightDistance, S.coordinate_neighbor]
  by_cases hr : j = S.root
  · have h : S.coordinate j < S.coordinate S.neighbor := by
      rw [hr, S.coordinate_root, S.coordinate_neighbor]
      norm_num
    rw [S.forwardDistance_eq_wrap h]
    simp [AnchoredCircleSource.rightDistance, hr, S.coordinate_root, S.coordinate_neighbor]
    ring
  · have h : S.coordinate S.neighbor < S.coordinate j := by
      rw [S.coordinate_neighbor]
      exact S.other_coordinate j hr hn
    rw [S.forwardDistance_eq_sub h]
    simp [AnchoredCircleSource.rightDistance, hr, hn, S.coordinate_neighbor]

theorem Configuration.next_gap_lt_one {n : ℕ} {p : ℝ} (F : Configuration n p)
    (hn : 2 ≤ n) (hp : 0 < p) (hp₂ : p ≤ 2) (hNonregular : ¬IsEqualMassRegular F)
    (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi)) {j : Fin n}
    (hj : C.source.IsNext C.source.neighbor j) :
    C.source.forwardDistance C.source.neighbor j < 1 := by
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  let S := C.source
  let L := S.period
  let u := S.forwardDistance S.neighbor j
  let m := S.mass j
  let b := S.mass S.neighbor
  let A := imageMoment p L .a 0
  let B := imageMoment p L .b 0
  have hL : 0 < L := S.period_pos
  have hm : 0 < m := S.mass_pos _
  have hu : 0 < u := S.forwardDistance_pos _ _
  have hne : S.neighbor ≠ j := fun h => (lt_irrefl _) (h ▸ hj.1)
  have hmu : m ≤ u := (S.forwardDistance_caps C.circular_caps hne).2
  change u < 1
  by_contra! hu₁
  have hK := imageMoment_quadratureData hp hp₂ hL (by norm_num : 0 < (1 : ℝ)) .b
  have hRight := S.forwardExterior_le_head C.circular_caps (by norm_num : 0 < (1 : ℝ))
    hK S.neighbor j (hj.forward_le S) hu₁ hm (le_refl m)
  have hMono : samplingHead B u m ≤ samplingHead B u u :=
    hK.head_mono u hu₁ hm hu hmu
  have hAnti : samplingTail B 0 u ≤ samplingTail B 0 1 :=
    hK.boundary_anti (by simp) hu₁ hu₁
  rw [samplingTail_eq_shift, zero_add] at hAnti
  have hExt : S.forwardExterior B S.neighbor = S.rightExterior B := by
    simp only [AnchoredCircleSource.forwardExterior, AnchoredCircleSource.rightExterior,
      forwardDistance_neighbor_eq]
  rw [hExt] at hRight
  have hLeft := S.leftExterior_quadrature (imageMoment_quadratureData hp hp₂ hL
    (by norm_num : 0 < (1 : ℝ)) .a) C.circular_caps
  have hLA : S.leftExterior A = S.leftExterior (imageA p L) := by
    unfold AnchoredCircleSource.leftExterior
    exact Finset.sum_congr rfl fun k _ => by
      rw [imageTail_moment_zero_a hp hL (S.leftDistance_pos k)]
  have hRB : S.rightExterior B = S.rightExterior (imageB p L) := by
    unfold AnchoredCircleSource.rightExterior
    exact Finset.sum_congr rfl fun k _ => by
      rw [imageTail_moment_zero_b hp hL (S.rightDistance_pos k)]
  have hTel := imageMoment_unit_tail_sum hp hp₂ hL
  obtain ⟨hRow, _⟩ := F.anchored_image_balances hp C
  change S.leftExterior (imageA p L) + S.rightExterior (imageB p L) =
    imageSlope p L 1 + (1 - b) * (imagePotential p L 1 + imageSelf p L) at hRow
  rw [← hLA, ← hRB] at hRow
  have hBound := add_le_add hLeft ((hRight.trans hMono).trans hAnti)
  rw [hTel, hRow] at hBound
  have hD := add_pos (imagePotential_pos hp hL (show 0 < (1 : ℝ) by norm_num))
    (imageSelf_pos hp hL)
  have hb : b = 1 := by
    by_contra hb
    have hlt : b < 1 := lt_of_le_of_ne S.mass_neighbor_le_one hb
    linarith [mul_pos (sub_pos.mpr hlt) hD]
  exact hNonregular (F.regular_of_anchor_mass_one hn hp hp₂ C hb)

end ACS12

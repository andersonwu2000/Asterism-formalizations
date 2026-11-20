import ACS12.OuterReturn
import ACS12.LawClip

/-! The pure affine outer source is bounded by the same-law adjacent mesh. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN Set

noncomputable def adjacentDiagonal (p L θ u m : ℝ) : ℝ :=
  adjacentSourceLaw p L θ u m m m

theorem adjacentDiagonal_strictAnti {p L θ u : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hu : 0 < u) :
    StrictAntiOn (adjacentDiagonal p L θ u) (Ioi 0) := by
  intro x hx y hy hxy
  have h := adjacentSourceLaw_advance_lt (m := x) hp hp₂ hL hθ hu hx hxy hx hy (by linarith)
  have hD := outerLawDenom_pos hp hp₂ hL hθ hu
  have hE : adjacentSourceLaw p L θ u y y y - adjacentSourceLaw p L θ u y x y =
      -(y - x) * outerLawDenom p L θ u := by
    unfold adjacentSourceLaw outerLawDenom
    ring
  have hN := mul_neg_of_neg_of_pos (neg_neg_of_pos (sub_pos.mpr hxy)) hD
  unfold adjacentDiagonal
  linarith only [h, hE, hN]

theorem adjacentDiagonal_at_outer_pos {p L θ u : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hu : 0 < u) (hu₁ : u < 1) :
    0 < adjacentDiagonal p L θ u (outerLawMass p L θ u) := by
  let m := outerLawMass p L θ u
  obtain ⟨hm, hmu⟩ := outerLawMass_mem hp hp₂ hL hθ hu hu₁
  have h := adjacentSourceLaw_advance_lt (m := m) hp hp₂ hL hθ hu hm hmu hm hu (by linarith)
  rw [outerSourceLaw_eq hp hp₂ hL hθ hu, sub_self, zero_mul] at h
  exact h

theorem outerLawMass_lt_of_adjacentDiagonal_nonpos {p L θ u m : ℝ}
    (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hu : 0 < u) (hu₁ : u < 1) (hm : 0 < m) (hQ : adjacentDiagonal p L θ u m ≤ 0) :
    outerLawMass p L θ u < m := by
  by_contra! h
  have hR := (outerLawMass_mem hp hp₂ hL hθ hu hu₁).1
  have hA := (adjacentDiagonal_strictAnti hp hp₂ hL hθ hu).antitoneOn hm hR h
  exact (not_lt_of_ge (hA.trans hQ)) (adjacentDiagonal_at_outer_pos hp hp₂ hL hθ hu hu₁)

theorem outerLawValue_le_adjacentMesh {p L θ u m : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hu : 0 < u) (hu₁ : u < 1)
    (hQ : adjacentDiagonal p L θ u m ≤ 0) (hm : 0 < m) :
    outerLawValue p L θ u ≤ middleLawBase p L θ u + samplingHead (lawRightClip p L θ u) u m := by
  let K := lawRightClip p L θ u
  let r := outerLawMass p L θ u
  have hQd := lawRightClip_quadratureData (u := u) hp hp₂ hL hθ hu
  have hrm := (outerLawMass_lt_of_adjacentDiagonal_nonpos hp hp₂ hL hθ hu hu₁ hm hQ).le
  obtain ⟨hr, hru⟩ := outerLawMass_mem hp hp₂ hL hθ hu hu₁
  have hK : 0 ≤ K u := hQd.nonneg u le_rfl
  have hG : lawRightTest p L θ u u ≤ K u := le_max_right _ _
  rw [outerLawValue_clipped hp hp₂ hL hθ hu]
  change middleLawBase p L θ u + r * lawRightTest p L θ u u + samplingTail K u u ≤ _
  rcases le_total m u with h | h
  · rw [samplingHead_split K u m (hQd.summable u m le_rfl hm)]
    have hTail := hQd.tail_anti u le_rfl hm hu h
    have hM := (mul_le_mul_of_nonneg_left hG hr.le).trans (mul_le_mul_of_nonneg_right hrm hK)
    linarith only [hTail, hM]
  · have hHead := hQd.head_mono u le_rfl hu hm h
    rw [samplingHead_split K u u (hQd.summable u u le_rfl hu)] at hHead
    have hM := (mul_le_mul_of_nonneg_left hG hr.le).trans (mul_le_mul_of_nonneg_right hru.le hK)
    linarith only [hHead, hM]

end ACS12.GammaMeasure

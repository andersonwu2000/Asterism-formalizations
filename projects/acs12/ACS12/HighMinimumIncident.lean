import ACS12.HighIncidentSides
import ACS12.HighPhysicalRectangle

/-! The same smaller original radial side bounds the minimum-label incident current. -/
namespace ACS12.HighCurrent

noncomputable def minimumIncidentPrice (p q : ℝ) : ℝ :=
  (q / 2) * (2 * q) ^ (-(1 / p))

end ACS12.HighCurrent

namespace ACS12.Configuration

open Finset HighCurrent
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {p : ℝ} (F : ACS12.Configuration n p)

theorem incidentSideRow_atom_le (incoming : Bool) (o j : Fin n)
    (hj : j ∈ univ.erase o) (hSide : F.currentIncidentSide incoming o j) :
    F.currentRowMark o j ≤ F.incidentSideRow incoming o := by
  have h := single_le_sum
    (f := fun k => if F.currentIncidentSide incoming o k then F.currentRowMark o k else 0)
    (fun k _ => by dsimp only; split_ifs; exact F.currentRowMark_nonneg o k; exact le_rfl) hj
  dsimp only at h
  rw [if_pos hSide] at h
  exact h

theorem incidentSide_current_zeta_upper (incoming : Bool) (o : Fin n) {B : ℝ}
    (hB : 0 ≤ B) (hHalf : F.incidentSideRow incoming o ≤ 1 / 2)
    (hZ : ∀ j ∈ univ.erase o, F.currentIncidentSide incoming o j → F.currentZeta o j ≤ B) :
    (∑ j, F.currentIncidentEdge incoming o j) ≤ (F.currentMasses o / 2) * B := by
  let q := F.currentMasses o
  have hq : 0 < q := F.mass_pos (F.currentOrder o)
  have hPoint (j : Fin n) (hj : j ∈ univ.erase o) :
      F.currentIncidentEdge incoming o j ≤
        (q * B) * (if F.currentIncidentSide incoming o j then F.currentRowMark o j else 0) := by
    have hjo := (mem_erase.mp hj).1
    by_cases hSide : F.currentIncidentSide incoming o j
    · rw [if_pos hSide]
      calc
        _ ≤ q * F.currentRowMark o j * F.currentZeta o j := F.currentIncidentEdge_pair_bound incoming hjo
        _ ≤ q * F.currentRowMark o j * B :=
          mul_le_mul_of_nonneg_left (hZ j hj hSide) (mul_nonneg hq.le (F.currentRowMark_nonneg o j))
        _ = _ := by ring
    · rw [F.currentIncidentEdge_zero incoming hjo hSide,if_neg hSide,mul_zero]
  have hSum := sum_le_sum hPoint
  rw [← mul_sum] at hSum
  have hAll : (∑ j, F.currentIncidentEdge incoming o j) =
      ∑ j ∈ univ.erase o, F.currentIncidentEdge incoming o j := by
    rw [sum_erase_eq_sub (mem_univ o),F.currentIncidentEdge_diagonal,sub_zero]
  rw [hAll]
  have hScaled := mul_le_mul_of_nonneg_left hHalf (mul_nonneg hq.le hB)
  change (∑ j ∈ univ.erase o, F.currentIncidentEdge incoming o j) ≤ (q / 2) * B
  change (∑ j ∈ univ.erase o, F.currentIncidentEdge incoming o j) ≤
    (q * B) * F.incidentSideRow incoming o at hSum
  linarith only [hSum,hScaled]

theorem incidentSide_current_upper (hp : 0 < p) (incoming : Bool) (o : Fin n)
    (hMin : ∀ j, F.currentMasses o ≤ F.currentMasses j)
    (hHalf : F.incidentSideRow incoming o ≤ 1 / 2) :
    (∑ j, F.currentIncidentEdge incoming o j) ≤ minimumIncidentPrice p (F.currentMasses o) := by
  have hq : 0 < F.currentMasses o := F.mass_pos (F.currentOrder o)
  have hB : 0 ≤ (2 * F.currentMasses o) ^ (-(1 / p)) :=
    (Real.rpow_pos_of_pos (mul_pos (by norm_num) hq) _).le
  apply F.incidentSide_current_zeta_upper incoming o hB hHalf
  intro j hj hSide
  have hAtom := (F.incidentSideRow_atom_le incoming o j hj hSide).trans hHalf
  exact (F.currentZeta_le_inverse_chord (mem_erase.mp hj).1).trans
    (incident_inverse_chord_bound hp hq (F.currentChord_pos (mem_erase.mp hj).1) (hMin j) hAtom)

theorem minimum_incident_upper (hp : 0 < p) (o : Fin n)
    (hMin : ∀ j, F.currentMasses o ≤ F.currentMasses j)
    (hRow : 2 * F.coefficient * F.radius ^ 2 = 1) :
    (∑ j, F.currentEdges o j) ≤ minimumIncidentPrice p (F.currentMasses o) := by
  have hSides := F.incidentSideRows_le_radial o
  rw [hRow] at hSides
  have hOne : F.incidentSideRow false o ≤ 1 / 2 ∨ F.incidentSideRow true o ≤ 1 / 2 := by
    by_cases h : F.incidentSideRow false o ≤ 1 / 2
    · exact Or.inl h
    · right
      linarith only [hSides,lt_of_not_ge h]
  change (∑ j, F.currentIncidentEdge false o j) ≤ _
  rcases hOne with h | h
  · exact F.incidentSide_current_upper hp false o hMin h
  · rw [F.incidentSide_current_conservation o]
    exact F.incidentSide_current_upper hp true o hMin h

theorem minimum_current_upper (hp : 3 ≤ p) (o : Fin n)
    (hMin : ∀ j, F.currentMasses o ≤ F.currentMasses j)
    (hRow : 2 * F.coefficient * F.radius ^ 2 = 1) :
    F.commonCurrent ≤ minimumIncidentPrice p (F.currentMasses o) +
      crossingCoefficient p * F.totalCrossMoment o ^ 2 := by
  exact (F.commonCurrent_le_incident_add_cross hp o).trans
    (add_le_add (F.minimum_incident_upper (by linarith only [hp]) o hMin hRow) le_rfl)

end ACS12.Configuration

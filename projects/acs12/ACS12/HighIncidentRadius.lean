import ACS12.HighMinimumIncident

/-! The same original smaller incident side retains its actual physical radius in the current price. -/
namespace ACS12.Configuration

open Finset HighCurrent
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {p : ℝ} (F : ACS12.Configuration n p)

theorem incidentSide_zeta_radius_bound (hp : 0 < p) (incoming : Bool) (o : Fin n)
    (hMin : ∀ j, F.currentMasses o ≤ F.currentMasses j)
    (hHalf : F.incidentSideRow incoming o ≤ 1 / 2) (j : Fin n)
    (hj : j ∈ univ.erase o) (hSide : F.currentIncidentSide incoming o j) :
    F.currentZeta o j ≤ Real.sqrt
      ((2 * F.currentMasses o) ^ (-(2 / p)) - 1 / (2 * F.radius) ^ 2) := by
  have hq : 0 < F.currentMasses o := F.mass_pos (F.currentOrder o)
  have hChord := F.currentChord_pos (mem_erase.mp hj).1
  have hAtom := (F.incidentSideRow_atom_le incoming o j hj hSide).trans hHalf
  have hInv := incident_inverse_chord_bound hp hq hChord (hMin j) hAtom
  have hSq := pow_le_pow_left₀ (one_div_pos.mpr hChord).le hInv 2
  have hId := F.currentZeta_chord_identity (Ne.symm (mem_erase.mp hj).1)
  change 1 / (2 * F.radius) ^ 2 + F.currentZeta o j ^ 2 = 1 / F.currentChord o j ^ 2 at hId
  have hInvSq : (1 / F.currentChord o j) ^ (2 : ℕ) = 1 / F.currentChord o j ^ (2 : ℕ) := by
    rw [div_pow,one_pow]
  have hPower : ((2 * F.currentMasses o) ^ (-(1 / p))) ^ (2 : ℕ) =
      (2 * F.currentMasses o) ^ (-(2 / p)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (mul_pos (by norm_num : (0 : ℝ) < 2) hq).le]
    congr 1
    push_cast
    ring
  rw [hPower,hInvSq] at hSq
  exact Real.le_sqrt_of_sq_le (by linarith only [hSq,hId])

theorem incidentSide_current_radius_upper (hp : 0 < p) (incoming : Bool) (o : Fin n)
    (hMin : ∀ j, F.currentMasses o ≤ F.currentMasses j)
    (hHalf : F.incidentSideRow incoming o ≤ 1 / 2) :
    (∑ j, F.currentIncidentEdge incoming o j) ≤ (F.currentMasses o / 2) *
      Real.sqrt ((2 * F.currentMasses o) ^ (-(2 / p)) - 1 / (2 * F.radius) ^ 2) := by
  apply F.incidentSide_current_zeta_upper incoming o (Real.sqrt_nonneg _) hHalf
  intro j hj hSide
  exact F.incidentSide_zeta_radius_bound hp incoming o hMin hHalf j hj hSide

theorem minimum_incident_radius_upper (hp : 0 < p) (o : Fin n)
    (hMin : ∀ j, F.currentMasses o ≤ F.currentMasses j)
    (hRow : 2 * F.coefficient * F.radius ^ 2 = 1) :
    (∑ j, F.currentEdges o j) ≤ (F.currentMasses o / 2) *
      Real.sqrt ((2 * F.currentMasses o) ^ (-(2 / p)) - 1 / (2 * F.radius) ^ 2) := by
  have hSides := F.incidentSideRows_le_radial o
  rw [hRow] at hSides
  have hOne : F.incidentSideRow false o ≤ 1 / 2 ∨ F.incidentSideRow true o ≤ 1 / 2 := by
    by_cases h : F.incidentSideRow false o ≤ 1 / 2
    · exact Or.inl h
    · right
      linarith only [hSides,lt_of_not_ge h]
  change (∑ j, F.currentIncidentEdge false o j) ≤ _
  rcases hOne with h | h
  · exact F.incidentSide_current_radius_upper hp false o hMin h
  · rw [F.incidentSide_current_conservation o]
    exact F.incidentSide_current_radius_upper hp true o hMin h

end ACS12.Configuration

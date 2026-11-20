import ACS12.HighIncidentChordBound

/-! Both literal incident sides retain the same original radial marks and conserved torque. -/
namespace ACS12.Configuration

open Finset HighCurrent
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {p : ℝ} (F : ACS12.Configuration n p)

noncomputable def currentRowMark (o j : Fin n) : ℝ :=
  F.currentMasses j / F.currentChord o j ^ p

def currentIncidentSide (incoming : Bool) (o j : Fin n) : Prop :=
  if incoming then Real.pi / 2 < halfArc F.currentAngles o j
    else halfArc F.currentAngles o j < Real.pi / 2

noncomputable instance currentIncidentSide_decidable (incoming : Bool) (o j : Fin n) :
    Decidable (F.currentIncidentSide incoming o j) := by
  unfold currentIncidentSide
  cases incoming <;> dsimp <;> infer_instance

noncomputable def currentIncidentEdge (incoming : Bool) (o j : Fin n) : ℝ :=
  if incoming then F.currentEdges j o else F.currentEdges o j

noncomputable def incidentSideRow (incoming : Bool) (o : Fin n) : ℝ :=
  ∑ j ∈ univ.erase o, if F.currentIncidentSide incoming o j then F.currentRowMark o j else 0

theorem currentRowMark_nonneg (o j : Fin n) : 0 ≤ F.currentRowMark o j := by
  unfold currentRowMark
  exact div_nonneg (F.mass_pos (F.currentOrder j)).le
    (Real.rpow_nonneg (norm_nonneg _) _)

theorem incidentSideRow_nonneg (incoming : Bool) (o : Fin n) : 0 ≤ F.incidentSideRow incoming o :=
  sum_nonneg (fun j _ => by split_ifs; exact F.currentRowMark_nonneg o j; exact le_rfl)

theorem currentRowMark_total (o : Fin n) :
    (∑ j ∈ univ.erase o, F.currentRowMark o j) = 2 * F.coefficient * F.radius ^ 2 := by
  have h := F.currentReweighted_radial o
  rw [sum_congr rfl (fun j hj => F.currentReweighted_row_identity (mem_erase.mp hj).1)] at h
  exact h

theorem incidentSideRows_le_radial (o : Fin n) :
    F.incidentSideRow false o + F.incidentSideRow true o ≤ 2 * F.coefficient * F.radius ^ 2 := by
  rw [← F.currentRowMark_total o]
  unfold incidentSideRow
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro j _
  have hMark := F.currentRowMark_nonneg o j
  unfold currentIncidentSide
  simp only [Bool.false_eq_true,if_false,if_true]
  split_ifs <;> simp_all <;> linarith

theorem currentIncidentEdge_diagonal (incoming : Bool) (o : Fin n) :
    F.currentIncidentEdge incoming o o = 0 := by
  unfold currentIncidentEdge
  split_ifs <;> exact F.currentEdges_diagonal o

theorem currentIncidentEdge_zero (incoming : Bool) {o j : Fin n} (hjo : j ≠ o)
    (hSide : ¬F.currentIncidentSide incoming o j) : F.currentIncidentEdge incoming o j = 0 := by
  cases incoming
  · change ¬halfArc F.currentAngles o j < Real.pi / 2 at hSide
    change F.currentEdges o j = 0
    unfold currentEdges shorterCurrent
    rw [if_neg (Ne.symm hjo),if_neg hSide]
  · change ¬Real.pi / 2 < halfArc F.currentAngles o j at hSide
    change F.currentEdges j o = 0
    unfold currentEdges shorterCurrent
    rw [if_neg hjo,halfArc_flip F.currentAngles hjo.symm,
      if_neg (by linarith only [le_of_not_gt hSide])]

theorem currentIncidentEdge_pair_bound (incoming : Bool) {o j : Fin n} (hjo : j ≠ o) :
    F.currentIncidentEdge incoming o j ≤
      F.currentMasses o * F.currentRowMark o j * F.currentZeta o j := by
  have hPair := F.current_pair_identity hjo.symm
  have hFirst := F.currentEdges_nonneg o j
  have hSecond := F.currentEdges_nonneg j o
  have hPaid : F.currentEdges o j + F.currentEdges j o =
      F.currentMasses o * F.currentRowMark o j * F.currentZeta o j := by
    rw [hPair]
    unfold currentRowMark currentChord
    ring
  cases incoming <;> change _ ≤ F.currentMasses o * F.currentRowMark o j * F.currentZeta o j
  · change F.currentEdges o j ≤ _
    linarith only [hPaid,hSecond]
  · change F.currentEdges j o ≤ _
    linarith only [hPaid,hFirst]

theorem incidentSide_current_conservation (o : Fin n) :
    (∑ j, F.currentIncidentEdge false o j) = ∑ j, F.currentIncidentEdge true o j := by
  have h := F.currentEdges_divergence_zero o
  unfold nodeDivergence at h
  change (∑ j, F.currentEdges o j) = ∑ j, F.currentEdges j o
  linarith only [h]

end ACS12.Configuration

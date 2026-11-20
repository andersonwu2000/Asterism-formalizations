import ACS12.HighPhysicalCrossKernel
import ACS12.HighRectangleBound
import ACS12.HighCutNodeDecomposition

/-! The entire original nonincident crossing rectangle is bounded once by its complete root moment. -/
namespace ACS12.Configuration

open Finset HighCurrent
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {p : ℝ} (F : ACS12.Configuration n p)

noncomputable def nonincidentCurrent (o : Fin n) : ℝ :=
  ∑ i ∈ univ.erase o, ∑ j ∈ univ.erase o,
    F.currentEdges i j * cutIndicator (F.currentAngles i) (F.currentAngles j) (F.currentAngles o)

noncomputable def totalCrossMoment (o : Fin n) : ℝ :=
  ∑ j ∈ univ.erase o, F.currentCrossMoment o j

theorem nonincidentCurrent_nonneg (o : Fin n) : 0 ≤ F.nonincidentCurrent o :=
  sum_nonneg (fun i _ => sum_nonneg (fun j _ =>
    mul_nonneg (F.currentEdges_nonneg i j) (cutIndicator_bounds _ _ _).1))

theorem nonincident_current_upper (hp : 3 ≤ p) (o : Fin n) :
    F.nonincidentCurrent o ≤ crossingCoefficient p * F.totalCrossMoment o ^ 2 := by
  apply complete_rectangle_bound (univ.erase o) (F.currentCrossMoment o)
    (fun i => Real.pi / 2 < halfArc F.currentAngles o i)
    (fun j => halfArc F.currentAngles o j < Real.pi / 2)
    (fun i j => F.currentEdges i j *
      cutIndicator (F.currentAngles i) (F.currentAngles j) (F.currentAngles o))
    (crossingCoefficient_pos (by linarith only [hp])).le
  · intro i hi
    exact (F.currentCrossMoment_pos (mem_erase.mp hi).1).le
  · intro i _ hi
    exact (not_lt_of_gt hi.1) hi.2
  · intro i hi j hj
    exact F.nonincident_current_pair_bound hp (mem_erase.mp hi).1 (mem_erase.mp hj).1

theorem commonCurrent_node_decomposition (o : Fin n) :
    F.commonCurrent = (∑ j, F.currentEdges o j) + F.nonincidentCurrent o := by
  rw [← F.currentAt_constant (F.currentAngles o)]
  exact cutFlux_node_decomposition F.currentAngles F.currentEdges
    F.currentAngles_strictMono.injective F.currentEdges_diagonal o

theorem commonCurrent_le_incident_add_cross (hp : 3 ≤ p) (o : Fin n) :
    F.commonCurrent ≤ (∑ j, F.currentEdges o j) + crossingCoefficient p * F.totalCrossMoment o ^ 2 := by
  rw [F.commonCurrent_node_decomposition]
  exact add_le_add le_rfl (F.nonincident_current_upper hp o)

end ACS12.Configuration

import ACS12.HighShorterCurrent

/-! The original full physical torque rows conserve the same shorter-route cut current. -/
namespace ACS12.Configuration

open Finset HighCurrent CenteredCircle.AllN

variable {n : ℕ} {α : ℝ} (F : ACS12.Configuration n α)

noncomputable def currentOrder : Equiv.Perm (Fin n) := Tuple.sort F.phase
noncomputable def currentAngles : Fin n → ℝ := F.phase ∘ F.currentOrder
noncomputable def currentMasses : Fin n → ℝ := F.mass ∘ F.currentOrder
noncomputable def currentEdges : Fin n → Fin n → ℝ :=
  shorterCurrent α (2 * F.radius) F.currentAngles F.currentMasses
noncomputable def currentAt (t : ℝ) : ℝ := cutFlux F.currentAngles F.currentEdges t
noncomputable def commonCurrent : ℝ := wrapFlux F.currentAngles F.currentEdges

theorem currentAngles_strictMono : StrictMono F.currentAngles := by
  exact (Tuple.monotone_sort F.phase).strictMono_of_injective
    (F.phase_injective.comp F.currentOrder.injective)

theorem currentAngles_nonneg (i : Fin n) : 0 ≤ F.currentAngles i := (positiveAngle_range _).1
theorem currentAngles_lt_two_pi (i : Fin n) : F.currentAngles i < 2 * Real.pi := (positiveAngle_range _).2

theorem currentEdges_nonneg (i j : Fin n) : 0 ≤ F.currentEdges i j :=
  shorterCurrent_nonneg α (mul_pos (by norm_num) F.radius_pos) F.currentAngles F.currentMasses
    F.currentAngles_strictMono F.currentAngles_nonneg F.currentAngles_lt_two_pi
    (fun k => (F.mass_pos (F.currentOrder k)).le) i j

theorem currentEdges_diagonal (i : Fin n) : F.currentEdges i i = 0 :=
  shorterCurrent_diagonal α (2 * F.radius) F.currentAngles F.currentMasses i

theorem currentEdges_divergence_zero (i : Fin n) : nodeDivergence F.currentEdges i = 0 := by
  have hRow := F.weighted_angular_row F.currentAngles F.currentOrder F.currentAngles_strictMono
    F.currentAngles_nonneg F.currentAngles_lt_two_pi (fun k => F.phase_eq (F.currentOrder k)) i
  change (∑ j ∈ univ.erase i, F.currentMasses j * angularKernel α (halfArc F.currentAngles i j)) = 0 at hRow
  unfold currentEdges
  rw [shorterCurrent_divergence,hRow,mul_zero]

theorem currentAt_constant (t : ℝ) : F.currentAt t = F.commonCurrent :=
  cutFlux_constant F.currentAngles F.currentEdges F.currentEdges_divergence_zero t

theorem commonCurrent_nonneg : 0 ≤ F.commonCurrent := by
  rw [← F.currentAt_constant 0]
  exact cutFlux_nonneg F.currentAngles F.currentEdges F.currentEdges_nonneg 0

theorem current_total_incident_le (o : Fin n) :
    (∑ j, F.currentEdges o j) + (∑ j, F.currentEdges j o) ≤ 2 * F.commonCurrent :=
  total_incident_le_two_flux F.currentAngles F.currentEdges F.currentAngles_strictMono.injective
    F.currentEdges_nonneg F.currentEdges_diagonal F.currentEdges_divergence_zero o

theorem currentEdge_chord {i j : Fin n} (hij : i ≠ j)
    (hShort : halfArc F.currentAngles i j < Real.pi / 2) :
    F.currentEdges i j =
      F.currentMasses i * F.currentMasses j * Real.cos (halfArc F.currentAngles i j) /
        ‖F.position (F.currentOrder j) - F.position (F.currentOrder i)‖ ^ (α + 1) := by
  have hArc := halfArc_mem F.currentAngles_strictMono F.currentAngles_nonneg F.currentAngles_lt_two_pi hij.symm
  have hSin := Real.sin_pos_of_pos_of_lt_pi hArc.1 hArc.2
  have hD : 0 < 2 * F.radius := mul_pos (by norm_num) F.radius_pos
  have hChord := F.chord_eq_halfArc F.currentAngles F.currentOrder
    (fun k => F.phase_eq (F.currentOrder k)) hArc
  unfold currentEdges
  rw [shorterCurrent,if_neg hij,if_pos hShort,hChord,Real.mul_rpow hD.le hSin.le]
  unfold angularKernel
  ring

end ACS12.Configuration

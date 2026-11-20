import ACS12.HighCrossPairKernel
import ACS12.HighCrossCutGeometry
import ACS12.HighPhysicalReweight

/-! The original nonincident crossing edge is paid on the same complete two root-relative sides. -/
namespace ACS12.Configuration

open HighCurrent
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {p : ℝ} (F : ACS12.Configuration n p)

noncomputable def currentCrossMoment (o j : Fin n) : ℝ :=
  F.currentMasses j / F.currentChord o j ^ ((p + 1) / 2)

theorem currentCrossMoment_pos {o j : Fin n} (hjo : j ≠ o) :
    0 < F.currentCrossMoment o j :=
  div_pos (F.mass_pos (F.currentOrder j)) (Real.rpow_pos_of_pos (F.currentChord_pos hjo) _)

theorem nonincident_current_pair_bound (hp : 3 ≤ p) {o i j : Fin n}
    (hio : i ≠ o) (hjo : j ≠ o) :
    F.currentEdges i j * cutIndicator (F.currentAngles i) (F.currentAngles j) (F.currentAngles o) ≤
      4 * crossingCoefficient p *
        (if Real.pi / 2 < halfArc F.currentAngles o i then F.currentCrossMoment o i else 0) *
        (if halfArc F.currentAngles o j < Real.pi / 2 then F.currentCrossMoment o j else 0) := by
  have hC : 0 < crossingCoefficient p := crossingCoefficient_pos (by linarith only [hp])
  have hMi := F.currentCrossMoment_pos hio
  have hMj := F.currentCrossMoment_pos hjo
  have hRight : 0 ≤ 4 * crossingCoefficient p *
      (if Real.pi / 2 < halfArc F.currentAngles o i then F.currentCrossMoment o i else 0) *
      (if halfArc F.currentAngles o j < Real.pi / 2 then F.currentCrossMoment o j else 0) := by
    split_ifs <;> positivity
  by_cases hij : i = j
  · subst j
    rw [F.currentEdges_diagonal,zero_mul]
    exact hRight
  by_cases hShort : halfArc F.currentAngles i j < Real.pi / 2
  · rcases cutIndicator_zero_or_one (F.currentAngles i) (F.currentAngles j) (F.currentAngles o) with hZero | hOne
    · rw [hZero,mul_zero]
      exact hRight
    · have hGeometry := crossing_cut_halfArcs F.currentAngles F.currentAngles_strictMono
        F.currentAngles_nonneg F.currentAngles_lt_two_pi hio hjo hij hShort hOne
      let u := Real.pi - halfArc F.currentAngles o i
      let v := halfArc F.currentAngles o j
      let D := 2 * F.radius
      have hArcI := halfArc_mem F.currentAngles_strictMono F.currentAngles_nonneg F.currentAngles_lt_two_pi hio
      have hArcJ := halfArc_mem F.currentAngles_strictMono F.currentAngles_nonneg F.currentAngles_lt_two_pi hjo
      have hArcIJ := halfArc_mem F.currentAngles_strictMono F.currentAngles_nonneg F.currentAngles_lt_two_pi (Ne.symm hij)
      have hD : 0 < D := mul_pos (by norm_num) F.radius_pos
      have hu : 0 < u := sub_pos.mpr hArcI.2
      have hv : 0 < v := hArcJ.1
      have hSum : u + v = halfArc F.currentAngles i j := hGeometry.2.2.symm
      have hKernel := crossing_pair_kernel hp hD hu hv (hSum.le.trans hShort.le)
      have hChordI : F.currentChord o i = D * Real.sin u := by
        have h := F.chord_eq_halfArc F.currentAngles F.currentOrder
          (fun k => F.phase_eq (F.currentOrder k)) hArcI
        simpa only [currentChord,D,u,Real.sin_pi_sub] using h
      have hChordJ : F.currentChord o j = D * Real.sin v :=
        F.chord_eq_halfArc F.currentAngles F.currentOrder (fun k => F.phase_eq (F.currentOrder k)) hArcJ
      rw [hSum,← hChordI,← hChordJ] at hKernel
      rw [hOne,mul_one,if_pos hGeometry.1,if_pos hGeometry.2.1,
        F.currentEdge_chord hij hShort,
        F.chord_eq_halfArc F.currentAngles F.currentOrder (fun k => F.phase_eq (F.currentOrder k)) hArcIJ]
      calc
        _ = (F.currentMasses i * F.currentMasses j) *
            (Real.cos (halfArc F.currentAngles i j) / (D * Real.sin (halfArc F.currentAngles i j)) ^ (p + 1)) := by
          unfold D
          ring
        _ ≤ (F.currentMasses i * F.currentMasses j) *
            (4 * crossingCoefficient p / (F.currentChord o i * F.currentChord o j) ^ ((p + 1) / 2)) :=
          mul_le_mul_of_nonneg_left hKernel (mul_nonneg (F.mass_pos (F.currentOrder i)).le (F.mass_pos (F.currentOrder j)).le)
        _ = _ := by
          rw [Real.mul_rpow (F.currentChord_pos hio).le (F.currentChord_pos hjo).le]
          unfold currentCrossMoment
          ring
  · have hZero : F.currentEdges i j = 0 := by
      unfold currentEdges shorterCurrent
      rw [if_neg hij,if_neg hShort]
    rw [hZero,zero_mul]
    exact hRight

end ACS12.Configuration

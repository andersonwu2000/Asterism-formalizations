import ACS12.Angular
import ACS12.ChartArc

/-! Transport the original equations into the attained finite incident chart.
The chart and its circular packing caps come from the reused geometric
construction. The radial kernel is the exact csc power at the actual period. -/

namespace ACS12

open scoped BigOperators
open CenteredCircle.AllN
set_option backward.isDefEq.respectTransparency false

noncomputable def circlePower (α L t : ℝ) : ℝ :=
  (Real.pi / L) ^ α / Real.sin (Real.pi * t / L) ^ α

noncomputable def circleTorque (α L t : ℝ) : ℝ :=
  angularKernel α (Real.pi * t / L)

theorem hasDerivAt_circlePower (α : ℝ) {L t : ℝ} (hL : 0 < L)
    (ht : 0 < t) (htL : t < L) :
    HasDerivAt (circlePower α L)
      (-α * (Real.pi / L) ^ (α + 1) * circleTorque α L t) t := by
  let k := Real.pi / L
  have hk : 0 < k := div_pos Real.pi_pos hL
  have hs := periodic_angle_sin_pos hL ht htL
  have hsk : 0 < Real.sin (k * t) := by
    simpa only [k, div_mul_eq_mul_div] using hs
  have ht' : HasDerivAt (fun x : ℝ => k * x) k t := by
    simpa only [mul_one] using (hasDerivAt_id t).const_mul k
  have h := (hasDerivAt_const t (k ^ α)).div
    (((Real.hasDerivAt_sin (k * t)).comp t ht').rpow_const (p := α) (Or.inl hsk.ne'))
    (Real.rpow_pos_of_pos hsk α).ne'
  simp only [Function.comp_apply] at h
  rw [Real.rpow_sub hsk, Real.rpow_one] at h
  have hp : Real.sin (k * t) ^ (α + 1) =
      Real.sin (k * t) ^ α * Real.sin (k * t) := by
    rw [Real.rpow_add hsk, Real.rpow_one]
  have hq : k ^ (α + 1) = k ^ α * k := by
    rw [Real.rpow_add hk, Real.rpow_one]
  have hfun : circlePower α L = fun x => k ^ α / Real.sin (k * x) ^ α := by
    funext x
    simp only [circlePower, k, div_mul_eq_mul_div]
  rw [hfun, circleTorque, angularKernel, ← div_mul_eq_mul_div]
  change HasDerivAt (fun x => k ^ α / Real.sin (k * x) ^ α)
    (-α * k ^ (α + 1) * (Real.cos (k * t) / Real.sin (k * t) ^ (α + 1))) t
  rw [hp, hq]
  convert h using 1
  field_simp [hsk.ne', (Real.rpow_pos_of_pos hsk α).ne']; ring

namespace Configuration

variable {n : ℕ} {α : ℝ} (F : Configuration n α)

theorem exists_normalized_chart (hn : 2 ≤ n) :
    Nonempty (NormalizedCircleChart F.phase F.mass (2 * Real.pi)) := by
  apply exists_normalized_circle_chart F.phase F.mass (fun i => (positiveAngle_range _).1)
    (fun i => (positiveAngle_range _).2) F.phase_injective F.mass_pos
  simpa only [Fintype.card_fin] using hn

variable (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi))

private theorem phase_in_chart (i : Fin n) :
    F.position i = F.center + ((F.radius : ℂ) * unitRay (F.phase C.source.root)) *
      unitRay (orientedPhase C.forward (C.scale * C.source.coordinate i)) := by
  rw [F.phase_eq, C.phase_presentation]
  ring

private theorem chart_pair (i j : Fin n) {t : ℝ}
    (ht : 0 < t) (htL : t < C.source.period)
    (hphase : unitRay (C.scale * C.source.coordinate j - C.scale * C.source.coordinate i) =
      unitRay (2 * Real.pi * t / C.source.period)) :
    ‖F.position j - F.position i‖ = (2 * F.radius) * Real.sin (Real.pi * t / C.source.period) ∧
    ((F.position j - F.position i) * star (F.position i - F.center)).im =
      F.radius ^ 2 * orientationSign C.forward * Real.sin (2 * Real.pi * t / C.source.period) := by
  have hs := congrArg Complex.im hphase
  simp only [unitRay_im] at hs
  constructor
  · rw [F.phase_in_chart C j, F.phase_in_chart C i, rotated_pair_norm,
      regular_rotation_norm F.radius_pos, hphase, periodic_chord_length C.source.period_pos ht htL]
    ring
  · rw [F.phase_in_chart C j, F.phase_in_chart C i, rotated_pair_torque,
      regular_rotation_norm F.radius_pos, hs]

noncomputable def chartRadialScale : ℝ :=
  ((2 * F.radius) ^ α * (Real.pi / C.source.period) ^ α) / F.mass C.source.root

private noncomputable def chartTorqueScale : ℝ :=
  (2 * F.radius) ^ (α + 2) / (2 * F.radius ^ 2 * orientationSign C.forward * F.mass C.source.root)

private theorem chart_radial_term (i j : Fin n) {t : ℝ}
    (ht : 0 < t) (htL : t < C.source.period)
    (hphase : unitRay (C.scale * C.source.coordinate j - C.scale * C.source.coordinate i) =
      unitRay (2 * Real.pi * t / C.source.period)) :
    C.source.mass j * circlePower α C.source.period t =
      F.chartRadialScale C * (F.mass j / ‖F.position j - F.position i‖ ^ α) := by
  have hR := F.radius_pos
  have hs := periodic_angle_sin_pos C.source.period_pos ht htL
  rw [C.mass_eq, (F.chart_pair C i j ht htL hphase).1, circlePower, chartRadialScale,
    Real.mul_rpow (by positivity) hs.le]
  field_simp [(Real.rpow_pos_of_pos (show 0 < 2 * F.radius by positivity) α).ne']

private theorem chart_torque_term (i j : Fin n) {t : ℝ}
    (ht : 0 < t) (htL : t < C.source.period)
    (hphase : unitRay (C.scale * C.source.coordinate j - C.scale * C.source.coordinate i) =
      unitRay (2 * Real.pi * t / C.source.period)) :
    C.source.mass j * circleTorque α C.source.period t =
      F.chartTorqueScale C * ((F.mass j / ‖F.position j - F.position i‖ ^ (α + 2)) *
        ((F.position j - F.position i) * star (F.position i - F.center)).im) := by
  have hR := F.radius_pos
  have hs := periodic_angle_sin_pos C.source.period_pos ht htL
  have hpow : Real.sin (Real.pi * t / C.source.period) ^ (α + 2) =
      Real.sin (Real.pi * t / C.source.period) ^ (α + 1) *
        Real.sin (Real.pi * t / C.source.period) := by
    rw [show α + 2 = (α + 1) + 1 by ring, Real.rpow_add hs, Real.rpow_one]
  obtain ⟨hd, him⟩ := F.chart_pair C i j ht htL hphase
  rw [C.mass_eq, hd, him, circleTorque, angularKernel, chartTorqueScale,
    Real.mul_rpow (by positivity) hs.le,
    show 2 * Real.pi * t / C.source.period = 2 * (Real.pi * t / C.source.period) by ring,
    Real.sin_two_mul, hpow]
  field_simp [hR.ne', hs.ne', (F.mass_pos C.source.root).ne', orientationSign_ne_zero,
    (Real.rpow_pos_of_pos hs (α + 1)).ne',
    (Real.rpow_pos_of_pos (show 0 < 2 * F.radius by positivity) (α + 2)).ne']

/-- The two actual anchored radial rows agree with the same csc-power kernel. -/
theorem anchored_radial_eq :
    (∑ j ∈ Finset.univ.erase C.source.root,
      C.source.mass j * circlePower α C.source.period (C.source.coordinate j)) =
    (∑ j ∈ Finset.univ.erase C.source.neighbor,
      C.source.mass j * circlePower α C.source.period (C.source.rightDistance j)) := by
  have hr : (∑ j ∈ Finset.univ.erase C.source.root,
      C.source.mass j * circlePower α C.source.period (C.source.coordinate j)) =
      F.chartRadialScale C * (2 * F.coefficient * F.radius ^ 2) := by
    rw [← F.radial_row C.source.root, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j hj =>
      F.chart_radial_term C _ _ (C.source.coordinate_pos_of_ne_root (Finset.mem_erase.mp hj).1)
        (C.source.coordinate_lt_period j) (C.root_pair_phase j)
  have hb : (∑ j ∈ Finset.univ.erase C.source.neighbor,
      C.source.mass j * circlePower α C.source.period (C.source.rightDistance j)) =
      F.chartRadialScale C * (2 * F.coefficient * F.radius ^ 2) := by
    rw [← F.radial_row C.source.neighbor, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j hj =>
      F.chart_radial_term C _ _ (C.source.rightDistance_pos j)
        (C.source.rightDistance_lt_period (Finset.mem_erase.mp hj).1) (C.neighbor_pair_phase j)
  exact hr.trans hb.symm

/-- Both actual anchored torque rows vanish, with their physical orientation. -/
theorem anchored_torque_eq_zero :
    (∑ j ∈ Finset.univ.erase C.source.root,
      C.source.mass j * circleTorque α C.source.period (C.source.coordinate j)) = 0 ∧
    (∑ j ∈ Finset.univ.erase C.source.neighbor,
      C.source.mass j * circleTorque α C.source.period (C.source.rightDistance j)) = 0 := by
  constructor
  · rw [← mul_zero (F.chartTorqueScale C), ← F.tangential_row C.source.root, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j hj =>
      F.chart_torque_term C _ _ (C.source.coordinate_pos_of_ne_root (Finset.mem_erase.mp hj).1)
        (C.source.coordinate_lt_period j) (C.root_pair_phase j)
  · rw [← mul_zero (F.chartTorqueScale C), ← F.tangential_row C.source.neighbor, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j hj =>
      F.chart_torque_term C _ _ (C.source.rightDistance_pos j)
        (C.source.rightDistance_lt_period (Finset.mem_erase.mp hj).1) (C.neighbor_pair_phase j)

/-- Every occupied radial row has the same scaled physical level in the chart. -/
theorem chart_forward_radial_eq (i : Fin n) :
    (∑ j ∈ Finset.univ.erase i,
      C.source.mass j * circlePower α C.source.period (C.source.forwardDistance i j)) =
      F.chartRadialScale C * (2 * F.coefficient * F.radius ^ 2) := by
  rw [← F.radial_row i, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hij := (Finset.mem_erase.mp hj).1.symm
  exact F.chart_radial_term C i j (C.source.forwardDistance_pos i j)
    (C.source.forwardDistance_lt_period hij) (C.forward_pair_phase hij)

/-- Every occupied torque row vanishes in the same oriented chart. -/
theorem chart_forward_torque_eq_zero (i : Fin n) :
    (∑ j ∈ Finset.univ.erase i,
      C.source.mass j * circleTorque α C.source.period (C.source.forwardDistance i j)) = 0 := by
  rw [← mul_zero (F.chartTorqueScale C), ← F.tangential_row i, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hij := (Finset.mem_erase.mp hj).1.symm
  exact F.chart_torque_term C i j (C.source.forwardDistance_pos i j)
    (C.source.forwardDistance_lt_period hij) (C.forward_pair_phase hij)

end Configuration

end ACS12

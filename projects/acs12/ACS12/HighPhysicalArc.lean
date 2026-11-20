import ACS12.HighCurrentIncident
import ACS12.HighUnitPacking

/-! Both literal shorter arcs retain the original circle sites and their pair separation. -/
namespace ACS12.Configuration

open HighCurrent Set CenteredCircle.AllN
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {α : ℝ} (F : ACS12.Configuration n α)

noncomputable def currentForwardArc (o j : Fin n) : ℝ :=
  (2 * F.radius) * halfArc F.currentAngles o j

noncomputable def currentBackwardArc (o j : Fin n) : ℝ :=
  (2 * F.radius) * (Real.pi - halfArc F.currentAngles o j)

theorem currentArc_position (o j : Fin n) :
    F.position (F.currentOrder j) = F.center +
      ((F.radius : ℂ) * unitRay (F.currentAngles o)) *
        unitRay (2 * halfArc F.currentAngles o j) := by
  rw [F.phase_eq]
  change F.center + (F.radius : ℂ) * unitRay (F.currentAngles j) = _
  rw [halfArc_phase,mul_assoc,← unitRay_add]
  congr 2
  ring

theorem currentForwardArc_pair_chord (o j k : Fin n) :
    ‖F.position (F.currentOrder j) - F.position (F.currentOrder k)‖ ≤
      |F.currentForwardArc o j - F.currentForwardArc o k| := by
  rw [F.currentArc_position o j,F.currentArc_position o k,add_sub_add_left_eq_sub,
    ← mul_sub,norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg F.radius_pos.le,
    norm_unitRay,mul_one]
  have h := mul_le_mul_of_nonneg_left
    (unitRay_chord_le (2 * halfArc F.currentAngles o j) (2 * halfArc F.currentAngles o k)) F.radius_pos.le
  have hAbs : |F.currentForwardArc o j - F.currentForwardArc o k| =
      F.radius * |2 * halfArc F.currentAngles o j - 2 * halfArc F.currentAngles o k| := by
    unfold currentForwardArc
    rw [show (2 * F.radius) * halfArc F.currentAngles o j -
      (2 * F.radius) * halfArc F.currentAngles o k =
      F.radius * (2 * halfArc F.currentAngles o j - 2 * halfArc F.currentAngles o k) by ring,
      abs_mul,abs_of_pos F.radius_pos]
  rwa [hAbs]

theorem currentBackwardArc_pair_chord (o j k : Fin n) :
    ‖F.position (F.currentOrder j) - F.position (F.currentOrder k)‖ ≤
      |F.currentBackwardArc o j - F.currentBackwardArc o k| := by
  have h := F.currentForwardArc_pair_chord o j k
  have hAbs : |F.currentBackwardArc o j - F.currentBackwardArc o k| =
      |F.currentForwardArc o j - F.currentForwardArc o k| := by
    unfold currentBackwardArc currentForwardArc
    rw [show (2 * F.radius) * (Real.pi - halfArc F.currentAngles o j) -
      (2 * F.radius) * (Real.pi - halfArc F.currentAngles o k) =
      -((2 * F.radius) * halfArc F.currentAngles o j -
        (2 * F.radius) * halfArc F.currentAngles o k) by ring,abs_neg]
  rwa [hAbs]

theorem currentForwardArc_root_chord {o j : Fin n} (hjo : j ≠ o) :
    ‖F.position (F.currentOrder j) - F.position (F.currentOrder o)‖ ≤ F.currentForwardArc o j := by
  have hArc := halfArc_mem F.currentAngles_strictMono F.currentAngles_nonneg F.currentAngles_lt_two_pi hjo
  rw [F.chord_eq_halfArc F.currentAngles F.currentOrder (fun k => F.phase_eq (F.currentOrder k)) hArc]
  exact mul_le_mul_of_nonneg_left (Real.sin_le hArc.1.le) (mul_nonneg (by norm_num) F.radius_pos.le)

theorem currentBackwardArc_root_chord {o j : Fin n} (hjo : j ≠ o) :
    ‖F.position (F.currentOrder j) - F.position (F.currentOrder o)‖ ≤ F.currentBackwardArc o j := by
  have hArc := halfArc_mem F.currentAngles_strictMono F.currentAngles_nonneg F.currentAngles_lt_two_pi hjo
  rw [F.chord_eq_halfArc F.currentAngles F.currentOrder (fun k => F.phase_eq (F.currentOrder k)) hArc]
  have hSin := Real.sin_le (sub_pos.mpr hArc.2).le
  rw [Real.sin_pi_sub] at hSin
  exact mul_le_mul_of_nonneg_left hSin (mul_nonneg (by norm_num) F.radius_pos.le)

end ACS12.Configuration

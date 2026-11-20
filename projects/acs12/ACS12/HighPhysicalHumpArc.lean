import ACS12.HighPhysicalArc
import ACS12.HighCurrentArc

/-! Each original half-circle receives the same nonnegative zeta under its own literal arc. -/
namespace ACS12.Configuration

open HighCurrent Set
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {α : ℝ} (F : ACS12.Configuration n α)

theorem currentZeta_forward {o j : Fin n} (hjo : j ≠ o)
    (hSide : halfArc F.currentAngles o j ≤ Real.pi / 2) :
    F.currentZeta o j = circleCurrentZeta (2 * F.radius) (F.currentForwardArc o j) := by
  have hArc := halfArc_mem F.currentAngles_strictMono F.currentAngles_nonneg F.currentAngles_lt_two_pi hjo
  have hCos := Real.cos_nonneg_of_mem_Icc
    (show halfArc F.currentAngles o j ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) by
      constructor <;> linarith only [hArc.1,hSide,Real.pi_pos])
  have hD : 0 < 2 * F.radius := mul_pos (by norm_num) F.radius_pos
  have hArg : F.currentForwardArc o j / (2 * F.radius) = halfArc F.currentAngles o j := by
    unfold currentForwardArc
    exact mul_div_cancel_left₀ _ hD.ne'
  simp only [currentZeta,circleCurrentZeta,hArg,abs_of_nonneg hCos]

theorem currentZeta_backward {o j : Fin n} (hjo : j ≠ o)
    (hSide : Real.pi / 2 ≤ halfArc F.currentAngles o j) :
    F.currentZeta o j = circleCurrentZeta (2 * F.radius) (F.currentBackwardArc o j) := by
  have hArc := halfArc_mem F.currentAngles_strictMono F.currentAngles_nonneg F.currentAngles_lt_two_pi hjo
  have hCos := Real.cos_nonpos_of_pi_div_two_le_of_le hSide (by linarith only [hArc.2,Real.pi_pos])
  have hD : 0 < 2 * F.radius := mul_pos (by norm_num) F.radius_pos
  have hArg : F.currentBackwardArc o j / (2 * F.radius) = Real.pi - halfArc F.currentAngles o j := by
    unfold currentBackwardArc
    exact mul_div_cancel_left₀ _ hD.ne'
  simp only [currentZeta,circleCurrentZeta,hArg,Real.cos_pi_sub,Real.sin_pi_sub,abs_of_nonpos hCos]

theorem currentForwardArc_half_bounds {o j : Fin n} (hjo : j ≠ o)
    (hChord : 1 ≤ ‖F.position (F.currentOrder j) - F.position (F.currentOrder o)‖)
    (hSide : halfArc F.currentAngles o j ≤ Real.pi / 2) :
    F.currentForwardArc o j ∈ Icc 1 (Real.pi * (2 * F.radius) / 2) := by
  constructor
  · exact hChord.trans (F.currentForwardArc_root_chord hjo)
  · unfold currentForwardArc
    have h := mul_le_mul_of_nonneg_left hSide
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) F.radius_pos.le)
    linarith only [h]

theorem currentBackwardArc_half_bounds {o j : Fin n} (hjo : j ≠ o)
    (hChord : 1 ≤ ‖F.position (F.currentOrder j) - F.position (F.currentOrder o)‖)
    (hSide : Real.pi / 2 ≤ halfArc F.currentAngles o j) :
    F.currentBackwardArc o j ∈ Icc 1 (Real.pi * (2 * F.radius) / 2) := by
  constructor
  · exact hChord.trans (F.currentBackwardArc_root_chord hjo)
  · unfold currentBackwardArc
    have h := mul_le_mul_of_nonneg_left (show Real.pi - halfArc F.currentAngles o j ≤ Real.pi / 2 by linarith only [hSide])
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) F.radius_pos.le)
    linarith only [h]

end ACS12.Configuration

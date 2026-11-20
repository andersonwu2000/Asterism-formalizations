import CenteredCircle.PhysicalAngles
import CenteredCircle.TorquePeriodization

/-! The periodic kernels are exactly the radial/torque kernels of a circle. -/

namespace CenteredCircle.AllN

set_option backward.isDefEq.respectTransparency false

theorem unitRay_im (θ : ℝ) : (unitRay θ).im = Real.sin θ := by
  simp [unitRay, Complex.exp_im]

theorem unitRay_chord (θ : ℝ) : ‖unitRay θ - 1‖ = 2 * |Real.sin (θ / 2)| := by
  have h := Complex.norm_exp_I_mul_ofReal_sub_one θ
  simpa only [unitRay, mul_comm Complex.I (θ : ℂ), Real.norm_eq_abs,
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using h

theorem periodic_angle_sin_pos {L t : ℝ} (hL : 0 < L) (ht : 0 < t) (htL : t < L) :
    0 < Real.sin (Real.pi * t / L) := by
  apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
  apply (div_lt_iff₀ hL).mpr
  nlinarith [Real.pi_pos]

theorem periodic_chord_length {L t : ℝ} (hL : 0 < L) (ht : 0 < t) (htL : t < L) :
    ‖unitRay (2 * Real.pi * t / L) - 1‖ = 2 * Real.sin (Real.pi * t / L) := by
  rw [unitRay_chord, show 2 * Real.pi * t / L / 2 = Real.pi * t / L by ring,
    abs_of_pos (periodic_angle_sin_pos hL ht htL)]

theorem periodicRadialKernel_eq_chord {L t : ℝ} (hL : 0 < L) (ht : 0 < t) (htL : t < L) :
    periodicRadialKernel L t = (2 * Real.pi / L) / ‖unitRay (2 * Real.pi * t / L) - 1‖ := by
  rw [periodic_chord_length hL ht htL, periodicRadialKernel]
  ring

theorem hasDerivAt_periodicRadialKernel_trig {L t : ℝ}
    (hL : 0 < L) (ht : 0 < t) (htL : t < L) :
    HasDerivAt (periodicRadialKernel L)
      (-(Real.pi / L) ^ 2 * Real.cos (Real.pi * t / L) / (Real.sin (Real.pi * t / L)) ^ 2) t := by
  have ha : HasDerivAt (fun x : ℝ => Real.pi * x / L) (Real.pi / L) t := by
    simpa only [mul_one] using ((hasDerivAt_id t).const_mul Real.pi).div_const L
  have hs := (Real.hasDerivAt_sin (Real.pi * t / L)).comp t ha
  have h := (hasDerivAt_const t (Real.pi / L)).div hs (ne_of_gt (periodic_angle_sin_pos hL ht htL))
  convert h using 1 <;> dsimp [periodicRadialKernel] <;> ring

theorem periodicRadialKernel_deriv_eq_chord {L t : ℝ}
    (hL : 0 < L) (ht : 0 < t) (htL : t < L) :
    deriv (periodicRadialKernel L) t =
      -(2 * Real.pi / L) ^ 2 * Real.sin (2 * Real.pi * t / L) /
        ‖unitRay (2 * Real.pi * t / L) - 1‖ ^ 3 := by
  rw [(hasDerivAt_periodicRadialKernel_trig hL ht htL).deriv,
    periodic_chord_length hL ht htL,
    show 2 * Real.pi * t / L = 2 * (Real.pi * t / L) by ring, Real.sin_two_mul]
  have hs := periodic_angle_sin_pos hL ht htL
  field_simp
  <;> ring

end CenteredCircle.AllN

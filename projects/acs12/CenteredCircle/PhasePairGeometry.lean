import CenteredCircle.OrientedPhase
import CenteredCircle.TrigonometricKernel

/-! Pairwise metric and torque identities for either orientation of a circle. -/

namespace CenteredCircle.AllN

set_option backward.isDefEq.respectTransparency false

noncomputable def orientationSign (forward : Bool) : ℝ := if forward then 1 else -1

theorem orientationSign_ne_zero (forward : Bool) : orientationSign forward ≠ 0 := by
  cases forward <;> norm_num [orientationSign]

theorem unitRay_mul_star (θ : ℝ) : unitRay θ * star (unitRay θ) = 1 := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_unitRay]
  norm_num

theorem unitRay_pair_difference (θ η : ℝ) :
    unitRay η - unitRay θ = unitRay θ * (unitRay (η - θ) - 1) := by
  rw [mul_sub, ← unitRay_add, mul_one, show θ + (η - θ) = η by ring]

theorem unitRay_pair_norm (θ η : ℝ) :
    ‖unitRay η - unitRay θ‖ = ‖unitRay (η - θ) - 1‖ := by
  rw [unitRay_pair_difference, norm_mul, norm_unitRay, one_mul]

theorem unitRay_pair_torque (θ η : ℝ) :
    ((unitRay η - unitRay θ) * star (unitRay θ)).im = Real.sin (η - θ) := by
  rw [unitRay_pair_difference,
    show (unitRay θ * (unitRay (η - θ) - 1)) * star (unitRay θ) =
      (unitRay θ * star (unitRay θ)) * (unitRay (η - θ) - 1) by ring,
    unitRay_mul_star, one_mul, Complex.sub_im, Complex.one_im, sub_zero, unitRay_im]

theorem unitRay_neg_chord (θ : ℝ) : ‖unitRay (-θ) - 1‖ = ‖unitRay θ - 1‖ := by
  rw [unitRay_chord, unitRay_chord, neg_div, Real.sin_neg, abs_neg]

theorem oriented_pair_norm (forward : Bool) (θ η : ℝ) :
    ‖unitRay (orientedPhase forward η) - unitRay (orientedPhase forward θ)‖ =
      ‖unitRay (η - θ) - 1‖ := by
  cases forward
  · change ‖unitRay (-η) - unitRay (-θ)‖ = _
    rw [unitRay_pair_norm, show -η - -θ = -(η - θ) by ring, unitRay_neg_chord]
  · exact unitRay_pair_norm θ η

theorem oriented_pair_torque (forward : Bool) (θ η : ℝ) :
    ((unitRay (orientedPhase forward η) - unitRay (orientedPhase forward θ)) *
      star (unitRay (orientedPhase forward θ))).im = orientationSign forward * Real.sin (η - θ) := by
  cases forward
  · change ((unitRay (-η) - unitRay (-θ)) * star (unitRay (-θ))).im = -1 * Real.sin (η - θ)
    rw [unitRay_pair_torque, show -η - -θ = -(η - θ) by ring, Real.sin_neg]
    ring
  · simpa only [orientedPhase, orientationSign, if_true, one_mul] using unitRay_pair_torque θ η

theorem rotated_pair_norm (center γ : ℂ) (forward : Bool) (θ η : ℝ) :
    ‖(center + γ * unitRay (orientedPhase forward η)) -
      (center + γ * unitRay (orientedPhase forward θ))‖ =
      ‖γ‖ * ‖unitRay (η - θ) - 1‖ := by
  rw [show (center + γ * unitRay (orientedPhase forward η)) -
      (center + γ * unitRay (orientedPhase forward θ)) =
      γ * (unitRay (orientedPhase forward η) - unitRay (orientedPhase forward θ)) by ring,
    norm_mul, oriented_pair_norm]

theorem rotated_pair_torque (center γ : ℂ) (forward : Bool) (θ η : ℝ) :
    (((center + γ * unitRay (orientedPhase forward η)) -
        (center + γ * unitRay (orientedPhase forward θ))) *
      star ((center + γ * unitRay (orientedPhase forward θ)) - center)).im =
      ‖γ‖ ^ 2 * orientationSign forward * Real.sin (η - θ) := by
  have he : ((center + γ * unitRay (orientedPhase forward η)) -
        (center + γ * unitRay (orientedPhase forward θ))) *
      star ((center + γ * unitRay (orientedPhase forward θ)) - center) =
      (γ * star γ) * ((unitRay (orientedPhase forward η) - unitRay (orientedPhase forward θ)) *
        star (unitRay (orientedPhase forward θ))) := by
    simp only [add_sub_cancel_left, star_mul]
    ring
  rw [he, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    Complex.im_ofReal_mul, ← Complex.star_def, oriented_pair_torque]
  ring

end CenteredCircle.AllN

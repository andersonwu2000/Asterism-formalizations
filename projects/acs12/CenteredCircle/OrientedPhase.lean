import CenteredCircle.PhysicalAngles
import CenteredCircle.GeometricNormalization

/-! Exact complex phase presentation through the constructed normalization. -/

namespace CenteredCircle.AllN

set_option backward.isDefEq.respectTransparency false

theorem unitRay_neg (θ : ℝ) : unitRay (-θ) = (unitRay θ)⁻¹ := by
  simp only [unitRay, Complex.ofReal_neg, neg_mul, Complex.exp_neg]

theorem unitRay_neg_congr {θ η : ℝ} (h : unitRay θ = unitRay η) : unitRay (-θ) = unitRay (-η) := by
  rw [unitRay_neg, unitRay_neg, h]

theorem unitRay_clockwise (r x : ℝ) :
    unitRay (clockwiseArc (2 * Real.pi) r x) = unitRay (x - r) := by
  unfold clockwiseArc
  split_ifs
  · rfl
  · exact unitRay_periodic _

theorem unitRay_reverseCircle (x : ℝ) :
    unitRay (reverseCircle (2 * Real.pi) x) = unitRay (-x) := by
  unfold reverseCircle
  split_ifs with h
  · simp [h]
  · rw [show 2 * Real.pi - x = -x + 2 * Real.pi by ring, unitRay_periodic]

noncomputable def orientedPhase (forward : Bool) (θ : ℝ) : ℝ := if forward then θ else -θ

theorem orientedPhase_involutive (forward : Bool) (θ : ℝ) :
    orientedPhase forward (orientedPhase forward θ) = θ := by
  cases forward <;> simp [orientedPhase]

theorem unitRay_orientedCircle (r x : ℝ) (forward : Bool) :
    unitRay (orientedCircle (2 * Real.pi) r forward x) =
      unitRay (orientedPhase forward (x - r)) := by
  cases forward
  · change unitRay (reverseCircle (2 * Real.pi) (clockwiseArc (2 * Real.pi) r x)) = unitRay (-(x-r))
    rw [unitRay_reverseCircle]
    exact unitRay_neg_congr (unitRay_clockwise r x)
  · exact unitRay_clockwise r x

theorem unitRay_phase_presentation (r x : ℝ) (forward : Bool) :
    unitRay x = unitRay r * unitRay (orientedPhase forward (orientedCircle (2 * Real.pi) r forward x)) := by
  have he : unitRay (orientedPhase forward (orientedCircle (2 * Real.pi) r forward x)) =
      unitRay (x - r) := by
    cases forward
    · have h := unitRay_neg_congr (unitRay_orientedCircle r x false)
      simpa only [orientedPhase, Bool.false_eq_true, if_false, neg_neg] using h
    · exact unitRay_orientedCircle r x true
  rw [he, ← unitRay_add]
  congr 1
  ring

namespace NormalizedCircleChart

variable {ι : Type*} [DecidableEq ι] {a m : ι → ℝ}
    (C : NormalizedCircleChart a m (2 * Real.pi))

theorem angular_scale : 2 * Real.pi / C.source.period = C.scale := by
  rw [C.period_eq]
  have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp

theorem phase_presentation (i : ι) :
    unitRay (a i) = unitRay (a C.source.root) *
      unitRay (orientedPhase C.forward (C.scale * C.source.coordinate i)) := by
  rw [C.coordinate_eq, mul_div_cancel₀ _ (ne_of_gt C.scale_pos)]
  exact unitRay_phase_presentation _ _ _

end NormalizedCircleChart

end CenteredCircle.AllN

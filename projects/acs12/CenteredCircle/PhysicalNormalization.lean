import CenteredCircle.PhasePairGeometry

/-! Phase differences in the normalized circular chart. -/

namespace CenteredCircle.AllN

open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace NormalizedCircleChart

variable {ι : Type*} [DecidableEq ι] {a m : ι → ℝ}
    (C : NormalizedCircleChart a m (2 * Real.pi))

theorem scale_mul_period : C.scale * C.source.period = 2 * Real.pi := by
  rw [C.period_eq]
  field_simp [ne_of_gt C.scale_pos]

theorem kernel_angle (t : ℝ) : 2 * Real.pi * t / C.source.period = C.scale * t := by
  rw [show 2 * Real.pi * t / C.source.period =
    (2 * Real.pi / C.source.period) * t by ring, C.angular_scale]

theorem root_pair_phase (j : ι) :
    unitRay (C.scale * C.source.coordinate j - C.scale * C.source.coordinate C.source.root) =
      unitRay (2 * Real.pi * C.source.coordinate j / C.source.period) := by
  rw [C.source.coordinate_root, mul_zero, sub_zero, C.kernel_angle]

theorem neighbor_pair_phase (j : ι) :
    unitRay (C.scale * C.source.coordinate j - C.scale * C.source.coordinate C.source.neighbor) =
      unitRay (2 * Real.pi * C.source.rightDistance j / C.source.period) := by
  rw [C.source.coordinate_neighbor, mul_one, C.kernel_angle]
  unfold AnchoredCircleSource.rightDistance
  split_ifs
  · rw [show C.scale * (C.source.coordinate j + C.source.period - 1) =
      (C.scale * C.source.coordinate j - C.scale) + 2 * Real.pi by
        nlinarith [C.scale_mul_period], unitRay_periodic]
  · congr 1
    ring

end NormalizedCircleChart

end CenteredCircle.AllN

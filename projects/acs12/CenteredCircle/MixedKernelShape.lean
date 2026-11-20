import CenteredCircle.MixedMoments
import Mathlib.Analysis.Convex.Deriv

/-! Shape of the actual mixed kernels on their exact sampled domains. -/

namespace CenteredCircle.AllN

open Set Filter
open scoped Topology

noncomputable def mixedLeftKernel (L : ℝ) : ℝ → ℝ := leftMixedMoment L 0
noncomputable def mixedRightKernel (L : ℝ) : ℝ → ℝ := rightMixedMoment L 0

theorem mixedLeftKernel_formula {L : ℝ} (hL : 0 < L) (t : ℝ) :
    mixedLeftKernel L t = circleKernel L .a t - circleKernel L .b t / 4 := by
  simp only [mixedLeftKernel, leftMixedMoment, kernelMoment_zero hL]

theorem mixedRightKernel_formula {L : ℝ} (hL : 0 < L) (t : ℝ) :
    mixedRightKernel L t = circleKernel L .b t - circleKernel L .a t / 4 := by
  simp only [mixedRightKernel, rightMixedMoment, kernelMoment_zero hL]

theorem mixedLeftKernel_pos {L t : ℝ} (hL : 0 < L) (ht : 1 ≤ t) :
    0 < mixedLeftKernel L t := leftMixedMoment_pos hL ht 0 (by norm_num)

theorem mixedRightKernel_pos {L t : ℝ} (hL : 0 < L) (ht : 0 < t) :
    0 < mixedRightKernel L t := rightMixedMoment_pos hL ht 0

theorem mixedLeftKernel_continuousOn {L : ℝ} (hL : 0 < L) :
    ContinuousOn (mixedLeftKernel L) (Ici 1) := by
  intro t ht
  change 1 ≤ t at ht
  exact (hasDerivAt_leftMixedMoment hL (by linarith : 0 < t) 0).continuousAt.continuousWithinAt

theorem mixedRightKernel_continuousOn {L : ℝ} (hL : 0 < L) :
    ContinuousOn (mixedRightKernel L) (Ioi 0) := by
  intro t ht
  exact (hasDerivAt_rightMixedMoment hL ht 0).continuousAt.continuousWithinAt

theorem strictAntiOn_mixedLeftKernel {L : ℝ} (hL : 0 < L) :
    StrictAntiOn (mixedLeftKernel L) (Ici 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 1) (mixedLeftKernel_continuousOn hL)
  intro t ht
  have ht1 : 1 ≤ t := interior_subset ht
  have htp : 0 < t := by linarith
  change deriv (leftMixedMoment L 0) t < 0
  rw [(hasDerivAt_leftMixedMoment hL htp 0).deriv]
  exact neg_neg_of_pos (leftMixedMoment_pos hL ht1 1 (by norm_num))

theorem strictAntiOn_mixedRightKernel {L : ℝ} (hL : 0 < L) :
    StrictAntiOn (mixedRightKernel L) (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0) (mixedRightKernel_continuousOn hL)
  intro t ht
  have htp : 0 < t := by simpa using ht
  change deriv (rightMixedMoment L 0) t < 0
  rw [(hasDerivAt_rightMixedMoment hL htp 0).deriv]
  exact neg_neg_of_pos (rightMixedMoment_pos hL htp 1)

theorem hasDerivAt_deriv_mixedLeftKernel {L t : ℝ} (hL : 0 < L) (ht : 0 < t) :
    HasDerivAt (deriv (mixedLeftKernel L)) (leftMixedMoment L 2 t) t := by
  have he : deriv (mixedLeftKernel L) =ᶠ[𝓝 t] fun x => -leftMixedMoment L 1 x := by
    filter_upwards [Ioi_mem_nhds ht] with x hx
    exact (hasDerivAt_leftMixedMoment hL hx 0).deriv
  have hd := (hasDerivAt_leftMixedMoment hL ht 1).neg
  simpa only [neg_neg, Nat.reduceAdd] using hd.congr_of_eventuallyEq he

theorem hasDerivAt_deriv_mixedRightKernel {L t : ℝ} (hL : 0 < L) (ht : 0 < t) :
    HasDerivAt (deriv (mixedRightKernel L)) (rightMixedMoment L 2 t) t := by
  have he : deriv (mixedRightKernel L) =ᶠ[𝓝 t] fun x => -rightMixedMoment L 1 x := by
    filter_upwards [Ioi_mem_nhds ht] with x hx
    exact (hasDerivAt_rightMixedMoment hL hx 0).deriv
  have hd := (hasDerivAt_rightMixedMoment hL ht 1).neg
  simpa only [neg_neg, Nat.reduceAdd] using hd.congr_of_eventuallyEq he

theorem strictConvexOn_mixedLeftKernel {L : ℝ} (hL : 0 < L) :
    StrictConvexOn ℝ (Ici 1) (mixedLeftKernel L) := by
  apply strictConvexOn_of_deriv2_pos' (convex_Ici 1) (mixedLeftKernel_continuousOn hL)
  intro t ht
  change 1 ≤ t at ht
  change 0 < deriv (deriv (mixedLeftKernel L)) t
  rw [(hasDerivAt_deriv_mixedLeftKernel hL (by linarith : 0 < t)).deriv]
  exact leftMixedMoment_pos hL ht 2 (by norm_num)

theorem strictConvexOn_mixedRightKernel {L : ℝ} (hL : 0 < L) :
    StrictConvexOn ℝ (Ioi 0) (mixedRightKernel L) := by
  apply strictConvexOn_of_deriv2_pos' (convex_Ioi 0) (mixedRightKernel_continuousOn hL)
  intro t ht
  change 0 < deriv (deriv (mixedRightKernel L)) t
  rw [(hasDerivAt_deriv_mixedRightKernel hL ht).deriv]
  exact rightMixedMoment_pos hL ht 2

theorem mixedLeftKernel_le_cubic {L t : ℝ} (hL : 0 < L) (ht : 0 < t) :
    mixedLeftKernel L t ≤ 1 / t ^ 3 := by
  rw [mixedLeftKernel_formula hL]
  have hp := circleKernel_pos hL .b t ht
  have hb := circleKernel_le_cubic hL .a t ht
  linarith

theorem mixedRightKernel_le_cubic {L t : ℝ} (hL : 0 < L) (ht : 0 < t) :
    mixedRightKernel L t ≤ 1 / t ^ 3 := by
  rw [mixedRightKernel_formula hL]
  have hp := circleKernel_pos hL .a t ht
  have hb := circleKernel_le_cubic hL .b t ht
  linarith

theorem mixedLeftKernel_summable {L t s : ℝ} (hL : 0 < L) (ht : 0 < t) (hs : 0 < s) :
    Summable (fun j : ℕ => mixedLeftKernel L (t + j * s)) := by
  simpa only [mixedLeftKernel_formula hL] using
    (circleKernel_summable hL .a t s ht hs).sub ((circleKernel_summable hL .b t s ht hs).div_const 4)

theorem mixedRightKernel_summable {L t s : ℝ} (hL : 0 < L) (ht : 0 < t) (hs : 0 < s) :
    Summable (fun j : ℕ => mixedRightKernel L (t + j * s)) := by
  simpa only [mixedRightKernel_formula hL] using
    (circleKernel_summable hL .b t s ht hs).sub ((circleKernel_summable hL .a t s ht hs).div_const 4)

end CenteredCircle.AllN

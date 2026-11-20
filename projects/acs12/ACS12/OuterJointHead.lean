import ACS12.OuterJointKernel
import ACS12.JointPureSource

/-! Complete A-head comparison after the fourth-root lower bound. -/
namespace ACS12.GammaMeasure
open CenteredCircle.AllN MeasureTheory Set Filter
set_option maxHeartbeats 1000000

theorem outer_joint_head_lt {p L θ u m r : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9/5)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hu : 0 < u) (hm : 0 < m) (hmu : m < u)
    (hr₀ : 0 < 2*m-u) (hr : 2*m-u ≤ r) :
    samplingHead (lawPeanoKernel p L θ u .a) u u <
      samplingHead (lawPeanoKernel p L θ u .a) m r := by
  have hp₂ : p ≤ 2 := hP.trans (by norm_num)
  have hrP : 0 < r := hr₀.trans_le hr
  obtain ⟨hU,hUE⟩ := lawPeanoHead_sampling hp hp₂ hL hθ hu hu hu .a
  obtain ⟨hR,hRE⟩ := lawPeanoHead_sampling hp hp₂ hL hθ hu hm hrP .a
  letI : NeZero (volume.restrict (Ioi (0:ℝ))) := ⟨positiveHalfLine_ne_zero⟩
  rw [hUE,hRE]
  apply integral_strict_of_ae_lt (volume.restrict (Ioi (0:ℝ))) hU hR
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs₀ : 0 < s := hs
  have hCenter := pureHead_centered_density_lt hs₀ hmu hr₀
  have hTail := (scaledExpTail_secant hs₀ hr₀ hr).2
  have hC := (BoseShape.C_lt_one (mul_pos hs₀ hr₀)).le
  have hScale := mul_le_mul_of_nonneg_left hC (sub_nonneg.mpr hr)
  have hMono : (2*m-u)+scaledExpTail s (2*m-u) ≤ r+scaledExpTail s r := by
    nlinarith only [hTail,hScale]
  have hMove := mul_le_mul_of_nonneg_left hMono (Real.exp_pos (-s*m)).le
  have hRaw := hCenter.trans_le hMove
  have h := mul_lt_mul_of_pos_left hRaw (lawPeanoDensity_pos (zero_lt_one.trans_le hp) hL hθ hu hs₀ .a)
  simpa only [mul_assoc] using h

end ACS12.GammaMeasure

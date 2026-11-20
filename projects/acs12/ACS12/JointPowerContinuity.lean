import ACS12.NativeJointBoseLaw

/-! The actual joint power row is continuous at its zero-count end under its proved moment bound. -/
namespace ACS12.NativeCells
open Set MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

noncomputable def jointPowerRow (p q z : ℝ) : ℝ :=
  ∫ s, nativeJointEnergy z s^q ∂nativeJointMeasure p

theorem jointPowerRow_zero_continuous {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) :
    ContinuousWithinAt (jointPowerRow p q) (Ici 0) 0 := by
  have hMeas (z : ℝ) : AEStronglyMeasurable
      (fun s => nativeJointEnergy z s^q) (nativeJointMeasure p) :=
    ((measurable_nativeJointEnergy z).pow_const q).aestronglyMeasurable
  have hInt := nativeJoint_all_positive_moments (z:=1) hp (by norm_num) hq
  have hLt : ∀ᶠ z : ℝ in 𝓝[Ici 0] 0, z < 1 :=
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  refine continuousWithinAt_of_dominated (Eventually.of_forall hMeas) ?_ hInt ?_
  · filter_upwards [self_mem_nhdsWithin,hLt] with z hz hz₁
    filter_upwards [nativeJoint_coordinates_ae_pos hp] with s hs
    have hz₀ : 0 ≤ z := hz
    have hE : 0 < nativeJointEnergy z s := by
      unfold nativeJointEnergy
      exact add_pos_of_pos_of_nonneg hs.1 (mul_nonneg hz₀ hs.2.le)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hE.le q)]
    apply Real.rpow_le_rpow hE.le _ hq
    unfold nativeJointEnergy
    nlinarith only [hz₁,hs.2]
  · filter_upwards [nativeJoint_coordinates_ae_pos hp] with s hs
    have hBase : Continuous (fun z : ℝ => nativeJointEnergy z s) := by
      unfold nativeJointEnergy
      fun_prop
    apply (hBase.continuousAt.rpow_const (Or.inl ?_)).continuousWithinAt
    simpa only [nativeJointEnergy,zero_mul,add_zero] using hs.1.ne'

end ACS12.NativeCells

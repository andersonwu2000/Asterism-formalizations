import ACS12.JointNativeTiltCore

/-! Bounded joint fractions pay every fixed count derivative by the same complete positive moment. -/
namespace ACS12.NativeCells
open MeasureTheory Filter
set_option backward.isDefEq.respectTransparency false

noncomputable def jointWeightedPower (β : ℝ) (j : ℕ) (z : ℝ) (s : NativeJointSample) : ℝ :=
  (boseNoise s.2)^j*nativeJointEnergy z s^(β-(j:ℝ))
noncomputable def jointWeightedPowerRow (p β : ℝ) (j : ℕ) (z : ℝ) : ℝ :=
  ∫ s, jointWeightedPower β j z s ∂nativeJointMeasure p

theorem measurable_jointWeightedPower (β : ℝ) (j : ℕ) (z : ℝ) :
    Measurable (jointWeightedPower β j z) :=
  ((measurable_boseNoise.comp measurable_snd).pow_const j).mul
    ((measurable_nativeJointEnergy z).pow_const _)

theorem jointWeightedPower_ratio {β z : ℝ} (j : ℕ) (s : NativeJointSample)
    (hY : 0 < nativeJointEnergy z s) :
    jointWeightedPower β j z s =
      (boseNoise s.2/nativeJointEnergy z s)^j*nativeJointEnergy z s^β := by
  unfold jointWeightedPower
  rw [Real.rpow_sub hY,Real.rpow_natCast,div_pow]
  ring

theorem jointWeightedPower_bound {β a b z : ℝ} (hβ : 0 ≤ β) (ha : 0 < a)
    (haz : a ≤ z) (hzb : z ≤ b) (j : ℕ) (s : NativeJointSample)
    (hs : 0 < GammaMixture.gammaTotal s.1 ∧ 0 < boseNoise s.2) :
    jointWeightedPower β j z s ≤ (1/a)^j*nativeJointEnergy b s^β := by
  have hz : 0 < z := ha.trans_le haz
  have hb : 0 < b := hz.trans_le hzb
  have hY : 0 < nativeJointEnergy z s :=
    add_pos_of_pos_of_nonneg hs.1 (mul_nonneg hz.le hs.2.le)
  have hRatio : boseNoise s.2/nativeJointEnergy z s ≤ 1/a := by
    apply (div_le_iff₀ hY).mpr
    rw [show (1/a)*nativeJointEnergy z s = nativeJointEnergy z s/a by ring]
    apply (le_div_iff₀ ha).mpr
    change boseNoise s.2*a ≤ nativeJointEnergy z s
    unfold nativeJointEnergy
    nlinarith only [mul_le_mul_of_nonneg_right haz hs.2.le,hs.1]
  have hYB : nativeJointEnergy z s ≤ nativeJointEnergy b s := by
    unfold nativeJointEnergy
    nlinarith only [mul_le_mul_of_nonneg_right hzb hs.2.le]
  rw [jointWeightedPower_ratio j s hY]
  exact mul_le_mul
    (pow_le_pow_left₀ (div_nonneg hs.2.le hY.le) hRatio j)
    (Real.rpow_le_rpow hY.le hYB hβ) (Real.rpow_nonneg hY.le _)
    (pow_nonneg (by positivity) _)

theorem jointWeightedPower_integrable {p β z : ℝ} (hp : 0 < p) (hβ : 0 ≤ β)
    (hz : 0 < z) (j : ℕ) :
    Integrable (jointWeightedPower β j z) (nativeJointMeasure p) := by
  have hI := (nativeJoint_all_positive_moments (q:=β) hp hz.le hβ).const_mul ((1/z)^j)
  apply hI.mono' (measurable_jointWeightedPower β j z).aestronglyMeasurable
  filter_upwards [nativeJoint_coordinates_ae_pos hp] with s hs
  have hY : 0 < nativeJointEnergy z s :=
    add_pos_of_pos_of_nonneg hs.1 (mul_nonneg hz.le hs.2.le)
  have hNon : 0 ≤ jointWeightedPower β j z s :=
    mul_nonneg (pow_nonneg hs.2.le j) (Real.rpow_nonneg hY.le _)
  rw [Real.norm_of_nonneg hNon]
  exact jointWeightedPower_bound hβ hz le_rfl le_rfl j s hs

end ACS12.NativeCells

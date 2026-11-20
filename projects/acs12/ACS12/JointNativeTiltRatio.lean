import ACS12.JointNativeTiltCore

/-! Exact raw row ratios under the same fixed-in-count joint tilt. -/
namespace ACS12.NativeCells
open MeasureTheory Set Filter
set_option backward.isDefEq.respectTransparency false

theorem jointNativeTilt_ratio {p z t : ℝ} (hp : 0 < p) (hz : 0 < z) (ht : 0 < t) :
    (∫ s, (1+jointNativeVariable z s*(t^2-1))^((p-2)/2) ∂jointNativeTilt p z) =
      jointPowerRow p ((p-2)/2) (z*t^2)/jointPowerRow p ((p-2)/2) z := by
  let h := (p-2)/2
  let μ := nativeJointMeasure p
  let f := jointNativeTiltWeight p z
  let g (s : NativeJointSample) := h*Real.log (1+jointNativeVariable z s*(t^2-1))
  have hE (s : NativeJointSample) (hs : 0 < GammaMixture.gammaTotal s.1 ∧ 0 < boseNoise s.2) :
      1+jointNativeVariable z s*(t^2-1) =
        nativeJointEnergy (z*t^2) s/nativeJointEnergy z s := by
    have hY : 0 < nativeJointEnergy z s :=
      add_pos_of_pos_of_nonneg hs.1 (mul_nonneg hz.le hs.2.le)
    dsimp only [nativeJointEnergy] at hY
    unfold jointNativeVariable nativeJointEnergy
    field_simp [hY.ne']
    <;> ring
  have hP (s : NativeJointSample) (hs : 0 < GammaMixture.gammaTotal s.1 ∧ 0 < boseNoise s.2) :
      0 < 1+jointNativeVariable z s*(t^2-1) := by
    rw [hE s hs]
    exact div_pos (add_pos_of_pos_of_nonneg hs.1 (mul_nonneg (mul_nonneg hz.le (sq_nonneg t)) hs.2.le))
      (add_pos_of_pos_of_nonneg hs.1 (mul_nonneg hz.le hs.2.le))
  have hG : (fun s => (1+jointNativeVariable z s*(t^2-1))^h) =ᵐ[jointNativeTilt p z]
      (fun s => Real.exp (g s)) := by
    filter_upwards [jointNativeTilt_coordinates_ae_pos (z:=z) hp] with s hs
    rw [Real.rpow_def_of_pos (hP s hs)]
    dsimp only [g]
    congr 1
    ring
  have hFG : (fun s => Real.exp ((f+g) s)) =ᵐ[μ]
      (fun s => nativeJointEnergy (z*t^2) s^h) := by
    filter_upwards [nativeJoint_coordinates_ae_pos hp] with s hs
    have hY : 0 < nativeJointEnergy z s :=
      add_pos_of_pos_of_nonneg hs.1 (mul_nonneg hz.le hs.2.le)
    have hZ : 0 < nativeJointEnergy (z*t^2) s :=
      add_pos_of_pos_of_nonneg hs.1 (mul_nonneg (mul_nonneg hz.le (sq_nonneg t)) hs.2.le)
    simp only [Pi.add_apply,f,jointNativeTiltWeight,g,hE s hs,Real.log_div hZ.ne' hY.ne']
    rw [Real.rpow_def_of_pos hZ]
    dsimp only [h]
    congr 1
    ring
  change (∫ s, (1+jointNativeVariable z s*(t^2-1))^h ∂jointNativeTilt p z) = _
  rw [integral_congr_ae hG,jointNativeTilt,integral_exp_tilted f g,integral_congr_ae hFG,
    integral_congr_ae (jointNativeTilt_exp_eq hp hz.le)]
  rfl

theorem boseRow_pos_joint {p N : ℝ} (hp : 0 < p) (hN : 0 < N) : 0 < boseRow p N := by
  rw [boseRow_joint_all hp hN]
  exact mul_pos (mul_pos (sq_pos_of_pos hN) (nativeJointScale_pos hp))
    (jointPowerRow_pos hp (sq_nonneg N))

theorem boseRow_joint_tilt_ratio {p n t : ℝ} (hp : 0 < p) (hn : 0 < n) (ht : 0 < t) :
    boseRow p (n*t)/boseRow p n =
      t^2*∫ s, (1+jointNativeVariable (n^2) s*(t^2-1))^((p-2)/2) ∂jointNativeTilt p (n^2) := by
  have hC := nativeJointScale_pos hp
  have hn₂ := sq_pos_of_pos hn
  have hF := jointPowerRow_pos (q:=(p-2)/2) hp hn₂.le
  rw [boseRow_joint_all hp (mul_pos hn ht),boseRow_joint_all hp hn,
    jointNativeTilt_ratio hp hn₂ ht,mul_pow]
  change (n^2*t^2*nativeJointScale p*jointPowerRow p ((p-2)/2) (n^2*t^2))/
    (n^2*nativeJointScale p*jointPowerRow p ((p-2)/2) (n^2)) = _
  field_simp [hC.ne',hn₂.ne',hF.ne']
  <;> ring

end ACS12.NativeCells

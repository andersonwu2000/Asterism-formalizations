import ACS12.JointWeightedPowerBounds

/-! All fixed count derivatives of the actual joint law use the same locally bounded fraction and positive moment. -/
namespace ACS12.NativeCells
open MeasureTheory Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

theorem jointWeightedPower_hasDerivAt {β z : ℝ} (j : ℕ) (hz : 0 < z) (s : NativeJointSample)
    (hs : 0 < GammaMixture.gammaTotal s.1 ∧ 0 < boseNoise s.2) :
    HasDerivAt (fun x => jointWeightedPower β j x s)
      ((β-(j:ℝ))*jointWeightedPower β (j+1) z s) z := by
  have hY : 0 < nativeJointEnergy z s :=
    add_pos_of_pos_of_nonneg hs.1 (mul_nonneg hz.le hs.2.le)
  have hBase := ((hasDerivAt_id z).mul_const (boseNoise s.2)).const_add (GammaMixture.gammaTotal s.1)
  have hPow := (hBase.rpow_const (p:=β-(j:ℝ)) (Or.inl hY.ne')).const_mul ((boseNoise s.2)^j)
  convert hPow using 1
  have hExp : β-((j+1:ℕ):ℝ) = β-(j:ℝ)-1 := by push_cast; ring
  simp only [jointWeightedPower,nativeJointEnergy,id_eq,hExp,pow_succ]
  ring

theorem jointWeightedPower_deriv_bound {β a b z : ℝ} (hβ : 0 ≤ β) (ha : 0 < a)
    (haz : a ≤ z) (hzb : z ≤ b) (j : ℕ) (s : NativeJointSample)
    (hs : 0 < GammaMixture.gammaTotal s.1 ∧ 0 < boseNoise s.2) :
    ‖(β-(j:ℝ))*jointWeightedPower β (j+1) z s‖ ≤
      (|β-(j:ℝ)| *(1/a)^(j+1))*nativeJointEnergy b s^β := by
  have hz : 0 < z := ha.trans_le haz
  have hY : 0 < nativeJointEnergy z s :=
    add_pos_of_pos_of_nonneg hs.1 (mul_nonneg hz.le hs.2.le)
  have hNon : 0 ≤ jointWeightedPower β (j+1) z s :=
    mul_nonneg (pow_nonneg hs.2.le _) (Real.rpow_nonneg hY.le _)
  rw [norm_mul,Real.norm_eq_abs,Real.norm_of_nonneg hNon]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (jointWeightedPower_bound hβ ha haz hzb (j+1) s hs) (abs_nonneg (β-(j:ℝ)))

theorem jointWeightedPowerRow_calculus {p β z : ℝ} (hp : 0 < p) (hβ : 0 ≤ β)
    (hz : 0 < z) (j : ℕ) :
    HasDerivAt (jointWeightedPowerRow p β j)
      ((β-(j:ℝ))*jointWeightedPowerRow p β (j+1) z) z := by
  let J := Ioo (z/2) (2*z)
  let D (x : ℝ) (s : NativeJointSample) := (β-(j:ℝ))*jointWeightedPower β (j+1) x s
  let G (s : NativeJointSample) :=
    (|β-(j:ℝ)| *(1/(z/2))^(j+1))*nativeJointEnergy (2*z) s^β
  have hJ : J ∈ 𝓝 z := Ioo_mem_nhds (by linarith only [hz]) (by linarith only [hz])
  have hMeas (x : ℝ) : AEStronglyMeasurable (jointWeightedPower β j x) (nativeJointMeasure p) :=
    (measurable_jointWeightedPower β j x).aestronglyMeasurable
  have hDMeas : AEStronglyMeasurable (D z) (nativeJointMeasure p) :=
    ((measurable_jointWeightedPower β (j+1) z).const_mul _).aestronglyMeasurable
  have hG : Integrable G (nativeJointMeasure p) :=
    (nativeJoint_all_positive_moments hp (by linarith only [hz] : 0 ≤ 2*z) hβ).const_mul _
  have hBound : ∀ᵐ s ∂nativeJointMeasure p, ∀ x ∈ J, ‖D x s‖ ≤ G s := by
    filter_upwards [nativeJoint_coordinates_ae_pos hp] with s hs
    intro x hx
    exact jointWeightedPower_deriv_bound hβ (half_pos hz) hx.1.le hx.2.le j s hs
  have hDiff : ∀ᵐ s ∂nativeJointMeasure p, ∀ x ∈ J,
      HasDerivAt (fun x => jointWeightedPower β j x s) (D x s) x := by
    filter_upwards [nativeJoint_coordinates_ae_pos hp] with s hs
    intro x hx
    exact jointWeightedPower_hasDerivAt j ((half_pos hz).trans hx.1) s hs
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hJ
    (Eventually.of_forall hMeas) (jointWeightedPower_integrable hp hβ hz j)
    hDMeas hBound hG hDiff).2
  change HasDerivAt (fun x => ∫ s, jointWeightedPower β j x s ∂nativeJointMeasure p)
    ((β-(j:ℝ))*(∫ s, jointWeightedPower β (j+1) z s ∂nativeJointMeasure p)) z
  rw [←integral_const_mul]
  exact h

theorem jointPowerRow_hasDerivAt {p β z : ℝ} (hp : 0 < p) (hβ : 0 ≤ β) (hz : 0 < z) :
    HasDerivAt (jointPowerRow p β) (β*jointWeightedPowerRow p β 1 z) z := by
  have hEq : jointWeightedPowerRow p β 0 = jointPowerRow p β := by
    funext x
    simp only [jointWeightedPowerRow,jointPowerRow,jointWeightedPower,Nat.cast_zero,sub_zero,pow_zero,one_mul]
  simpa only [hEq,Nat.cast_zero,sub_zero,Nat.zero_add] using jointWeightedPowerRow_calculus hp hβ hz 0

end ACS12.NativeCells

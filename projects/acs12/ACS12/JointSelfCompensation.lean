import ACS12.ProfileSelfCalculus
import ACS12.NativeSelfCore

/-! The quantitative literal-SELF tangent for the actual common power profile. -/
namespace ACS12.NativeCells
open Set Filter MeasureTheory
open scoped Topology
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem nativeSelfCorrection_quantitative {p n x : ℝ} (hp : 2≤p) (hp₄ : p≤4)
    (hn : 1<n) (hx : 1<x) (hxn : x≠n) :
    nativeSelfCorrection p x+n^3*deriv (nativeSelfCorrection p) n/(2*x^2)<
      nativeSelfCorrection p n+n*deriv (nativeSelfCorrection p) n/2 := by
  let β:=(p-2)/2
  let F:=jointPowerRow p β
  let F₁ (z : ℝ):=β*jointWeightedPowerRow p β 1 z
  let F₂ (z : ℝ):=β*(β-1)*jointWeightedPowerRow p β 2 z
  let c:=nativeJointScale p
  let d:=boseRow p 1
  have hp₀ : 0<p:=by linarith only [hp]
  have hβ : 0≤β:=by unfold β;linarith only [hp]
  have hβ₁ : β≤1:=by unfold β;linarith only [hp₄]
  have hc : 0<c:=nativeJointScale_pos hp₀
  have hd : 0<d:=boseRow_pos_joint hp₀ zero_lt_one
  have hW (j : ℕ) (z : ℝ) (hz : 0<z) : 0≤jointWeightedPowerRow p β j z:=by
    apply integral_nonneg_of_ae
    filter_upwards [nativeJoint_coordinates_ae_pos hp₀] with s hs
    unfold jointWeightedPower
    exact mul_nonneg (pow_nonneg hs.2.le j)
      (Real.rpow_nonneg (add_nonneg hs.1.le (mul_nonneg hz.le hs.2.le)) _)
  have hD (z : ℝ) (hz : 0<z) : HasDerivAt F (F₁ z) z:=
    jointPowerRow_hasDerivAt hp₀ hβ hz
  have hD₁ (z : ℝ) (hz : 0<z) : HasDerivAt F₁ (F₂ z) z:=by
    have h:=(jointWeightedPowerRow_calculus hp₀ hβ hz 1).const_mul β
    convert h using 1
    simp only [F₂,Nat.cast_one]
    ring
  have hf (z : ℝ) (hz : 0<z) : 0<F z:=jointPowerRow_pos hp₀ hz.le
  have hf₁ (z : ℝ) (hz : 0<z) : 0≤F₁ z:=mul_nonneg hβ (hW 1 z hz)
  have hf₂ (z : ℝ) (hz : 0<z) : F₂ z≤0:=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hβ (sub_nonpos.mpr hβ₁)) (hW 2 z hz)
  have hV (N : ℝ) (hN : 0<N) : ACS12.inverseSquareProfile c F N=
      Real.exp (-Real.log (boseRow p N)):=by
    rw [Real.exp_neg,Real.exp_log (boseRow_pos_joint hp₀ hN),boseRow_joint_all hp₀ hN]
    unfold ACS12.inverseSquareProfile c F β jointPowerRow
    ring
  have hDom (N : ℝ) (hN : 1<N) : 0<1-d*ACS12.inverseSquareProfile c F N:=by
    rw [hV N (zero_lt_one.trans hN)]
    exact nativeSelfArgument_pos hp hN
  have hEq (N : ℝ) (hN : 1<N) : ACS12.profileSelf c d F N=nativeSelfCorrection p N:=by
    unfold ACS12.profileSelf nativeSelfCorrection
    rw [hV N (zero_lt_one.trans hN)]
  have hQuant:=ACS12.profileSelf_weightedTangent hc hd hD hD₁ hf hf₁ hf₂ hDom hn hx hxn
  have hPD:=ACS12.profileSelf_hasDerivAt hc.ne' (zero_lt_one.trans hn).ne'
    (hf _ (sq_pos_of_pos (zero_lt_one.trans hn))).ne'
    (hD _ (sq_pos_of_pos (zero_lt_one.trans hn))) (hDom n hn)
  have hE : nativeSelfCorrection p=ᶠ[𝓝 n] ACS12.profileSelf c d F:=by
    filter_upwards [Ioi_mem_nhds hn] with N hN
    exact (hEq N hN).symm
  have hSlope:=(hPD.congr_of_eventuallyEq hE).deriv
  rw [hEq x hx,hEq n hn,←hSlope] at hQuant
  exact hQuant

end ACS12.NativeCells

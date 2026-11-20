import ACS12.JointNativeRawSlope

/-! Exact literal SELF identities and the full row elasticity on the closed band. -/
namespace ACS12.NativeCells
open Set Filter
open scoped Topology
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

noncomputable def nativeSelfCorrection (p N : ℝ) : ℝ :=
  Real.log (1 - boseRow p 1 * Real.exp (-Real.log (boseRow p N)))

theorem nativeSelfArgument_pos {p N : ℝ} (hp : 2 ≤ p) (hN : 1 < N) :
    0 < 1 - boseRow p 1 * Real.exp (-Real.log (boseRow p N)) := by
  have hp₀ : 0 < p := by linarith only [hp]
  have hU := boseRow_pos_joint (by linarith only [hp]) (zero_lt_one.trans hN)
  have hS := analyticRow_pos hp₀ hN
  rw [← boseRow_sub_self hp₀ hN] at hS
  rw [Real.exp_neg,Real.exp_log hU,← div_eq_mul_inv]
  exact sub_pos.mpr ((div_lt_one hU).mpr (sub_pos.mp hS))

theorem nativeSelfCorrection_hasDerivAt {p N : ℝ} (hp : 2 ≤ p) (hN : 1 < N) :
    HasDerivAt (nativeSelfCorrection p) (deriv (nativeSelfCorrection p) N) N := by
  have h := (boseRow_joint_log_hasDerivAt hp (zero_lt_one.trans hN)).neg.exp
  have hQ := ((h.const_mul (boseRow p 1)).const_sub 1).log
    (nativeSelfArgument_pos hp hN).ne'
  exact hQ.differentiableAt.hasDerivAt

theorem analyticRow_self_log_eq {p N : ℝ} (hp : 2 ≤ p) (hN : 1 < N) :
    Real.log (analyticRow p N) = Real.log (boseRow p N) + nativeSelfCorrection p N := by
  have hp₀ : 0 < p := by linarith only [hp]
  have hU := boseRow_pos_joint (by linarith only [hp]) (zero_lt_one.trans hN)
  have hR := nativeSelfArgument_pos hp hN
  unfold nativeSelfCorrection
  rw [← Real.log_mul hU.ne' hR.ne']
  congr 1
  rw [← boseRow_sub_self hp₀ hN,Real.exp_neg,Real.exp_log hU,mul_sub,mul_one]
  field_simp [hU.ne']


theorem nativeSelfCorrection_slope {p N : ℝ} (hp : 2≤p) (hN : 1<N) :
    let δ:=boseRow p 1/boseRow p N
    let e:=2+(p-2)*jointNativeMean p (N^2)
    N*deriv (nativeSelfCorrection p) N=δ*e/(1-δ) := by
  have hN₀:=zero_lt_one.trans hN
  have hU:=boseRow_pos_joint (by linarith only [hp]) hN₀
  have hArg:=nativeSelfArgument_pos hp hN
  have hLog:=boseRow_joint_log_hasDerivAt hp hN₀
  have hQ:=(((hLog.neg.exp).const_mul (boseRow p 1)).const_sub 1).log hArg.ne'
  have hD : 0<1-boseRow p 1/boseRow p N := by
    simpa only [Real.exp_neg,Real.exp_log hU,div_eq_mul_inv] using hArg
  dsimp only [Pi.neg_apply] at hQ
  dsimp only
  unfold nativeSelfCorrection
  rw [hQ.deriv,Real.exp_neg,Real.exp_log hU]
  field_simp [hN₀.ne',hU.ne',hD.ne']
  <;>ring

theorem analyticRow_self_elasticity {p N : ℝ} (hp : 2≤p) (hN : 1<N) :
    N*deriv (fun x=>Real.log (analyticRow p x)) N=
      (2+(p-2)*jointNativeMean p (N^2))/(1-boseRow p 1/boseRow p N) := by
  have hN₀:=zero_lt_one.trans hN
  have hQ:=nativeSelfCorrection_hasDerivAt hp hN
  have hD:=(boseRow_joint_log_hasDerivAt hp hN₀).add hQ
  have hEq : (fun x=>Real.log (analyticRow p x))=ᶠ[𝓝 N]
      ((fun x=>Real.log (boseRow p x))+nativeSelfCorrection p) := by
    filter_upwards [Ioi_mem_nhds hN] with x hx
    exact analyticRow_self_log_eq hp hx
  have hDeriv:=(hD.congr_of_eventuallyEq hEq).deriv
  rw [hDeriv]
  have hRaw:=boseRow_joint_rawElasticity hp hN₀
  have hSlope:=nativeSelfCorrection_slope hp hN
  dsimp only at hSlope
  have hU:=boseRow_pos_joint (by linarith only [hp]) hN₀
  have hArg:=nativeSelfArgument_pos hp hN
  have hDen : 0<1-boseRow p 1/boseRow p N:=by
    simpa only [Real.exp_neg,Real.exp_log hU,div_eq_mul_inv] using hArg
  rw [mul_add,hSlope]
  generalize hδ : boseRow p 1/boseRow p N=δ at hDen ⊢
  field_simp [hN₀.ne',hDen.ne']
  <;>ring

end ACS12.NativeCells

import ACS12.JointAnchorMeanReduction
import ACS12.JointSelfFraction
import ACS12.NativeRawDebit
import ACS12.JointSelfCompensation

/-! One complete literal-SELF/mean tangent for every real anchor above one. -/
namespace ACS12.NativeCells
open MeasureTheory Set Filter
open scoped Topology
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem analyticRow_elasticity_gt {p N : ℝ} (hp : 2≤p) (hp₄ : p≤4) (hN : 1<N) :
    2+(p-2)/2<N*deriv (fun x=>Real.log (analyticRow p x)) N := by
  let β:=(p-2)/2
  let x:=N^2
  let m:=jointNativeMean p x
  let δ:=boseRow p 1/boseRow p N
  have hp₀ : 0<p:=by linarith only [hp]
  have hN₁ : 1<N:=hN
  have hN₀:=zero_lt_one.trans hN₁
  have hβ : 0≤β:=by unfold β;linarith only [hp]
  have hβ₁ : β≤1:=by unfold β;linarith only [hp₄]
  have hx₀ : 0<x:=sq_pos_of_pos hN₀
  have hU:=boseRow_pos_joint hp₀ hN₀
  have hS:=analyticRow_pos hp₀ hN₁
  rw [←boseRow_sub_self hp₀ hN₁] at hS
  have hδ₁ : δ<1:=(div_lt_one hU).mpr (sub_pos.mp hS)
  have hm : 9*x/anchorElasticityDen β x≤m:=by
    exact (jointNativeMean_anchor_lower hp hp₄ hx₀).le
  have hδ : (5*β+6)/(x*anchorSelfDen β x)≤δ:=boseRow_self_fraction_lower hp hp₄ hN₁
  have h:=compensatedElasticity_lower hβ hβ₁ hx₀ hδ₁ hm hδ
  rw [analyticRow_self_elasticity hp hN₁]
  change 2+β<(2+(p-2)*m)/(1-δ)
  convert h using 1
  unfold β
  ring

theorem boseRow_joint_rawAdapted_debit {p n t : ℝ} (hp : 2 ≤ p) (hp₄ : p ≤ 4) (hn : 0 < n)
    (ht : 0 < t) :
    let h := (p-2)/2
    let H := t^2*((1+t^2)/2)^h;
    -h*max (1-2*jointNativeMean p (n^2)) 0*selfTangentShape t ≤ (n*deriv (fun x => Real.log (boseRow p x)) n-(2+h))*(t-1)-
      Real.log (boseRow p (n*t)/(boseRow p n*H)) := by
  let h := (p-2)/2
  let Y := jointNativeVariable (n^2)
  let μ := jointNativeTilt p (n^2)
  let U := ∫ s, (1+Y s*(t^2-1))^h ∂μ
  let B := (1+t^2)/2
  have hn₀ : 0 < n := by linarith only [hn]
  have hn₂ := sq_pos_of_pos hn₀
  have hh : 0 ≤ h := by unfold h; linarith only [hp]
  have hh₁ : h ≤ 1 := by unfold h; linarith only [hp₄]
  have hp₀ : 0 < p := by linarith only [hp]
  letI := jointNativeTilt_probability hp₀ hn₂.le
  have hY := (jointNativeVariable_ae_mem hp₀ hn₂).mono (fun _ hs => Ioo_subset_Icc_self hs)
  have hR := boseRow_joint_tilt_ratio hp₀ hn₀ ht
  change boseRow p (n*t)/boseRow p n = t^2*U at hR
  have hU : 0 < U := pos_of_mul_pos_right (hR ▸ div_pos
    (boseRow_pos_joint hp₀ (mul_pos hn₀ ht)) (boseRow_pos_joint hp₀ hn₀)) (sq_nonneg t)
  have hJ := adaptedAnchor_logTangent_debit (measurable_jointNativeVariable (n^2)) hY hh hh₁ ht hU
  have hL : boseRow p (n*t)/(boseRow p n*(t^2*B^h)) = U/B^h := by
    rw [←div_div,hR]
    field_simp [(sq_pos_of_pos ht).ne']
  change -h*max (1-2*jointNativeMean p (n^2)) 0*selfTangentShape t ≤ (n*deriv (fun x => Real.log (boseRow p x)) n-(2+h))*(t-1)-
    Real.log (boseRow p (n*t)/(boseRow p n*(t^2*B^h)))
  rw [boseRow_joint_rawElasticity hp hn₀,hL]
  change -h*max (1-2*jointNativeMean p (n^2)) 0*selfTangentShape t ≤ h*(2*jointNativeMean p (n^2)-1)*(t-1)-Real.log (U/B^h) at hJ
  have hE : p-2 = 2*h := by unfold h; ring
  rw [hE]
  nlinarith only [hJ]

theorem analyticRow_adapted_tangent {p n t : ℝ} (hp : 2≤p) (hp₄ : p≤4) (hn : 1<n)
    (ht : 1<n*t) (ht₁ : t≠1) :
    let h:=(p-2)/2
    let H:=t^2*((1+t^2)/2)^h
    0<(n*deriv (fun x=>Real.log (analyticRow p x)) n-(2+h))*(t-1)-
      Real.log (analyticRow p (n*t)/(analyticRow p n*H)) := by
  let β:=(p-2)/2
  let H:=t^2*((1+t^2)/2)^β
  let L (N : ℝ):=Real.log (boseRow p N)
  let Q:=nativeSelfCorrection p
  let m:=jointNativeMean p (n^2)
  let K:=max (1-2*m) 0
  have hn₁ : 1<n:=by linarith only [hn]
  have hn₀:=zero_lt_one.trans hn₁
  have ht₀ : 0<t:=pos_of_mul_pos_right (zero_lt_one.trans ht) hn₀.le
  have hH : 0<H:=by unfold H;positivity
  have hp₀ : 0<p:=by linarith only [hp]
  have hβ : 0≤β:=by unfold β;linarith only [hp]
  have hS₀:=analyticRow_pos hp₀ hn₁
  have hS₁:=analyticRow_pos hp₀ ht
  have hU₀:=boseRow_pos_joint hp₀ hn₀
  have hU₁:=boseRow_pos_joint hp₀ (zero_lt_one.trans ht)
  have hQ:=nativeSelfCorrection_hasDerivAt hp hn₁
  have hD:=(boseRow_joint_log_hasDerivAt hp hn₀).add hQ
  have hEq : (fun x=>Real.log (analyticRow p x))=ᶠ[𝓝 n] (L+Q):=by
    filter_upwards [Ioi_mem_nhds hn₁] with x hx
    exact analyticRow_self_log_eq hp hx
  have hDeriv : deriv (fun x=>Real.log (analyticRow p x)) n=deriv L n+deriv Q n:=by
    rw [(hD.congr_of_eventuallyEq hEq).deriv,(boseRow_joint_log_hasDerivAt hp hn₀).deriv]
  have hRawE:=boseRow_joint_rawElasticity hp hn₀
  change n*deriv L n=2+(p-2)*m at hRawE
  have hComp:=analyticRow_elasticity_gt hp hp₄ hn
  change 2+β<n*deriv (fun x=>Real.log (analyticRow p x)) n at hComp
  rw [hDeriv,mul_add,hRawE] at hComp
  have hE : p-2=2*β:=by unfold β;ring
  rw [hE] at hComp
  have hQLower : β*(1-2*m)≤n*deriv Q n:=by linarith only [hComp]
  have hδ : 0<boseRow p 1/boseRow p n:=div_pos (boseRow_pos_joint hp₀ zero_lt_one) hU₀
  have hArg:=nativeSelfArgument_pos hp hn₁
  have hδ₁ : 0<1-boseRow p 1/boseRow p n:=by
    simpa only [Real.exp_neg,Real.exp_log hU₀,div_eq_mul_inv] using hArg
  have hm₀:= (jointNativeMean_bounds hp₀ (sq_pos_of_pos hn₀)).1
  have he : 0<2+(p-2)*m:=by
    have hP:=mul_nonneg (sub_nonneg.mpr hp) hm₀
    linarith only [hP]
  have hQPos : 0<n*deriv Q n:=by
    rw [nativeSelfCorrection_slope hp hn₁]
    exact div_pos (mul_pos hδ he) hδ₁
  have hCoef : β*K≤n*deriv Q n:=by
    unfold K
    by_cases hM : 1-2*m≤0
    · rw [max_eq_right hM,mul_zero]
      exact hQPos.le
    · rw [max_eq_left (le_of_not_ge hM)]
      exact hQLower
  have hnt : n*t≠n:=by
    intro h
    exact ht₁ (mul_left_cancel₀ hn₀.ne' (h.trans (mul_one n).symm))
  have hQuant:=nativeSelfCorrection_quantitative hp hp₄ hn₁ ht hnt
  change Q (n*t)+n^3*deriv Q n/(2*(n*t)^2)<Q n+n*deriv Q n/2 at hQuant
  have hDiv : n^3*deriv Q n/(2*(n*t)^2)=n*deriv Q n/(2*t^2):=by
    field_simp [hn₀.ne',ht₀.ne']
    <;>ring
  rw [hDiv] at hQuant
  have hSelf : n*deriv Q n*selfTangentShape t<
      n*deriv Q n*(t-1)-(Q (n*t)-Q n):=by
    have hId : n*deriv Q n*(t-1)-(Q (n*t)-Q n)-n*deriv Q n*selfTangentShape t=
        (Q n+n*deriv Q n/2)-(Q (n*t)+n*deriv Q n/(2*t^2)):=by
      unfold selfTangentShape
      ring
    linarith only [hQuant,hId]
  have hPay:=mul_le_mul_of_nonneg_right hCoef (selfTangentShape_pos ht₀ ht₁).le
  have hRaw:=boseRow_joint_rawAdapted_debit hp hp₄ hn₀ ht₀
  change -β*K*selfTangentShape t≤(n*deriv L n-(2+β))*(t-1)-
    Real.log (boseRow p (n*t)/(boseRow p n*H)) at hRaw
  rw [Real.log_div hU₁.ne' (mul_pos hU₀ hH).ne',Real.log_mul hU₀.ne' hH.ne'] at hRaw
  change 0<(n*deriv (fun x=>Real.log (analyticRow p x)) n-(2+β))*(t-1)-
    Real.log (analyticRow p (n*t)/(analyticRow p n*H))
  rw [hDeriv,Real.log_div hS₁.ne' (mul_pos hS₀ hH).ne',Real.log_mul hS₀.ne' hH.ne',
    analyticRow_self_log_eq hp ht,analyticRow_self_log_eq hp hn₁]
  change 0<(n*(deriv L n+deriv Q n)-(2+β))*(t-1)-
    (L (n*t)+Q (n*t)-(L n+Q n+Real.log H))
  nlinarith only [hRaw,hSelf,hPay]

end ACS12.NativeCells

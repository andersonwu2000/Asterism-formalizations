import ACS12.GammaProductSecondMoment
import ACS12.MomentInterpolation
import ACS12.BoseMeanReduction
import ACS12.CompensatedElasticityScalar

/-! Fractional interpolation of the complete literal-SELF variable X+chi. -/
namespace ACS12.NativeCells
open MeasureTheory ProbabilityTheory Set Filter
open GammaMixture (gammaProduct gammaTotal)
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem nativeJointEnergy_one_second {p : ℝ} (hp : 0<p) :
    (∫ s, nativeJointEnergy 1 s^2 ∂nativeJointMeasure p) =
      (p/24+1/60)^2+p/1440+13/25200 := by
  letI:=GammaMixture.gammaProduct_probability hp
  letI:=boseNoise_probability
  have hχI : Integrable (fun s=>boseNoise s^2) boseNoiseMeasure := by
    simpa only [Real.rpow_two] using boseNoise_power_integrable (by norm_num : (0:ℝ)≤2)
  have hχ : (∫ s,boseNoise s^2 ∂boseNoiseMeasure)=(1/1260:ℝ) := by
    have h:=scaledBoseMoment_2
    change (∫ s,(60*boseNoise s)^2 ∂boseNoiseMeasure)=20/7 at h
    simp only [mul_pow,integral_const_mul] at h
    linarith only [h]
  have hX : Integrable (fun s : NativeJointSample=>gammaTotal s.1^2) (nativeJointMeasure p) :=
    (measurePreserving_fst (μ:=gammaProduct p) (ν:=boseNoiseMeasure)).integrable_comp_of_integrable
      (GammaMixture.gammaTotal_square_integrable hp)
  have hY : Integrable (fun s : NativeJointSample=>boseNoise s.2^2) (nativeJointMeasure p) :=
    (measurePreserving_snd (μ:=gammaProduct p) (ν:=boseNoiseMeasure)).integrable_comp_of_integrable hχI
  have hXY : Integrable (fun s : NativeJointSample=>gammaTotal s.1*boseNoise s.2) (nativeJointMeasure p) :=
    (GammaMixture.integrable_gammaTotal hp).mul_prod boseNoise_integrable
  have hEq : (fun s : NativeJointSample=>nativeJointEnergy 1 s^2)=
      (fun s=>gammaTotal s.1^2+2*(gammaTotal s.1*boseNoise s.2)+boseNoise s.2^2) := by
    funext s
    unfold nativeJointEnergy
    ring
  rw [hEq,integral_add (f:=fun s : NativeJointSample=>gammaTotal s.1^2+2*(gammaTotal s.1*boseNoise s.2))
      (g:=fun s=>boseNoise s.2^2) (hX.add (hXY.const_mul 2)) hY,
    integral_add (f:=fun s : NativeJointSample=>gammaTotal s.1^2)
      (g:=fun s=>2*(gammaTotal s.1*boseNoise s.2)) hX (hXY.const_mul 2),integral_const_mul,nativeJointMeasure,
    integral_fun_fst (fun ω : ℕ→ℝ=>gammaTotal ω^2),
    integral_fun_snd (fun s : BoseNoiseSample=>boseNoise s^2),
    integral_prod_mul gammaTotal boseNoise,
    GammaMixture.gammaTotal_second_integral hp,GammaMixture.gammaTotal_integral hp,
    boseNoise_mean,hχ]
  simp only [probReal_univ,one_smul]
  ring

theorem nativeJointEnergy_one_interpolation {p β : ℝ} (hp : 0<p)
    (hβ : 0≤β) (hβ₁ : β≤1) (hP : p=2*(β+1)) :
    let h:=5*β+6
    (h/60)^β≤jointPowerRow p β 1*(1+2/h)^(1-β) := by
  letI:=nativeJoint_probability hp
  let h:=5*β+6
  let μ:=h/60
  let κ:=1+2/h
  have hh : 0<h := by unfold h;positivity
  have hμ : 0<μ := div_pos hh (by norm_num)
  have hκ : 0<κ := by unfold κ;positivity
  have hM : (∫ s,nativeJointEnergy 1 s ∂nativeJointMeasure p)=μ := by
    rw [nativeJointEnergy_mean hp,hP]
    unfold μ h
    ring
  have hI : Integrable (nativeJointEnergy 1) (nativeJointMeasure p) := by
    simpa only [Real.rpow_one] using nativeJoint_all_positive_moments (q:=1) hp (by norm_num) (by norm_num)
  have h₂I : Integrable (fun s=>nativeJointEnergy 1 s^2) (nativeJointMeasure p) := by
    simpa only [Real.rpow_two] using nativeJoint_all_positive_moments (q:=2) hp (by norm_num) (by norm_num)
  have hA:=jointPowerRow_pos (q:=β) hp (by norm_num : (0:ℝ)≤1)
  have hB : 0<∫ s,nativeJointEnergy 1 s^2 ∂nativeJointMeasure p := by
    rw [nativeJointEnergy_one_second hp]
    positivity
  have hMean : 0<∫ s,nativeJointEnergy 1 s ∂nativeJointMeasure p := by rwa [hM]
  have hInterp:=ACS12.positive_moment_interpolation hβ hβ₁
    (nativeJointEnergy_ae_pos hp (by norm_num)) hI (nativeJoint_all_positive_moments hp (by norm_num) hβ)
    h₂I hA hB hMean
  rw [hM] at hInterp
  have hSecond : (∫ s,nativeJointEnergy 1 s^2 ∂nativeJointMeasure p)≤μ^2*κ := by
    rw [nativeJointEnergy_one_second hp,hP]
    unfold μ κ
    field_simp [hh.ne']
    dsimp only [h]
    nlinarith only [hβ]
  have hPow:=Real.rpow_le_rpow hB.le hSecond (sub_nonneg.mpr hβ₁)
  have hPay:=hInterp.trans (mul_le_mul_of_nonneg_left hPow hA.le)
  have hE : μ^(2-β)=μ^β*μ^(2*(1-β)) := by
    rw [←Real.rpow_add hμ]
    congr 1
    ring
  rw [Real.mul_rpow (sq_nonneg μ) hκ.le,←Real.rpow_two μ,
    ←Real.rpow_mul hμ.le,hE] at hPay
  have hFinal : μ^β*μ^(2*(1-β))≤
      (jointPowerRow p β 1*κ^(1-β))*μ^(2*(1-β)) := by
    simpa only [jointPowerRow,mul_assoc,mul_comm,mul_left_comm] using hPay
  exact (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hμ _)).mp hFinal

theorem boseRow_self_fraction_lower {p N : ℝ} (hp : 2≤p) (hp₄ : p≤4) (hN : 1<N) :
    let β:=(p-2)/2
    (5*β+6)/(N^2*anchorSelfDen β (N^2))≤boseRow p 1/boseRow p N := by
  let β:=(p-2)/2
  let x:=N^2
  let h:=5*β+6
  let μ:=h/60
  let k:=1+2/h
  let v:=1+(x-1)/h
  let H:=(1-β)*k+β*v
  let I₁:=jointPowerRow p β 1
  let Iₓ:=jointPowerRow p β x
  have hp₀ : 0<p:=by linarith only [hp]
  have hβ : 0≤β:=by unfold β;linarith only [hp]
  have hβ₁ : β≤1:=by unfold β;linarith only [hp₄]
  have hN₀:=zero_lt_one.trans hN
  have hx : 0<x:=sq_pos_of_pos hN₀
  have hx₁ : 1<x:=by unfold x;nlinarith only [hN,sq_nonneg (N-1)]
  have hh : 0<h:=by unfold h;positivity
  have hμ : 0<μ:=div_pos hh (by norm_num)
  have hk : 0<k:=by unfold k;positivity
  have hv : 0<v:=by
    have hPos:=sub_pos.mpr hx₁
    unfold v
    positivity
  have hI₁ : 0<I₁:=jointPowerRow_pos hp₀ (by norm_num)
  have hIₓ : 0<Iₓ:=jointPowerRow_pos hp₀ hx.le
  have hAM:=Real.geom_mean_le_arith_mean2_weighted (sub_nonneg.mpr hβ₁) hβ hk.le hv.le
    (by ring : (1-β)+β=1)
  have hH : 0<H :=
    (mul_pos (Real.rpow_pos_of_pos hk _) (Real.rpow_pos_of_pos hv _)).trans_le hAM
  have hNum : μ^β≤I₁*k^(1-β):=
    nativeJointEnergy_one_interpolation hp₀ hβ hβ₁ (by unfold β;ring)
  have hMean:=jointPowerRow_low_Jensen hp₀ hβ hβ₁ hx.le
  have hPV : p/24+x/60=μ*v:=by
    unfold μ v
    field_simp [hh.ne']
    unfold h β
    ring
  rw [hPV,Real.mul_rpow hμ.le hv.le] at hMean
  have hProduct:=mul_le_mul_of_nonneg_right hNum (Real.rpow_nonneg hv.le β)
  have hPaid:=mul_le_mul_of_nonneg_left hAM hI₁.le
  have hRow : Iₓ≤I₁*H:=by
    change Iₓ≤μ^β*v^β at hMean
    change μ^β*v^β≤(I₁*k^(1-β))*v^β at hProduct
    change I₁*(k^(1-β)*v^β)≤I₁*H at hPaid
    nlinarith only [hMean,hProduct,hPaid]
  have hRatio : boseRow p 1/boseRow p N=I₁/(x*Iₓ):=by
    rw [boseRow_joint_all hp₀ zero_lt_one,boseRow_joint_all hp₀ hN₀]
    norm_num only [one_pow,one_mul]
    change nativeJointScale p*I₁/(x*nativeJointScale p*Iₓ)=I₁/(x*Iₓ)
    field_simp [(nativeJointScale_pos hp₀).ne',hx.ne',hIₓ.ne']
    <;>ring
  have hBound : 1/(x*H)≤I₁/(x*Iₓ):=by
    apply (div_le_div_iff₀ (mul_pos hx hH) (mul_pos hx hIₓ)).mpr
    have hPay:=mul_le_mul_of_nonneg_left hRow hx.le
    nlinarith only [hPay]
  have hExact : h/(x*anchorSelfDen β x)=1/(x*H):=by
    have hBody : 0<8+β*(x+2):=by positivity
    unfold anchorSelfDen H k v h
    field_simp [hx.ne',hh.ne',hBody.ne']
    ring_nf at hBody ⊢
    field_simp [hBody.ne']
    <;>ring
  change h/(x*anchorSelfDen β x)≤boseRow p 1/boseRow p N
  rw [hRatio,hExact]
  exact hBound

end ACS12.NativeCells

import ACS12.BoseMeanReduction
import ACS12.BoseCompensatedQuadratic

/-! Conditional Jensen and one correlated AM–GM reduction at every positive anchor. -/
namespace ACS12.NativeCells
open MeasureTheory ProbabilityTheory Set Filter
open GammaMixture (gammaProduct gammaTotal)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem boseAnchorMean_pointwise {p z χ : ℝ} (hp : 2≤p) (hp₄ : p≤4)
    (hz : 0<z) (hχ : 0<χ) :
    let β := (p-2)/2
    let μ := p/24
    let a := z/60
    let w := z*χ
    (60*χ)/anchorMeanDen β z (60*χ) ≤ w*(μ+w)^(β-1)/(μ+a)^β := by
  let β := (p-2)/2
  let μ := p/24
  let a := z/60
  let w := z*χ
  have hβ : 0≤β := by dsimp only [β]; linarith only [hp]
  have hβ₁ : β≤1 := by dsimp only [β]; linarith only [hp₄]
  have hμ : 0<μ := by dsimp only [μ]; linarith only [hp]
  have ha : 0<a := div_pos hz (by norm_num)
  have hw : 0<w := mul_pos hz hχ
  have hU := add_pos hμ hw
  have hV := add_pos hμ ha
  have hAM := Real.geom_mean_le_arith_mean2_weighted
    (sub_nonneg.mpr hβ₁) hβ hU.le hV.le (by ring : (1-β)+β=1)
  have hMul : (μ+w)^(1-β)*(μ+a)^β ≤ a*anchorMeanDen β z (60*χ) := by
    convert hAM using 1
    unfold anchorMeanDen β μ a w
    field_simp [hz.ne']
    <;> ring
  have hDen : 0<anchorMeanDen β z (60*χ) := by
    unfold anchorMeanDen
    have hB : 0<5*(β+1)/z := by positivity
    exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hB hβ)
      (mul_nonneg (sub_nonneg.mpr hβ₁) (by positivity))
  have hInv : (μ+w)^(β-1) = 1/(μ+w)^(1-β) := by
    rw [show β-1=-(1-β) by ring,Real.rpow_neg hU.le,one_div]
  change (60*χ)/anchorMeanDen β z (60*χ) ≤ w*(μ+w)^(β-1)/(μ+a)^β
  rw [hInv,mul_one_div,div_div]
  have hBase : 0<(μ+w)^(1-β)*(μ+a)^β := by positivity
  apply (div_le_div_iff₀ hDen hBase).mpr
  have hPay:=mul_le_mul_of_nonneg_left hMul (by positivity : (0:ℝ)≤60*χ)
  dsimp only [a,w] at hPay ⊢
  nlinarith only [hPay]

theorem jointNativeMean_anchor_reduction {p z : ℝ} (hp : 2≤p) (hp₄ : p≤4) (hz : 0<z) :
    (∫ s, scaledBoseNoise s/anchorMeanDen ((p-2)/2) z (scaledBoseNoise s) ∂boseNoiseMeasure) ≤
      jointNativeMean p z := by
  let β := (p-2)/2
  let e := (p/24+z/60)^β
  let G (s : NativeJointSample) := z*boseNoise s.2*nativeJointEnergy z s^(β-1)/e
  have hp₀ : 0<p := by linarith only [hp]
  have hz₀ : 0<z := by linarith only [hz]
  have hβ : 0≤β := by dsimp only [β]; linarith only [hp]
  have hβ₁ : β≤1 := by dsimp only [β]; linarith only [hp₄]
  have he : 0<e := Real.rpow_pos_of_pos (by positivity : 0<p/24+z/60) _
  letI := GammaMixture.gammaProduct_probability hp₀
  letI := boseNoise_probability
  have hGI : Integrable G (nativeJointMeasure p) := by
    have h := ((jointWeightedPower_integrable hp₀ hβ hz₀ 1).const_mul z).div_const e
    simpa only [G,jointWeightedPower,pow_one,Nat.cast_one,mul_assoc] using h
  have hPoint : ∀ᵐ s ∂boseNoiseMeasure,
      scaledBoseNoise s/anchorMeanDen β z (scaledBoseNoise s) ≤
        ∫ ω, G (ω,s) ∂gammaProduct p := by
    filter_upwards [boseNoise_ae_pos] with s hs
    have hSupp := gammaTotal_negative_support hp₀ hβ₁ (mul_pos hz₀ hs)
    have hPaid := mul_le_mul_of_nonneg_left hSupp (div_pos (mul_pos hz₀ hs) he).le
    have hCmp := boseAnchorMean_pointwise hp hp₄ hz hs
    change scaledBoseNoise s/anchorMeanDen β z (scaledBoseNoise s) ≤ _ at hCmp
    have hId : (∫ ω, G (ω,s) ∂gammaProduct p) =
        z*boseNoise s*(∫ ω, (gammaTotal ω+z*boseNoise s)^(β-1) ∂gammaProduct p)/e := by
      unfold G nativeJointEnergy
      simp only [Prod.fst,Prod.snd]
      rw [integral_div,integral_const_mul]
    rw [hId]
    exact hCmp.trans (by convert hPaid using 1 <;> ring)
  have hCmp := integral_mono_of_nonneg
    (boseNoise_ae_pos.mono fun s hs => by
      apply div_nonneg (mul_nonneg (by norm_num) hs.le)
      unfold anchorMeanDen
      exact add_nonneg (add_nonneg (by positivity) hβ) (mul_nonneg (sub_nonneg.mpr hβ₁)
        (mul_nonneg (by norm_num) hs.le)))
    hGI.integral_prod_right hPoint
  have hInt : (∫ s, ∫ ω, G (ω,s) ∂gammaProduct p ∂boseNoiseMeasure) =
      z*jointWeightedPowerRow p β 1 z/e := by
    rw [←integral_prod_symm _ hGI]
    change (∫ s, G s ∂nativeJointMeasure p) = _
    unfold G jointWeightedPowerRow jointWeightedPower
    simp only [pow_one,Nat.cast_one]
    rw [integral_div,←integral_const_mul]
    congr 2
    funext s
    ring
  rw [hInt] at hCmp
  have hNum : 0≤z*jointWeightedPowerRow p β 1 z := by
    apply mul_nonneg hz₀.le
    apply integral_nonneg_of_ae
    filter_upwards [nativeJoint_coordinates_ae_pos hp₀] with s hs
    unfold jointWeightedPower
    exact mul_nonneg (pow_nonneg hs.2.le _) (Real.rpow_nonneg
      (add_nonneg hs.1.le (mul_nonneg hz₀.le hs.2.le)) _)
  have hRow : jointPowerRow p β z ≤ e := jointPowerRow_low_Jensen hp₀ hβ hβ₁ hz₀.le
  have hRPos := jointPowerRow_pos (q:=β) hp₀ hz₀.le
  have hRatio := div_le_div_of_nonneg_left hNum hRPos hRow
  rw [jointNativeMean_weighted hp₀ hz₀]
  exact hCmp.trans hRatio


theorem jointNativeMean_anchor_lower {p z : ℝ} (hp : 2≤p) (hp₄ : p≤4) (hz : 0<z) :
    9*z/(z*(18-8*((p-2)/2))+50*(1+(p-2)/2))<jointNativeMean p z := by
  exact (anchorMean_quadratic_lower (by linarith only [hp]) (by linarith only [hp₄]) hz).trans_le
    (jointNativeMean_anchor_reduction hp hp₄ hz)

end ACS12.NativeCells

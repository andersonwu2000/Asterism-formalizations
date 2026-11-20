import ACS12.BoseNoiseSixMoments
import ACS12.JointNativeTiltMoments
import ACS12.NegativePowerSupport
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.MeanInequalities

/-! CM's mean reduction uses only independence, conditional power support and AM–GM. -/
namespace ACS12.NativeCells
open MeasureTheory ProbabilityTheory Set Filter
open GammaMixture (gammaProduct gammaTotal)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem boseNoise_integrable : Integrable boseNoise boseNoiseMeasure := by
  simpa only [Real.rpow_one] using boseNoise_power_integrable (by norm_num : (0:ℝ)≤1)

theorem boseNoise_mean : (∫ s, boseNoise s ∂boseNoiseMeasure) = 1/60 := by
  have h := scaledBoseMoment_1
  change (∫ s, (60*boseNoise s)^1 ∂boseNoiseMeasure) = 1 at h
  simp only [pow_one,integral_const_mul] at h
  linarith only [h]

theorem nativeJointEnergy_mean {p z : ℝ} (hp : 0<p) :
    (∫ s, nativeJointEnergy z s ∂nativeJointMeasure p) = p/24+z/60 := by
  letI := GammaMixture.gammaProduct_probability hp
  letI := boseNoise_probability
  have hX : Integrable (fun s : NativeJointSample => gammaTotal s.1) (nativeJointMeasure p) :=
    (measurePreserving_fst (μ:=gammaProduct p) (ν:=boseNoiseMeasure)).integrable_comp_of_integrable
      (GammaMixture.integrable_gammaTotal hp)
  have hW : Integrable (fun s : NativeJointSample => z*boseNoise s.2) (nativeJointMeasure p) :=
    ((measurePreserving_snd (μ:=gammaProduct p) (ν:=boseNoiseMeasure)).integrable_comp_of_integrable
      boseNoise_integrable).const_mul z
  change (∫ s, gammaTotal s.1+z*boseNoise s.2 ∂nativeJointMeasure p) = _
  rw [integral_add hX hW,integral_const_mul,nativeJointMeasure,
    integral_fun_fst,integral_fun_snd,GammaMixture.gammaTotal_integral hp,boseNoise_mean]
  simp only [probReal_univ,one_smul]
  ring

theorem jointPowerRow_low_Jensen {p β z : ℝ} (hp : 0<p) (hβ : 0≤β) (hβ₁ : β≤1)
    (hz : 0≤z) :
    jointPowerRow p β z ≤ (p/24+z/60)^β := by
  letI := nativeJoint_probability hp
  have hI : Integrable (nativeJointEnergy z) (nativeJointMeasure p) := by
    simpa only [Real.rpow_one] using nativeJoint_all_positive_moments (q:=1) hp hz (by norm_num)
  have hJ := (Real.concaveOn_rpow hβ hβ₁).le_map_integral
    (Real.continuous_rpow_const hβ).continuousOn isClosed_Ici
    ((nativeJointEnergy_ae_pos hp hz).mono fun _ hs => hs.le) hI
    (nativeJoint_all_positive_moments hp hz hβ)
  rw [nativeJointEnergy_mean hp] at hJ
  exact hJ

theorem gammaTotal_negative_support {p β w : ℝ} (hp : 0<p) (hβ₁ : β≤1) (hw : 0<w) :
    (p/24+w)^(β-1) ≤ ∫ ω, (gammaTotal ω+w)^(β-1) ∂gammaProduct p := by
  letI := GammaMixture.gammaProduct_probability hp
  let μ := p/24
  let c := (β-1)*(μ+w)^(β-2)
  have hμ : 0<μ := div_pos hp (by norm_num)
  have hI : Integrable (fun ω => (gammaTotal ω+w)^(β-1)) (gammaProduct p) := by
    apply (integrable_const (μ:=gammaProduct p) (w^(β-1))).mono'
      (((GammaMixture.measurable_gammaTotal.add_const w).pow_const _).aestronglyMeasurable)
    filter_upwards [GammaMixture.gammaProduct_ae_total_pos hp] with ω hω
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : 0≤gammaTotal ω+w) _)]
    exact Real.rpow_le_rpow_of_nonpos hw (by linarith) (by linarith only [hβ₁])
  have hL : Integrable (fun ω => (μ+w)^(β-1)+c*(gammaTotal ω-μ)) (gammaProduct p) :=
    (integrable_const _).add (((GammaMixture.integrable_gammaTotal hp).sub (integrable_const μ)).const_mul c)
  have hCmp := integral_mono_ae hL hI ((GammaMixture.gammaProduct_ae_total_pos hp).mono
    fun ω hω => by
      have h := ACS12.negativePower_support (by linarith only [hβ₁] : β-1≤0)
        (add_pos hω hw) (add_pos hμ hw)
      simpa only [show β-1-1=β-2 by ring,add_sub_add_right_eq_sub,c] using h)
  have hDiff : Integrable (fun ω => gammaTotal ω-μ) (gammaProduct p) :=
    (GammaMixture.integrable_gammaTotal hp).sub (integrable_const μ)
  have hAdd := integral_add (integrable_const (μ:=gammaProduct p) ((μ+w)^(β-1)))
    (hDiff.const_mul c)
  have hSub := integral_sub (GammaMixture.integrable_gammaTotal hp) (integrable_const μ)
  simp only [Pi.add_apply,Pi.sub_apply] at hAdd hSub
  rw [hAdd,integral_const_mul,hSub,integral_const,integral_const,
    GammaMixture.gammaTotal_integral hp] at hCmp
  simpa only [μ,probReal_univ,one_smul,sub_self,mul_zero,add_zero] using hCmp

end ACS12.NativeCells

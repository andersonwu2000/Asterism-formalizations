import ACS12.NativeJointGammaLaw
import ACS12.GammaProductExponential
import ACS12.ExponentialPowerMoments
import Mathlib.Probability.Moments.ComplexMGF

/-! The fixed Bose noise has positive exponential moments, and hence its analytic origin germ. -/
namespace ACS12.NativeCells
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

theorem boseNoise_exponential_integrable {c : ℝ} (hc₀ : 0 ≤ c) (hc : c < GammaMixture.gammaRate 0) :
    Integrable (fun s => Real.exp (c*boseNoise s)) boseNoiseMeasure := by
  let ν := nativeZetaMeasure 2
  let γ := gammaMeasure 1 1
  let r := GammaMixture.gammaRate 0
  have hr : 0 < r := GammaMixture.gammaRate_pos 0
  letI := nativeZeta_probability (by norm_num : (1:ℝ)<2)
  letI := isProbabilityMeasure_gammaMeasure zero_lt_one zero_lt_one
  have hExp := (GammaDistribution.gammaMeasure_exponential zero_lt_one zero_lt_one
    ((div_lt_one hr).mpr hc)).1
  have hLift : Integrable (fun s : BoseNoiseSample => Real.exp ((c/r)*s.2)) boseNoiseMeasure :=
    (measurePreserving_snd (μ := ν) (ν := γ)).integrable_comp_of_integrable hExp
  apply hLift.mono' ((measurable_boseNoise.const_mul c).exp.aestronglyMeasurable)
  have hE : ∀ᵐ s : BoseNoiseSample ∂boseNoiseMeasure, 0 < s.2 :=
    Measure.quasiMeasurePreserving_snd.ae (gammaUnit_ae_pos 1)
  filter_upwards [hE] with s hs
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  have hχ : boseNoise s ≤ s.2/r := by
    unfold boseNoise r
    exact div_le_div_of_nonneg_left hs.le (GammaMixture.gammaRate_pos 0) (GammaMixture.gammaRate_zero_le s.1)
  have h := mul_le_mul_of_nonneg_left hχ hc₀
  convert h using 1 <;> ring

theorem boseNoise_integrableExpSet {c : ℝ} (hc : c < GammaMixture.gammaRate 0) :
    c ∈ integrableExpSet boseNoise boseNoiseMeasure := by
  letI := boseNoise_probability
  by_cases hc₀ : 0 ≤ c
  · exact boseNoise_exponential_integrable hc₀ hc
  · apply (integrable_const (μ := boseNoiseMeasure) (1:ℝ)).mono'
      ((measurable_boseNoise.const_mul c).exp.aestronglyMeasurable)
    filter_upwards [boseNoise_ae_pos] with s hs
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hc₀) hs.le)

theorem boseNoise_complexMGF_analytic {z : ℂ} (hz : z.re < GammaMixture.gammaRate 0) :
    AnalyticAt ℂ (complexMGF boseNoise boseNoiseMeasure) z := by
  have hSubset : Iio (GammaMixture.gammaRate 0) ⊆ integrableExpSet boseNoise boseNoiseMeasure :=
    fun _ h => boseNoise_integrableExpSet h
  exact analyticAt_complexMGF (interior_maximal hSubset isOpen_Iio hz)

theorem boseNoise_power_integrable {r : ℝ} (hr : 0 ≤ r) :
    Integrable (fun s => boseNoise s^r) boseNoiseMeasure := by
  letI := boseNoise_probability
  let c := GammaMixture.gammaRate 0/2
  have hc : 0 < c := half_pos (GammaMixture.gammaRate_pos 0)
  exact integrable_rpow_of_exponential measurable_boseNoise (boseNoise_ae_pos.mono fun _ h => h.le)
    hc (boseNoise_exponential_integrable hc.le (by unfold c; linarith [GammaMixture.gammaRate_pos 0])) hr

end ACS12.NativeCells

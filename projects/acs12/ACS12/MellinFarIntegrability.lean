import ACS12.MellinFarBound
import ACS12.SquareRootExponentialTail
import ACS12.ComplexMGFMeasurable

/-! Every full Mellin far integral is finite, with a common compact-parameter envelope. -/
namespace ACS12.NativeCells
open MeasureTheory ProbabilityTheory Set GammaMixture

theorem measurable_jointLaplaceCarrier (α : ℂ) (z : ℝ) :
    Measurable (fun t : ℝ => jointLaplaceCarrier α z (t:ℂ)) := by
  letI := gammaProduct_probability zero_lt_one
  letI := boseNoise_probability
  have hGM : Measurable (gammaLaplaceGerm 1) :=
    (measurable_complexMGF measurable_gammaTotal).comp measurable_neg
  have hNM := measurable_complexMGF (μ := boseNoiseMeasure) measurable_boseNoise
  have hReal := Complex.continuous_ofReal.measurable
  have hLog : Measurable (fun t : ℝ => jointPhiLog (t:ℂ)) :=
    Complex.measurable_log.comp (hGM.comp hReal)
  have hArg : Measurable (fun t : ℝ => -(z:ℂ)*(t:ℂ)) := by fun_prop
  exact (Complex.continuous_exp.measurable.comp (hLog.const_mul α)).mul (hNM.comp hArg)

theorem mellinFar_integrable {α h : ℂ} {z : ℝ} (hα : 0 < α.re) (hz : 0 ≤ z) :
    IntegrableOn (fun t : ℝ => (t:ℂ)^(-h-1)*jointLaplaceCarrier α z (t:ℂ)) (Ioi 1) := by
  let B := max (-h.re) 0
  have hh : -B ≤ h.re := by
    have h := le_max_left (-h.re) 0
    unfold B
    linarith only [h]
  have hMajor := (integrableOn_rpow_exp_neg_sqrt (q := B+α.re/2) (half_pos hα)).const_mul
    (mellinFarConstant α.re)
  have hPow : Measurable (fun t : ℝ => (t:ℂ)^(-h-1)) := by fun_prop
  apply hMajor.mono' (hPow.mul (measurable_jointLaplaceCarrier α z)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simpa only [mul_assoc] using mellinFar_norm_bound hz hα le_rfl hh (show (1:ℝ)≤t from ht.le)

end ACS12.NativeCells

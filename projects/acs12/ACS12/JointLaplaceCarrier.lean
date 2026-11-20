import ACS12.GammaProductAnalytic
import ACS12.BoseNoiseExponential
import ACS12.NativeJointMellinKernel
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! The explicit complex-shape Laplace carrier uses an analytic Phi germ and the same fixed Bose noise; no complex probability law is introduced. -/
namespace ACS12.NativeCells
open MeasureTheory ProbabilityTheory Set
open GammaMixture

noncomputable def jointPhiLog (t : ℂ) : ℂ :=
  Complex.log (gammaLaplaceGerm 1 t)

noncomputable def jointLaplaceCarrier (α : ℂ) (z : ℝ) (t : ℂ) : ℂ :=
  Complex.exp (α*jointPhiLog t) * complexMGF boseNoise boseNoiseMeasure (-(z:ℂ)*t)

theorem jointPhiLog_zero : jointPhiLog 0 = 0 := by
  unfold jointPhiLog
  rw [gammaLaplaceGerm_zero zero_lt_one,Complex.log_one]

theorem jointPhiLog_analytic : AnalyticAt ℂ jointPhiLog 0 := by
  apply (gammaLaplaceGerm_analytic zero_lt_one).clog
  rw [gammaLaplaceGerm_zero zero_lt_one]
  exact Complex.one_mem_slitPlane

theorem jointLaplaceCarrier_zero (α : ℂ) (z : ℝ) : jointLaplaceCarrier α z 0 = 1 := by
  letI := boseNoise_probability
  unfold jointLaplaceCarrier
  rw [jointPhiLog_zero,mul_zero,Complex.exp_zero,mul_zero,show (0:ℂ) = ((0:ℝ):ℂ) by rfl,
    complexMGF_ofReal,mgf_zero]
  simp

theorem jointLaplaceCarrier_origin_analytic (α : ℂ) (z : ℝ) :
    AnalyticAt ℂ (fun a : ℂ × ℂ => jointLaplaceCarrier a.1 z a.2) (α,0) := by
  have hFst : AnalyticAt ℂ (fun a : ℂ × ℂ => a.1) (α,0) :=
    (ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt _
  have hSnd : AnalyticAt ℂ (fun a : ℂ × ℂ => a.2) (α,0) :=
    (ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt _
  have hLog : AnalyticAt ℂ (fun a : ℂ × ℂ => jointPhiLog a.2) (α,0) :=
    jointPhiLog_analytic.comp_of_eq' hSnd rfl
  have hArg : AnalyticAt ℂ (fun a : ℂ × ℂ => -(z:ℂ)*a.2) (α,0) := by fun_prop
  have hNoise := boseNoise_complexMGF_analytic (z := 0) (by simpa using gammaRate_pos 0)
  have hN : AnalyticAt ℂ (fun a : ℂ × ℂ =>
      complexMGF boseNoise boseNoiseMeasure (-(z:ℂ)*a.2)) (α,0) :=
    hNoise.comp_of_eq' hArg (by simp)
  exact ((hFst.mul hLog).cexp').mul hN

theorem jointLaplaceCarrier_real {p z t : ℝ} (hp : 0 < p) (hz : 0 ≤ z) (ht : 0 < t) :
    jointLaplaceCarrier (p:ℂ) z (t:ℂ) = (nativeJointLaplaceValue p z t : ℂ) := by
  let v := Real.sqrt t
  have hv : 0 < v := Real.sqrt_pos.mpr ht
  have hv₂ : v^2 = t := Real.sq_sqrt ht.le
  let φ := v/(2*Real.sinh (v/2))
  have hφ : 0 < φ := by unfold φ; positivity
  have hG : gammaLaplaceGerm 1 (t:ℂ) = (φ:ℂ) := by
    have h := gammaLaplaceGerm_real zero_lt_one hv
    rw [hv₂,Real.rpow_one] at h
    exact h
  have hLog : jointPhiLog (t:ℂ) = (Real.log φ:ℂ) := by
    unfold jointPhiLog
    rw [hG,← Complex.ofReal_log hφ.le]
  unfold jointLaplaceCarrier
  rw [hLog,← Complex.ofReal_mul,← Complex.ofReal_exp]
  have hExp : Real.exp (p*Real.log φ) = φ^p := by rw [Real.rpow_def_of_pos hφ]; congr 1; ring
  rw [hExp,show -(z:ℂ)*(t:ℂ) = (-(t*z):ℝ) by push_cast; ring,
    complexMGF_ofReal]
  unfold mgf nativeJointLaplaceValue
  have hRow := nativeJoint_laplace_product hp hv hz
  rw [hv₂] at hRow
  rw [hRow]
  push_cast
  rfl

end ACS12.NativeCells

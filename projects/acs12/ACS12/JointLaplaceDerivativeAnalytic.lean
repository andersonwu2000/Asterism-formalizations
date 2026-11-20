import ACS12.AnalyticVerticalDerivative
import ACS12.JointLaplaceUniformDisc

/-! Actual t derivatives are holomorphic in the independent complex shape. -/
namespace ACS12.NativeCells
open MeasureTheory ProbabilityTheory Set Filter GammaMixture Metric
open scoped Topology
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem jointLaplaceCarrier_joint_analytic {α w : ℂ} {z : ℝ} (hGamma : -w.re < gammaRate 0)
    (hNoiseRate : (-(z:ℂ)*w).re < gammaRate 0) (hSlit : gammaLaplaceGerm 1 w ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun a : ℂ × ℂ => jointLaplaceCarrier a.1 z a.2) (α,w) := by
  have hFst : AnalyticAt ℂ (fun a : ℂ × ℂ => a.1) (α,w) :=
    (ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt _
  have hSnd : AnalyticAt ℂ (fun a : ℂ × ℂ => a.2) (α,w) :=
    (ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt _
  have hG : AnalyticAt ℂ (gammaLaplaceGerm 1) w := by
    have hMGF := gammaTotal_complexMGF_analytic zero_lt_one (z:=-w)
      (by simpa only [Complex.neg_re] using hGamma)
    exact hMGF.comp_of_eq' (by fun_prop : AnalyticAt ℂ (fun x : ℂ => -x) w) rfl
  have hLog : AnalyticAt ℂ (fun a : ℂ × ℂ => jointPhiLog a.2) (α,w) :=
    (hG.clog hSlit).comp_of_eq' hSnd rfl
  have hNoise := boseNoise_complexMGF_analytic hNoiseRate
  have hN : AnalyticAt ℂ (fun a : ℂ × ℂ => complexMGF boseNoise boseNoiseMeasure (-(z:ℂ)*a.2)) (α,w) :=
    hNoise.comp_of_eq' (by fun_prop) rfl
  exact ((hFst.mul hLog).cexp').mul hN

theorem jointLaplaceCarrier_joint_real_analytic (α : ℂ) {z t : ℝ} (hz : 0 ≤ z) (ht : 0 < t) :
    AnalyticAt ℂ (fun a : ℂ × ℂ => jointLaplaceCarrier a.1 z a.2) (α,(t:ℂ)) := by
  apply jointLaplaceCarrier_joint_analytic
    (by simp only [Complex.ofReal_re]; linarith only [ht,gammaRate_pos 0])
    (by simp only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.ofReal_re,
      Complex.ofReal_im,neg_zero,zero_mul,sub_zero]
        have h := mul_nonneg hz ht.le
        linarith only [h,gammaRate_pos 0])
  rw [gammaLaplaceGerm_one_real ht]
  exact Complex.ofReal_mem_slitPlane.mpr (mellinPhi_pos ht)

theorem jointLaplaceDerivative_shape_analytic {z t : ℝ} (hz : 0 ≤ z) (ht : 0 < t)
    (k : ℕ) (α : ℂ) :
    AnalyticAt ℂ (fun a => iteratedDeriv k (jointLaplaceCarrier a z) (t:ℂ)) α :=
  section_iteratedDeriv_analytic (jointLaplaceCarrier_joint_real_analytic α hz ht) k

theorem jointLaplaceDerivative_continuousOn {z : ℝ} (hz : 0 ≤ z) (k : ℕ) (α : ℂ) :
    ContinuousOn (fun t : ℝ => iteratedDeriv k (jointLaplaceCarrier α z) (t:ℂ)) (Ioi 0) := by
  let F (a : ℂ × ℂ) := jointLaplaceCarrier a.1 z a.2
  have hV : ContinuousOn (fun t : ℝ => verticalDerivative F k (α,(t:ℂ))) (Ioi 0) := by
    intro t ht
    have hArg : ContinuousAt (fun x : ℝ => (α,(x:ℂ))) t :=
      (continuous_const.prodMk Complex.continuous_ofReal).continuousAt
    have hCont : ContinuousAt (fun x : ℝ => verticalDerivative F k (α,(x:ℂ))) t :=
      ContinuousAt.comp (g:=verticalDerivative F k) (f:=fun x : ℝ => (α,(x:ℂ)))
        (verticalDerivative_analytic (jointLaplaceCarrier_joint_real_analytic α hz ht) k).continuousAt hArg
    exact hCont.continuousWithinAt
  apply hV.congr
  intro t ht
  exact (verticalDerivative_eq (jointLaplaceCarrier_joint_real_analytic α hz ht) k).symm

end ACS12.NativeCells

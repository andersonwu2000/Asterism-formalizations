import ACS12.JointDifferentiatedLaplace
import ACS12.JointLaplaceDerivativeAnalytic
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! The complex-shape carrier differentiates the same actual full joint Laplace law. -/
namespace ACS12.NativeCells
open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped Topology
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

private theorem complex_germ_eq_of_positive_real {f g : ℂ → ℂ} {t : ℝ} (ht : 0 < t)
    (hf : AnalyticAt ℂ f (t:ℂ)) (hg : AnalyticAt ℂ g (t:ℂ))
    (hEq : ∀ x : ℝ, 0 < x → f (x:ℂ)=g (x:ℂ)) : f =ᶠ[𝓝 (t:ℂ)] g := by
  have hAccum : (t:ℂ) ∈ closure ({w : ℂ | f w=g w}\{(t:ℂ)}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    let x := t+ε/2
    have hx : 0 < x := by dsimp [x]; linarith only [ht,hε]
    refine ⟨(x:ℂ),⟨hEq x hx,?_⟩,?_⟩
    · intro h
      have h' : (x:ℂ)=(t:ℂ) := Set.mem_singleton_iff.mp h
      have h'' := congrArg Complex.re h'
      simp only [Complex.ofReal_re] at h''
      dsimp [x] at h''
      linarith only [h'',hε]
    · rw [dist_eq_norm,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
      have hX : x-t=ε/2 := by dsimp [x]; ring
      rw [abs_sub_comm,hX,abs_of_pos (half_pos hε)]
      linarith only [hε]
  apply (hf.frequently_eq_iff_eventually_eq hg).mp
  rw [frequently_nhdsWithin_iff]
  exact (mem_closure_iff_frequently.mp hAccum).mono fun w hw => ⟨hw.1,hw.2⟩

theorem jointLaplaceCarrier_real_iteratedDeriv {p z t : ℝ} (hp : 0 < p) (hz : 0 ≤ z)
    (ht : 0 < t) (k : ℕ) :
    iteratedDeriv k (jointLaplaceCarrier (p:ℂ) z) (t:ℂ) =
      (-1:ℂ)^k*((∫ ω, nativeJointEnergy z ω^k*Real.exp (-t*nativeJointEnergy z ω)
        ∂nativeJointMeasure p:ℝ):ℂ) := by
  letI := nativeJoint_probability hp
  have hF : AnalyticAt ℂ (jointLaplaceCarrier (p:ℂ) z) (t:ℂ) :=
    (jointLaplaceCarrier_joint_real_analytic (p:ℂ) hz ht).comp_of_eq'
      (by fun_prop : AnalyticAt ℂ (fun w : ℂ => ((p:ℂ),w)) (t:ℂ)) rfl
  obtain ⟨c,hc,hExp⟩ := nativeJoint_exponential_moment hp hz
  have hMem : -t ∈ interior (integrableExpSet (nativeJointEnergy z) (nativeJointMeasure p)) := by
    have hSub : Iio c ⊆ integrableExpSet (nativeJointEnergy z) (nativeJointMeasure p) := by
      intro a ha
      apply hExp.mono' (((measurable_nativeJointEnergy z).const_mul a).exp.aestronglyMeasurable)
      filter_upwards [nativeJointEnergy_ae_pos hp hz] with ω hω
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ha.le hω.le)
    exact interior_maximal hSub isOpen_Iio (by linarith only [ht,hc] : -t < c)
  have hG : AnalyticAt ℂ (jointComplexLaplace p z) (t:ℂ) := by
    have h := analyticAt_complexMGF (X:=nativeJointEnergy z) (μ:=nativeJointMeasure p)
      (z:=-(t:ℂ)) (by simpa only [Complex.neg_re,Complex.ofReal_re] using hMem)
    exact h.comp_of_eq' (by fun_prop : AnalyticAt ℂ (fun w : ℂ => -w) (t:ℂ)) rfl
  have hEq := complex_germ_eq_of_positive_real ht hF hG (fun x hx => by
    rw [jointLaplaceCarrier_real hp hz hx]
    unfold jointComplexLaplace
    rw [←Complex.ofReal_neg,complexMGF_ofReal]
    rfl)
  rw [hEq.iteratedDeriv_eq k]
  exact jointComplexLaplace_iteratedDeriv hp hz ht k

end ACS12.NativeCells

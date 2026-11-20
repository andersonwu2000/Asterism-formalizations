import ACS12.JointAllPositiveMoments
import ACS12.JointAllNegativeMoments
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Differentiated Laplace moments on the actual full X_alpha+z chi law. -/
namespace ACS12.NativeCells
open MeasureTheory Set Filter ProbabilityTheory
open GammaDeficit (gamma_exp_integral integrable_gamma_exp)
open scoped Topology
set_option maxHeartbeats 1200000

theorem nativeJoint_all_real_moments {p z q : ℝ} (hp : 0 < p) (hz : 0 ≤ z) :
    Integrable (fun s => nativeJointEnergy z s^q) (nativeJointMeasure p) := by
  by_cases hq : 0 ≤ q
  · exact nativeJoint_all_positive_moments hp hz hq
  · have hr : 0 < -q := by linarith only [hq]
    simpa only [neg_neg] using (nativeJoint_all_negative_moments hp hz hr).1

noncomputable def jointComplexLaplace (p z : ℝ) (t : ℂ) : ℂ :=
  complexMGF (nativeJointEnergy z) (nativeJointMeasure p) (-t)

theorem jointComplexLaplace_iteratedDeriv {p z t : ℝ} (hp : 0 < p) (hz : 0 ≤ z)
    (ht : 0 < t) (k : ℕ) :
    iteratedDeriv k (jointComplexLaplace p z) (t:ℂ) =
      (-1:ℂ)^k*((∫ ω, nativeJointEnergy z ω^k*Real.exp (-t*nativeJointEnergy z ω)
        ∂nativeJointMeasure p:ℝ):ℂ) := by
  letI := nativeJoint_probability hp
  obtain ⟨c,hc,hExp⟩ := nativeJoint_exponential_moment hp hz
  have hMem : -t ∈ interior (integrableExpSet (nativeJointEnergy z) (nativeJointMeasure p)) := by
    have hSub : Iio c ⊆ integrableExpSet (nativeJointEnergy z) (nativeJointMeasure p) := by
      intro a ha
      apply hExp.mono' (((measurable_nativeJointEnergy z).const_mul a).exp.aestronglyMeasurable)
      filter_upwards [nativeJointEnergy_ae_pos hp hz] with ω hω
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ha.le hω.le)
    exact interior_maximal hSub isOpen_Iio (show -t < c by linarith only [ht,hc])
  unfold jointComplexLaplace
  rw [iteratedDeriv_comp_neg,iteratedDeriv_complexMGF (by simpa using hMem)]
  simp only [smul_eq_mul]
  congr 1
  calc
    _ = ∫ ω, ((nativeJointEnergy z ω^k*Real.exp (-t*nativeJointEnergy z ω):ℝ):ℂ)
        ∂nativeJointMeasure p := by
      apply integral_congr_ae
      exact Eventually.of_forall fun ω => by
        push_cast
        simp only [Complex.ofReal_pow,←Complex.ofReal_mul,←Complex.ofReal_neg,Complex.ofReal_exp]
    _ = _ := integral_complex_ofReal

/-- Weighted ordinary Gamma integration; no Taylor compensation or pole subtraction. -/
theorem jointDifferentiatedLaplace_moment {p z β : ℝ} (hp : 0 < p) (hz : 0 ≤ z)
    (k : ℕ) (hβ : β < (k:ℝ)) :
    IntegrableOn (fun t : ℝ => t^((k:ℝ)-β-1)*
      (∫ ω, nativeJointEnergy z ω^k*Real.exp (-t*nativeJointEnergy z ω) ∂nativeJointMeasure p)) (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0, t^((k:ℝ)-β-1)*
      (∫ ω, nativeJointEnergy z ω^k*Real.exp (-t*nativeJointEnergy z ω) ∂nativeJointMeasure p)) =
      Real.Gamma ((k:ℝ)-β)*(∫ ω, nativeJointEnergy z ω^β ∂nativeJointMeasure p) := by
  let μ := nativeJointMeasure p
  letI : IsProbabilityMeasure μ := nativeJoint_probability hp
  let ν := volume.restrict (Ioi (0:ℝ))
  let r : ℝ := (k:ℝ)-β
  let Y := nativeJointEnergy z
  let F (a : NativeJointSample × ℝ) := Y a.1^k*(a.2^(r-1)*Real.exp (-Y a.1*a.2))
  have hr : 0 < r := sub_pos.mpr hβ
  have hPos : ∀ᵐ ω ∂μ, 0 < Y ω := nativeJointEnergy_ae_pos hp hz
  have hMoment : Integrable (fun ω => Y ω^β) μ := by
    by_cases h : 0 ≤ β
    · exact nativeJoint_all_positive_moments hp hz h
    · have hβ₀ : 0 < -β := neg_pos.mpr (lt_of_not_ge h)
      simpa only [neg_neg] using (nativeJoint_all_negative_moments hp hz hβ₀).1
  have hM : Measurable F := by
    have hY : Measurable (fun a : NativeJointSample × ℝ => Y a.1) :=
      (measurable_nativeJointEnergy z).comp measurable_fst
    exact (hY.pow_const k).mul ((measurable_snd.pow_const _).mul ((hY.neg.mul measurable_snd).exp))
  have hRowI : ∀ᵐ ω ∂μ, Integrable (fun t => F (ω,t)) ν := by
    filter_upwards [hPos] with ω hω
    exact (integrable_gamma_exp hr hω).const_mul (Y ω^k)
  have hRow : ∀ᵐ ω ∂μ, (∫ t, F (ω,t) ∂ν) = Real.Gamma r*Y ω^β := by
    filter_upwards [hPos] with ω hω
    dsimp [F,ν]
    rw [integral_const_mul,gamma_exp_integral hr hω]
    have hPow : Y ω^k*Y ω^(-r) = Y ω^β := by
      rw [←Real.rpow_natCast,←Real.rpow_add hω]
      congr 1
      dsimp [r]; ring
    calc
      _ = Real.Gamma r*(Y ω^k*Y ω^(-r)) := by ring
      _ = _ := by rw [hPow]
  have hFI : Integrable F (μ.prod ν) := by
    apply (integrable_prod_iff hM.aestronglyMeasurable).mpr
    refine ⟨hRowI,?_⟩
    apply (hMoment.const_mul (Real.Gamma r)).congr
    filter_upwards [hPos,hRow] with ω hω hR
    have hNon : ∀ᵐ t ∂ν, 0 ≤ F (ω,t) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht₀ : 0 < t := ht
      exact mul_nonneg (pow_nonneg hω.le k)
        (mul_nonneg (Real.rpow_nonneg ht₀.le _) (Real.exp_pos _).le)
    rw [show (∫ t, ‖F (ω,t)‖ ∂ν) = ∫ t, F (ω,t) ∂ν from
      integral_congr_ae (hNon.mono fun t ht => Real.norm_of_nonneg ht),hR]
  have hCol (t : ℝ) : (∫ ω, F (ω,t) ∂μ) =
      t^(r-1)*(∫ ω, Y ω^k*Real.exp (-t*Y ω) ∂μ) := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun ω => by
      dsimp [F]
      rw [show -Y ω*t = -t*Y ω by ring]
      ring
  constructor
  · apply hFI.integral_prod_right.congr
    exact Eventually.of_forall hCol
  · change (∫ t, t^(r-1)*(∫ ω, Y ω^k*Real.exp (-t*Y ω) ∂μ) ∂ν) = _
    calc
      _ = ∫ t, ∫ ω, F (ω,t) ∂μ ∂ν := by simp_rw [hCol]
      _ = ∫ a, F a ∂μ.prod ν := (integral_prod_symm F hFI).symm
      _ = ∫ ω, ∫ t, F (ω,t) ∂ν ∂μ := integral_prod F hFI
      _ = _ := by rw [integral_congr_ae hRow,integral_const_mul]

end ACS12.NativeCells


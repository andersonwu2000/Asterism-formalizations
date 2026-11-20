import ACS12.MellinFarBound
import ACS12.JointLaplaceDerivativeBound
import ACS12.HolomorphicDominatedIntegral
import ACS12.SquareRootExponentialTail

/-! Differentiated Laplace integrals are holomorphic on their full paid strips. -/
namespace ACS12.NativeCells
open MeasureTheory Set Filter Metric
open scoped Topology
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable def jointDifferentiatedExponent (α : ℂ) : ℂ := (α-2)/2

@[simp] theorem jointDifferentiatedExponent_re (α : ℂ) :
    (jointDifferentiatedExponent α).re = (α.re-2)/2 := by
  simp [jointDifferentiatedExponent,Complex.div_re]
  <;> ring

noncomputable def jointDifferentiatedKernel (z : ℝ) (k : ℕ) (α : ℂ) (t : ℝ) : ℂ :=
  (t:ℂ)^((k:ℂ)-jointDifferentiatedExponent α-1)*iteratedDeriv k (jointLaplaceCarrier α z) (t:ℂ)

noncomputable def jointDifferentiatedIntegral (z : ℝ) (k : ℕ) (α : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0, jointDifferentiatedKernel z k α t

noncomputable def jointDifferentiatedMoment (z : ℝ) (k : ℕ) (α : ℂ) : ℂ :=
  (-1:ℂ)^k/Complex.Gamma ((k:ℂ)-jointDifferentiatedExponent α)*jointDifferentiatedIntegral z k α

theorem jointDifferentiatedKernel_analytic {z t : ℝ} (hz : 0 ≤ z) (ht : 0 < t) (k : ℕ) (α : ℂ) :
    AnalyticAt ℂ (fun a => jointDifferentiatedKernel z k a t) α := by
  have hWeight : AnalyticAt ℂ (fun a => (t:ℂ)^((k:ℂ)-jointDifferentiatedExponent a-1)) α := by
    have hEq : (fun a => (t:ℂ)^((k:ℂ)-jointDifferentiatedExponent a-1)) =
        (fun a => Complex.exp (Complex.log (t:ℂ)*((k:ℂ)-jointDifferentiatedExponent a-1))) := by
      funext a
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne')]
    rw [hEq]
    unfold jointDifferentiatedExponent
    fun_prop
  exact hWeight.mul (jointLaplaceDerivative_shape_analytic hz ht k α)

theorem jointDifferentiatedKernel_aestronglyMeasurable {z : ℝ} (hz : 0 ≤ z) (k : ℕ) (α : ℂ) :
    AEStronglyMeasurable (jointDifferentiatedKernel z k α) (volume.restrict (Ioi 0)) := by
  have hWeight : Measurable (fun t : ℝ => (t:ℂ)^((k:ℂ)-jointDifferentiatedExponent α-1)) := by fun_prop
  exact hWeight.aestronglyMeasurable.mul
    ((jointLaplaceDerivative_continuousOn hz k α).aestronglyMeasurable measurableSet_Ioi)

theorem jointDifferentiatedIntegral_differentiableAt {z : ℝ} {α₀ : ℂ} (hz : 0 ≤ z)
    (hα : 0 < α₀.re) (k : ℕ) (hStrip : (jointDifferentiatedExponent α₀).re < (k:ℝ)) :
    DifferentiableAt ℂ (jointDifferentiatedIntegral z k) α₀ := by
  let ε := α₀.re/2
  let M := ‖α₀‖+1
  let B := ((jointDifferentiatedExponent α₀).re+(k:ℝ))/2
  let R := min 1 (min (α₀.re/2) ((k:ℝ)-(jointDifferentiatedExponent α₀).re))
  have hε : 0 < ε := half_pos hα
  have hR : 0 < R := lt_min zero_lt_one (lt_min hε (sub_pos.mpr hStrip))
  have hB : B < (k:ℝ) := by dsimp [B]; linarith only [hStrip]
  have hDomain (a : ℂ) (ha : a ∈ closedBall α₀ R) : ε ≤ a.re ∧ ‖a‖ ≤ M ∧
      (jointDifferentiatedExponent a).re ≤ B := by
    have hNorm : ‖a-α₀‖ ≤ R := by simpa only [mem_closedBall,dist_eq_norm] using ha
    have hRe := (Complex.abs_re_le_norm (a-α₀)).trans hNorm
    simp only [Complex.sub_re] at hRe
    have hR₁ : R ≤ 1 := min_le_left _ _
    have hRα : R ≤ α₀.re/2 := (min_le_right _ _).trans (min_le_left _ _)
    have hRβ : R ≤ (k:ℝ)-(jointDifferentiatedExponent α₀).re :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hLo := (abs_le.mp hRe).1
    have hHi := (abs_le.mp hRe).2
    refine ⟨by dsimp [ε]; linarith only [hLo,hRα],?_,?_⟩
    · calc
        ‖a‖ = ‖α₀+(a-α₀)‖ := by congr 1; ring
        _ ≤ ‖α₀‖+‖a-α₀‖ := norm_add_le _ _
        _ ≤ M := add_le_add_right (hNorm.trans hR₁) _
    · dsimp [B]
      rw [jointDifferentiatedExponent_re,jointDifferentiatedExponent_re]
      rw [jointDifferentiatedExponent_re] at hRβ
      linarith only [hHi,hRβ]
  obtain ⟨C,hC,hDerivative⟩ := jointLaplaceDerivative_uniform_bound (M:=M) hz hε k
  let G (t : ℝ) := if t ≤ 1 then C*t^((k:ℝ)-B-1) else
    (C*mellinFarConstant ε)*(t^((k:ℝ)+ε/2)*Real.exp (-(ε/2)*Real.sqrt t))
  have hNear : IntegrableOn G (Ioo 0 1) := by
    have hP : IntegrableOn (fun t : ℝ => t^((k:ℝ)-B-1)) (Ioo 0 1) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (by linarith only [hB])
    apply (hP.const_mul C).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [G,if_pos ht.2.le]
  have hFar : IntegrableOn G (Ioi 1) := by
    have hP := (integrableOn_rpow_exp_neg_sqrt (q:=(k:ℝ)+ε/2) (half_pos hε)).const_mul (C*mellinFarConstant ε)
    apply hP.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [G,if_neg (not_le.mpr (show 1 < t from ht))]
  have hG : IntegrableOn G (Ioi 0) := by
    rw [←Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ)≤1),integrableOn_union]
    exact ⟨(integrableOn_Ioc_iff_integrableOn_Ioo (μ:=volume)).mpr hNear,hFar⟩
  apply differentiableAt_integral_of_holomorphic_dominated hR
    (fun a => jointDifferentiatedKernel_aestronglyMeasurable hz k a) hG
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro a _
    exact (jointDifferentiatedKernel_analytic hz ht k a).differentiableAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro a ha
    have ht₀ : 0 < t := ht
    obtain ⟨haRe,haNorm,haB⟩ := hDomain a ha
    have hD := hDerivative a haRe haNorm t ht₀
    have hPhi := mellinPhi_pos ht₀
    have hPhi₁ := mellinPhi_le_one ht₀
    have hNorm : ‖jointDifferentiatedKernel z k a t‖ =
        t^((k:ℝ)-(jointDifferentiatedExponent a).re-1)*
          ‖iteratedDeriv k (jointLaplaceCarrier a z) (t:ℂ)‖ := by
      unfold jointDifferentiatedKernel
      rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ht₀]
      simp only [Complex.sub_re,Complex.natCast_re,Complex.one_re]
    rw [hNorm]
    by_cases ht₁ : t ≤ 1
    · have hWeight : t^((k:ℝ)-(jointDifferentiatedExponent a).re-1) ≤ t^((k:ℝ)-B-1) :=
        Real.rpow_le_rpow_of_exponent_ge ht₀ ht₁ (by linarith only [haB])
      have hD₀ : ‖iteratedDeriv k (jointLaplaceCarrier a z) (t:ℂ)‖ ≤ C :=
        hD.trans (mul_le_of_le_one_right hC.le (Real.rpow_le_one hPhi.le hPhi₁ hε.le))
      dsimp [G]
      rw [if_pos ht₁]
      exact (mul_le_mul hWeight hD₀ (norm_nonneg _) (Real.rpow_nonneg ht₀.le _)).trans_eq (mul_comm _ _)
    · have htBig : 1 ≤ t := (lt_of_not_ge ht₁).le
      have haPos : 0 < a.re := hε.trans_le haRe
      have hWeight : t^((k:ℝ)-(jointDifferentiatedExponent a).re-1) ≤ t^(k:ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le htBig
        rw [jointDifferentiatedExponent_re]
        linarith only [haPos]
      have hDP := hD.trans (mul_le_mul_of_nonneg_left (mellinPhi_rpow_tail hε htBig) hC.le)
      have hPaid := mul_le_mul hWeight hDP (norm_nonneg _) (Real.rpow_nonneg ht₀.le _)
      have hEq : t^(k:ℝ)*(C*(mellinFarConstant ε*t^(ε/2)*Real.exp (-(ε/2)*Real.sqrt t))) =
          (C*mellinFarConstant ε)*(t^((k:ℝ)+ε/2)*Real.exp (-(ε/2)*Real.sqrt t)) := by
        rw [Real.rpow_add ht₀]
        ring
      rw [hEq] at hPaid
      dsimp [G]
      rw [if_neg ht₁]
      exact hPaid

theorem jointDifferentiatedIntegral_analytic {z : ℝ} {α : ℂ} (hz : 0 ≤ z) (hα : 0 < α.re)
    (k : ℕ) (hStrip : (jointDifferentiatedExponent α).re < (k:ℝ)) :
    AnalyticAt ℂ (jointDifferentiatedIntegral z k) α := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  have hOpen : IsOpen {a : ℂ | 0 < a.re ∧ (jointDifferentiatedExponent a).re < (k:ℝ)} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt (show Continuous (fun a : ℂ => (jointDifferentiatedExponent a).re) by unfold jointDifferentiatedExponent; fun_prop) continuous_const)
  filter_upwards [hOpen.mem_nhds ⟨hα,hStrip⟩] with a ha
  exact jointDifferentiatedIntegral_differentiableAt hz ha.1 k ha.2

end ACS12.NativeCells

import ACS12.GammaMixture
import ACS12.PowerSine

/-! Fractional powers from the complete positive Laplace deficit. -/
namespace ACS12.GammaMixture

open MeasureTheory Set Filter
open GammaDeficit (gamma_exp_integral integrable_gamma_exp)

private theorem exp_deficit_eq_integral {x s : ℝ} (hx : 0 ≤ x) (hs : 0 < s) :
    1 - Real.exp (-s * x) = s * ∫ t : ℝ in Ioc 0 x, Real.exp (-s * t) := by
  have hD (t : ℝ) : HasDerivAt (fun u : ℝ => Real.exp (-s * u) / (-s)) (Real.exp (-s * t)) t := by
    convert (((hasDerivAt_id t).const_mul (-s)).exp.div_const (-s)) using 1
    simp only [id_eq,mul_one]
    field_simp [hs.ne']
  rw [← intervalIntegral.integral_of_le hx,intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hD t) (by apply Continuous.intervalIntegrable; fun_prop),mul_zero,Real.exp_zero]
  field_simp [hs.ne']
  ring

theorem fractionalLaplaceDeficit {h x : ℝ} (hh : 0 < h) (hh₁ : h < 1) (hx : 0 ≤ x) :
    IntegrableOn (fun s => s ^ (-h - 1) * (1 - Real.exp (-s * x))) (Ioi 0) ∧
    (∫ s : ℝ in Ioi 0, s ^ (-h - 1) * (1 - Real.exp (-s * x))) =
      (Real.Gamma (1 - h) / h) * x ^ h := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  let ν := volume.restrict (Ioc 0 x)
  let F (z : ℝ × ℝ) := z.1 ^ (-h) * Real.exp (-z.2 * z.1)
  have hM : Measurable F := by unfold F; fun_prop
  have hh' : 0 < 1 - h := sub_pos.mpr hh₁
  have hR (t : ℝ) (ht : 0 < t) :
      (∫ s : ℝ, F (s,t) ∂μ) = Real.Gamma (1 - h) * t ^ (h - 1) := by
    dsimp only [F,μ]
    simpa only [sub_sub_cancel_left,neg_sub] using gamma_exp_integral hh' ht
  have hP : Integrable (fun t : ℝ => t ^ (h - 1)) ν := by
    have hI : IntervalIntegrable (fun t : ℝ => t ^ (h - 1)) volume 0 x :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith only [hh])
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le hx] at hI
  have hI : Integrable F (μ.prod ν) := by
    apply (integrable_prod_iff' hM.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      simpa only [F,μ,sub_sub_cancel_left] using integrable_gamma_exp hh' ht.1
    · apply (hP.const_mul (Real.Gamma (1 - h))).congr
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [← hR t ht.1]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact (Real.norm_of_nonneg (show 0 ≤ F (s,t) by exact mul_nonneg (Real.rpow_nonneg (show 0 < s from hs).le _) (Real.exp_pos _).le)).symm
  have hRow (s : ℝ) (hs : 0 < s) :
      (∫ t : ℝ, F (s,t) ∂ν) = s ^ (-h - 1) * (1 - Real.exp (-s * x)) := by
    dsimp only [F,ν]
    simp_rw [show ∀ t : ℝ, -t * s = -s * t from fun t => by ring]
    rw [integral_const_mul,exp_deficit_eq_integral hx hs,← mul_assoc,
      ← Real.rpow_add_one hs.ne']
    rw [show -h - 1 + 1 = -h by ring]
  have hInt : (∫ t : ℝ, t ^ (h - 1) ∂ν) = x ^ h / h := by
    change (∫ t : ℝ in Ioc 0 x, t ^ (h - 1)) = _
    rw [← intervalIntegral.integral_of_le hx,integral_rpow (Or.inl (by linarith only [hh])),
      sub_add_cancel,Real.zero_rpow hh.ne',sub_zero]
  have hRowAE : ∀ᵐ s ∂μ, (∫ t : ℝ, F (s,t) ∂ν) =
      s ^ (-h - 1) * (1 - Real.exp (-s * x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact hRow s hs
  refine ⟨hI.integral_prod_left.congr hRowAE,?_⟩
  calc
    _ = ∫ s : ℝ, (∫ t : ℝ, F (s,t) ∂ν) ∂μ := (integral_congr_ae hRowAE).symm
    _ = ∫ z, F z ∂μ.prod ν := (integral_prod F hI).symm
    _ = ∫ t : ℝ, (∫ s : ℝ, F (s,t) ∂μ) ∂ν := integral_prod_symm F hI
    _ = ∫ t : ℝ, Real.Gamma (1 - h) * t ^ (h - 1) ∂ν := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hR t ht.1
    _ = _ := by rw [integral_const_mul,hInt]; ring


theorem fractionalMoment_eq_laplace {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    (hI : Integrable X μ) (hNonneg : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    {h : ℝ} (hh : 0 < h) (hh₁ : h < 1) :
    let K (s : ℝ) := s ^ (-h - 1) * (1 - ∫ ω, Real.exp (-s * X ω) ∂μ)
    IntegrableOn K (Ioi 0) ∧
      (∫ ω, X ω ^ h ∂μ) = (h / Real.Gamma (1 - h)) * ∫ s : ℝ in Ioi 0, K s := by
  let ν := volume.restrict (Ioi (0 : ℝ))
  let F (z : Ω × ℝ) := z.2 ^ (-h - 1) * (1 - Real.exp (-z.2 * X z.1))
  let K (s : ℝ) := s ^ (-h - 1) * (1 - ∫ ω, Real.exp (-s * X ω) ∂μ)
  have hM : Measurable F := by unfold F; fun_prop
  have hV (x : ℝ) (hx : 0 ≤ x) : x ^ h ≤ 1 + x := by
    by_cases h' : x ≤ 1
    · exact ((Real.rpow_le_one hx h' hh.le)).trans (by linarith only [hx])
    · have hU := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge h') hh₁.le
      rw [Real.rpow_one] at hU
      linarith only [hU]
  have hP : Integrable (fun ω => X ω ^ h) μ := by
    have hMX : Measurable (fun ω => X ω ^ h) := by fun_prop
    apply ((integrable_const 1).add hI).mono' hMX.aestronglyMeasurable
    filter_upwards [hNonneg] with ω hω
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hω _)]
    exact hV _ hω
  have hFI : Integrable F (μ.prod ν) := by
    apply (integrable_prod_iff hM.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [hNonneg] with ω hω
      exact (fractionalLaplaceDeficit hh hh₁ hω).1
    · apply (hP.const_mul (Real.Gamma (1 - h) / h)).congr
      filter_upwards [hNonneg] with ω hω
      rw [← (fractionalLaplaceDeficit hh hh₁ hω).2]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hE := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (show 0 ≤ s from hs.le)) hω)
      exact (Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hs.le _) (sub_nonneg.mpr hE))).symm
  have hExp (s : ℝ) (hs : 0 < s) : Integrable (fun ω => Real.exp (-s * X ω)) μ := by
    apply (integrable_const 1).mono' (by fun_prop : Measurable (fun ω => Real.exp (-s * X ω))).aestronglyMeasurable
    filter_upwards [hNonneg] with ω hω
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) hω)
  have hCol : ∀ᵐ s ∂ν, (∫ ω, F (ω,s) ∂μ) = K s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    dsimp only [F,K]
    rw [integral_const_mul,integral_sub (integrable_const 1) (hExp s hs),integral_const]
    simp
  have hRow : ∀ᵐ ω ∂μ, (∫ s : ℝ, F (ω,s) ∂ν) = (Real.Gamma (1 - h) / h) * X ω ^ h := by
    filter_upwards [hNonneg] with ω hω
    exact (fractionalLaplaceDeficit hh hh₁ hω).2
  have hInt : (∫ s : ℝ, K s ∂ν) = (Real.Gamma (1 - h) / h) * ∫ ω, X ω ^ h ∂μ := by
    calc
      _ = ∫ s : ℝ, (∫ ω, F (ω,s) ∂μ) ∂ν := (integral_congr_ae hCol).symm
      _ = ∫ z, F z ∂μ.prod ν := (integral_prod_symm F hFI).symm
      _ = ∫ ω, (∫ s : ℝ, F (ω,s) ∂ν) ∂μ := integral_prod F hFI
      _ = _ := by rw [integral_congr_ae hRow,integral_const_mul]
  refine ⟨hFI.integral_prod_right.congr hCol,?_⟩
  change (∫ ω, X ω ^ h ∂μ) = (h / Real.Gamma (1 - h)) * ∫ s : ℝ, K s ∂ν
  rw [hInt,← mul_assoc,div_mul_div_comm,mul_comm (Real.Gamma (1 - h)),div_self,one_mul]
  exact mul_ne_zero hh.ne' (Real.Gamma_pos_of_pos (sub_pos.mpr hh₁)).ne'

end ACS12.GammaMixture

import ACS12.NativeProbabilityCore

/-! Ordinary negative moments are positive-kernel Mellin integrals, with finiteness paid by the actual Laplace kernel. -/
namespace ACS12
open MeasureTheory Set Filter
open GammaDeficit (gamma_exp_integral integrable_gamma_exp)

theorem negativeMoment_eq_laplace {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    (hPos : ∀ᵐ ω ∂μ, 0 < X ω) {r : ℝ} (hr : 0 < r)
    (hK : IntegrableOn (fun t => t^(r-1)*(∫ ω, Real.exp (-t*X ω) ∂μ)) (Ioi 0)) :
    Integrable (fun ω => X ω^(-r)) μ ∧
      (∫ ω, X ω^(-r) ∂μ) =
        (Real.Gamma r)⁻¹ * ∫ t : ℝ in Ioi 0, t^(r-1)*(∫ ω, Real.exp (-t*X ω) ∂μ) := by
  let ν := volume.restrict (Ioi (0:ℝ))
  let F (a : Ω × ℝ) := a.2^(r-1)*Real.exp (-a.2*X a.1)
  have hM : Measurable F := by unfold F; fun_prop
  have hColI (t : ℝ) (ht : 0 < t) : Integrable (fun ω => F (ω,t)) μ := by
    apply (integrable_const (μ := μ) (t^(r-1))).mono' (by unfold F; fun_prop)
    filter_upwards [hPos] with ω hω
    unfold F
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_of_le_one_right (Real.rpow_nonneg ht.le _)
      (Real.exp_le_one_iff.mpr (by nlinarith only [ht,hω]))
  have hCol (t : ℝ) : (∫ ω, F (ω,t) ∂μ) = t^(r-1)*(∫ ω, Real.exp (-t*X ω) ∂μ) := by
    dsimp only [F]
    rw [integral_const_mul]
  have hFI : Integrable F (μ.prod ν) := by
    apply (integrable_prod_iff' hM.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hColI t ht
    · apply hK.congr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [← hCol]
      apply integral_congr_ae
      exact Eventually.of_forall fun ω => (Real.norm_of_nonneg (by
        dsimp only [F]
        exact mul_nonneg (Real.rpow_nonneg (show 0 ≤ t from ht.le) _) (Real.exp_pos _).le)).symm
  have hRow : ∀ᵐ ω ∂μ, (∫ t, F (ω,t) ∂ν) = Real.Gamma r * X ω^(-r) := by
    filter_upwards [hPos] with ω hω
    dsimp only [F,ν]
    calc
      _ = ∫ t : ℝ in Ioi 0, t^(r-1)*Real.exp (-X ω*t) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t _
        dsimp only
        rw [show -t*X ω = -X ω*t by ring]
      _ = _ := gamma_exp_integral hr hω
  have hRowI := hFI.integral_prod_left
  have hPower : Integrable (fun ω => X ω^(-r)) μ := by
    have h := (hRowI.congr hRow).const_mul (Real.Gamma r)⁻¹
    apply h.congr
    exact Eventually.of_forall fun ω => by
      simp only [← mul_assoc,inv_mul_cancel₀ (Real.Gamma_pos_of_pos hr).ne',one_mul]
  refine ⟨hPower,?_⟩
  have hInt : Real.Gamma r * (∫ ω, X ω^(-r) ∂μ) =
      ∫ t : ℝ in Ioi 0, t^(r-1)*(∫ ω, Real.exp (-t*X ω) ∂μ) := by
    calc
      _ = ∫ ω, ∫ t, F (ω,t) ∂ν ∂μ := by rw [integral_congr_ae hRow,integral_const_mul]
      _ = ∫ a, F a ∂μ.prod ν := (integral_prod F hFI).symm
      _ = ∫ t, ∫ ω, F (ω,t) ∂μ ∂ν := integral_prod_symm F hFI
      _ = _ := by simp_rw [hCol]; rfl
  rw [← hInt,← mul_assoc,inv_mul_cancel₀ (Real.Gamma_pos_of_pos hr).ne',one_mul]

end ACS12

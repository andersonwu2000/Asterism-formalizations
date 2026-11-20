import Mathlib.Probability.Distributions.Gamma
import ACS12.PowerSine

/-! Generic Gamma density integration and its exact exponential moment on the full rate domain. -/
namespace ACS12.GammaDistribution
open MeasureTheory ProbabilityTheory Set Filter

theorem integral_gammaMeasure_eq {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (f : ℝ → ℝ) :
    (∫ x, f x ∂gammaMeasure a r) =
      ∫ x : ℝ in Ioi 0, (r^a/Real.Gamma a*x^(a-1)*Real.exp (-(r*x)))*f x := by
  have hM : Measurable (gammaPDF a r) := (measurable_gammaPDFReal a r).ennreal_ofReal
  unfold gammaMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hM
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) f,
    ← integral_Ici_eq_integral_Ioi,← integral_indicator measurableSet_Ici]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [gammaPDF,ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x),smul_eq_mul]
    by_cases hx : 0 ≤ x
    · simp [gammaPDFReal,hx,indicator_of_mem]
    · simp [gammaPDFReal,hx,indicator_of_notMem]

theorem gammaMeasure_exponential {a r c : ℝ} (ha : 0 < a) (hr : 0 < r) (hc : c < r) :
    Integrable (fun x => Real.exp (c*x)) (gammaMeasure a r) ∧
      (∫ x, Real.exp (c*x) ∂gammaMeasure a r) = (r/(r-c))^a := by
  have hrc := sub_pos.mpr hc
  have hE : (∫ x, Real.exp (c*x) ∂gammaMeasure a r) = (r/(r-c))^a := by
    rw [integral_gammaMeasure_eq ha hr]
    have hPoint (x : ℝ) :
        (r^a/Real.Gamma a*x^(a-1)*Real.exp (-(r*x)))*Real.exp (c*x) =
          (r^a/Real.Gamma a)*(x^(a-1)*Real.exp (-(r-c)*x)) := by
      rw [mul_assoc (r^a/Real.Gamma a*x^(a-1)),← Real.exp_add]
      rw [show -(r*x)+c*x = -(r-c)*x by ring]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => hPoint x),integral_const_mul,
      GammaDeficit.gamma_exp_integral ha hrc,Real.div_rpow hr.le hrc.le,Real.rpow_neg hrc.le]
    field_simp [(Real.Gamma_pos_of_pos ha).ne']
  exact ⟨Integrable.of_integral_ne_zero (hE ▸ (Real.rpow_pos_of_pos (div_pos hr hrc) a).ne'),hE⟩

end ACS12.GammaDistribution

import ACS12.GammaTotalExponential
import Mathlib.Probability.Moments.ComplexMGF

/-! The paid exponential moments give the actual Gamma-product Laplace transform its analytic origin germ. -/
namespace ACS12.GammaMixture
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

theorem gammaTotal_integrableExpSet {a c : ℝ} (ha : 0 < a) (hc : c < gammaRate 0) :
    c ∈ integrableExpSet gammaTotal (gammaProduct a) := by
  letI := gammaProduct_probability ha
  by_cases hc₀ : 0 ≤ c
  · exact gammaTotal_exponential_integrable ha hc₀ hc
  · apply (integrable_const (μ := gammaProduct a) (1:ℝ)).mono'
      ((measurable_gammaTotal.const_mul c).exp.aestronglyMeasurable)
    exact Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (le_of_not_ge hc₀) ENNReal.toReal_nonneg)

theorem gammaTotal_mgf_interior {a c : ℝ} (ha : 0 < a) (hc : c < gammaRate 0) :
    c ∈ interior (integrableExpSet gammaTotal (gammaProduct a)) := by
  have hSubset : Iio (gammaRate 0) ⊆ integrableExpSet gammaTotal (gammaProduct a) :=
    fun _ h => gammaTotal_integrableExpSet ha h
  exact interior_maximal hSubset isOpen_Iio hc

theorem gammaTotal_complexMGF_analytic {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : z.re < gammaRate 0) :
    AnalyticAt ℂ (complexMGF gammaTotal (gammaProduct a)) z :=
  analyticAt_complexMGF (gammaTotal_mgf_interior ha hz)

noncomputable def gammaLaplaceGerm (a : ℝ) (z : ℂ) : ℂ :=
  complexMGF gammaTotal (gammaProduct a) (-z)

theorem gammaLaplaceGerm_zero {a : ℝ} (ha : 0 < a) : gammaLaplaceGerm a 0 = 1 := by
  letI := gammaProduct_probability ha
  unfold gammaLaplaceGerm
  rw [neg_zero,show (0:ℂ) = ((0:ℝ):ℂ) by rfl,complexMGF_ofReal,mgf_zero]
  rfl

theorem gammaLaplaceGerm_analytic {a : ℝ} (ha : 0 < a) :
    AnalyticAt ℂ (gammaLaplaceGerm a) 0 := by
  have h := gammaTotal_complexMGF_analytic ha (z := 0) (by simpa using gammaRate_pos 0)
  have h' : AnalyticAt ℂ (fun z : ℂ => -z) 0 := by fun_prop
  exact h.comp_of_eq h' (by simp)

theorem gammaLaplaceGerm_real {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    gammaLaplaceGerm a (t^2:ℝ) =
      (((t/(2*Real.sinh (t/2)))^a:ℝ):ℂ) := by
  unfold gammaLaplaceGerm
  rw [← Complex.ofReal_neg,complexMGF_ofReal]
  unfold mgf
  rw [gammaTotal_laplace ha ht]

end ACS12.GammaMixture

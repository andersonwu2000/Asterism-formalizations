import ACS12.GammaProductExponentialBound
import ACS12.FiniteIntegralLimit

/-! The complete actual Gamma sum inherits each positive exponential moment below the first rate. -/
namespace ACS12.GammaMixture
open MeasureTheory Filter
open scoped Topology

theorem gammaTotal_exponential_integrable {a c : ℝ} (ha : 0 < a)
    (hc₀ : 0 ≤ c) (hc : c < gammaRate 0) :
    Integrable (fun ω => Real.exp (c*gammaTotal ω)) (gammaProduct a) := by
  let F (n : ℕ) (ω : ℕ → ℝ) := Real.exp (c*gammaPartialTotal n ω)
  have hF (n : ℕ) : Integrable (F n) (gammaProduct a) := (gammaPartial_exponential ha hc n).1
  have hf : Measurable (fun ω => Real.exp (c*gammaTotal ω)) :=
    (measurable_gammaTotal.const_mul c).exp
  have hlim : ∀ᵐ ω ∂gammaProduct a,
      Tendsto (fun n => F n ω) atTop (nhds (Real.exp (c*gammaTotal ω))) := by
    filter_upwards [gammaProduct_ae_hasSum ha] with ω hω
    exact (Real.continuous_exp.tendsto _).comp (hω.tendsto_sum_nat.const_mul c)
  have hBound (n : ℕ) :
      (∫ ω, ‖F n ω‖ ∂gammaProduct a) ≤ Real.exp ((a*(gammaRate 0/(gammaRate 0-c))*c)/24) := by
    have hEq : (∫ ω, ‖F n ω‖ ∂gammaProduct a) = ∫ ω, F n ω ∂gammaProduct a :=
      integral_congr_ae (Eventually.of_forall fun ω => Real.norm_of_nonneg (Real.exp_pos _).le)
    rw [hEq]
    exact gammaPartial_exponential_bound ha hc₀ hc n
  exact integrable_of_ae_tendsto_bounded_integrals hF hf.aestronglyMeasurable hlim hBound

end ACS12.GammaMixture

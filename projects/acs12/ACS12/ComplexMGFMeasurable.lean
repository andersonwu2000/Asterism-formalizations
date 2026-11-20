import Mathlib.Probability.Moments.ComplexMGF

/-! Global parameter measurability of the ordinary complex MGF. -/
namespace ACS12
open MeasureTheory ProbabilityTheory

theorem measurable_complexMGF {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
    {X : Ω → ℝ} (hX : Measurable X) : Measurable (complexMGF X μ) := by
  have hXC : Measurable (fun ω => (X ω:ℂ)) := Complex.continuous_ofReal.measurable.comp hX
  have hM : Measurable (fun a : ℂ × Ω => Complex.exp (a.1*(X a.2:ℂ))) :=
    Complex.continuous_exp.measurable.comp (measurable_fst.mul (hXC.comp measurable_snd))
  exact hM.stronglyMeasurable.integral_prod_right'.measurable

end ACS12

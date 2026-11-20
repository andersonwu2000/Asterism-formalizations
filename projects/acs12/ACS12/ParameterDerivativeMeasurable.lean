import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic

/-! A parameter derivative is measurable as the actual limit of measurable difference quotients. -/
namespace ACS12
open MeasureTheory Filter Set
open scoped Topology

theorem aestronglyMeasurable_parameter_deriv {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {F : ℂ → Ω → ℂ} {x : ℂ} (hM : ∀ z, AEStronglyMeasurable (F z) μ)
    (hD : ∀ᵐ ω ∂μ, DifferentiableAt ℂ (fun z => F z ω) x) :
    AEStronglyMeasurable (fun ω => deriv (fun z => F z ω) x) μ := by
  let q (n : ℕ) : ℂ := 1/((n:ℂ)+1)
  let Q (n : ℕ) (ω : Ω) := (q n)⁻¹ • (F (x+q n) ω-F x ω)
  have hQ (n : ℕ) : AEStronglyMeasurable (Q n) μ := by
    simpa only [Q,Pi.sub_apply,Pi.smul_apply] using
      ((hM (x+q n)).sub (hM x)).const_smul ((q n)⁻¹)
  have hq : Tendsto q atTop (𝓝[≠] (0:ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
    · apply Eventually.of_forall
      intro n
      change q n ≠ 0
      unfold q
      apply one_div_ne_zero
      intro he
      have h := congrArg Complex.re he
      simp only [Complex.add_re,Complex.natCast_re,Complex.one_re,Complex.zero_re] at h
      linarith [Nat.cast_nonneg (α := ℝ) n]
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => Q n ω) atTop
      (nhds (deriv (fun z => F z ω) x)) := by
    filter_upwards [hD] with ω hω
    exact hω.hasDerivAt.tendsto_slope_zero.comp hq
  exact aestronglyMeasurable_of_tendsto_ae atTop hQ hlim

end ACS12

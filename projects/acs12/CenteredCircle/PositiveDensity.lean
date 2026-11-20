import CenteredCircle.PowerDecay
import Mathlib.Tactic.FunProp

/-! Positive densities dominated by a quadratic give summable Laplace kernels. -/

namespace CenteredCircle.AllN

open MeasureTheory Filter Set
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

noncomputable def densityMeasure (g : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun u => ENNReal.ofReal (g u))

theorem densityMeasure_positive_support (g : ℝ → ℝ) (hg : Measurable g) :
    ∀ᵐ u ∂densityMeasure g, 0 < u := by
  have hweight : Measurable (fun u => ENNReal.ofReal (g u)) := ENNReal.measurable_ofReal.comp hg
  apply (ae_withDensity_iff (μ := volume.restrict (Ioi (0 : ℝ))) hweight).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  intro _
  exact hu

theorem densityMeasure_ne_zero (g : ℝ → ℝ) (hg : Measurable g)
    (hpos : ∀ u, 0 < u → 0 < g u) : densityMeasure g ≠ 0 := by
  haveI : NeZero (volume.restrict (Ioi (0 : ℝ))) := ⟨by
    intro hz
    have hm := congrArg (fun ν : Measure ℝ => ν univ) hz
    simpa using hm⟩
  intro hz
  have hae := (withDensity_eq_zero_iff
    (ENNReal.measurable_ofReal.comp hg).aemeasurable).mp hz
  obtain ⟨u, hu, heq⟩ := ((ae_restrict_mem measurableSet_Ioi).and hae).exists
  have hgt : 0 < ENNReal.ofReal (g u) := ENNReal.ofReal_pos.mpr (hpos u hu)
  exact hgt.ne' heq

theorem laplace_density_integral (g : ℝ → ℝ) (hg : Measurable g)
    (hg0 : ∀ u, 0 < u → 0 ≤ g u) (t : ℝ) :
    laplaceKernel (densityMeasure g) t =
      ∫ u : ℝ in Ioi 0, g u * Real.exp (-u * t) := by
  unfold laplaceKernel densityMeasure
  have hweight : Measurable (fun u => ENNReal.ofReal (g u)) := ENNReal.measurable_ofReal.comp hg
  rw [integral_withDensity_eq_integral_toReal_smul
    (μ := volume.restrict (Ioi (0 : ℝ))) hweight
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [ENNReal.toReal_ofReal (hg0 u hu), smul_eq_mul]

theorem integrable_weighted_exponential (g : ℝ → ℝ) (C t : ℝ)
    (hg : Measurable g) (hg0 : ∀ u, 0 < u → 0 ≤ g u)
    (hbound : ∀ u, 0 < u → g u ≤ C * u ^ 2) (ht : 0 < t) :
    IntegrableOn (fun u => g u * Real.exp (-u * t)) (Ioi 0) := by
  have hexp : Measurable (fun u : ℝ => Real.exp (-u * t)) := by fun_prop
  apply ((integrable_power_exponential 2 t ht).const_mul C).mono'
    (hg.mul hexp).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hg0 u hu) (Real.exp_pos _).le)]
  calc
    g u * Real.exp (-u * t) ≤ (C * u ^ 2) * Real.exp (-u * t) :=
      mul_le_mul_of_nonneg_right (hbound u hu) (Real.exp_pos _).le
    _ = C * (u ^ 2 * Real.exp (-u * t)) := by ring

theorem integrable_exp_density (g : ℝ → ℝ) (C t : ℝ)
    (hg : Measurable g) (hg0 : ∀ u, 0 < u → 0 ≤ g u)
    (hbound : ∀ u, 0 < u → g u ≤ C * u ^ 2) (ht : 0 < t) :
    Integrable (fun u => Real.exp (-u * t)) (densityMeasure g) := by
  have hweight : Measurable (fun u => ENNReal.ofReal (g u)) := ENNReal.measurable_ofReal.comp hg
  rw [densityMeasure, integrable_withDensity_iff_integrable_smul'
    (μ := volume.restrict (Ioi (0 : ℝ))) hweight
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply (integrable_weighted_exponential g C t hg hg0 hbound ht).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [ENNReal.toReal_ofReal (hg0 u hu), smul_eq_mul]

theorem laplace_density_cubic_bound (g : ℝ → ℝ) (C t : ℝ)
    (hg : Measurable g) (hg0 : ∀ u, 0 < u → 0 ≤ g u)
    (hbound : ∀ u, 0 < u → g u ≤ C * u ^ 2) (ht : 0 < t) :
    laplaceKernel (densityMeasure g) t ≤ (2 * C) / t ^ 3 := by
  rw [laplace_density_integral g hg hg0 t]
  calc
    (∫ u : ℝ in Ioi 0, g u * Real.exp (-u * t)) ≤
        ∫ u : ℝ in Ioi 0, C * (u ^ 2 * Real.exp (-u * t)) := by
      apply integral_mono_ae (integrable_weighted_exponential g C t hg hg0 hbound ht)
        ((integrable_power_exponential 2 t ht).const_mul C)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hm := mul_le_mul_of_nonneg_right (hbound u hu) (Real.exp_pos (-u * t)).le
      simpa only [mul_assoc] using hm
    _ = (2 * C) / t ^ 3 := by
      rw [integral_const_mul, integral_power_exponential 2 t ht]
      norm_num
      ring

theorem summable_laplace_density (g : ℝ → ℝ) (C t s : ℝ)
    (hg : Measurable g) (hg0 : ∀ u, 0 < u → 0 ≤ g u)
    (hbound : ∀ u, 0 < u → g u ≤ C * u ^ 2)
    (hC : 0 ≤ C) (ht : 0 < t) (hs : 0 < s) :
    Summable (fun j : ℕ => laplaceKernel (densityMeasure g) (t + j * s)) := by
  apply summable_of_cubic_decay (laplaceKernel (densityMeasure g)) (2 * C) t s
    (by positivity) ht hs
  · intro x _
    exact integral_nonneg (fun u => (Real.exp_pos _).le)
  · intro x hx
    exact laplace_density_cubic_bound g C x hg hg0 hbound hx

end CenteredCircle.AllN

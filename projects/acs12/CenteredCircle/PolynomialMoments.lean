import CenteredCircle.KernelCalculus

/-! Exact Laplace moments of the A/B density polynomials. -/

namespace CenteredCircle.AllN

open MeasureTheory Set

theorem densityPolynomial_moment_integrable (kind : CircleKernelKind)
    (m : ℕ) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun u : ℝ => (u ^ m * densityPolynomial kind u) * Real.exp (-u * t))
      (Ioi 0) := by
  have hg : Measurable (fun u : ℝ => u ^ m * densityPolynomial kind u) :=
    (measurable_id.pow_const m).mul (continuous_densityPolynomial kind).measurable
  apply integrable_weighted_exponential_of_abs_bound _ (1 / 2) t (m + 2) hg _ ht
  intro u hu
  rw [abs_of_pos (mul_pos (pow_pos hu m) (densityPolynomial_pos kind hu))]
  calc
    u ^ m * densityPolynomial kind u ≤ u ^ m * (u ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (densityPolynomial_lt_quadratic kind hu).le (pow_pos hu m).le
    _ = (1 / 2 : ℝ) * u ^ (m + 2) := by rw [pow_add]; ring

theorem densityPolynomial_moment_pos (kind : CircleKernelKind)
    (m : ℕ) {t : ℝ} (ht : 0 < t) :
    0 < ∫ u : ℝ in Ioi 0, (u ^ m * densityPolynomial kind u) * Real.exp (-u * t) := by
  letI : NeZero (volume.restrict (Ioi (0 : ℝ))) := ⟨positiveHalfLine_ne_zero⟩
  have h := integral_strict_of_ae_lt (volume.restrict (Ioi (0 : ℝ)))
    (integrable_zero ℝ ℝ _) (densityPolynomial_moment_integrable kind m ht) ?_
  · simpa only [integral_zero] using h
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_pos (mul_pos (pow_pos hu m) (densityPolynomial_pos kind hu)) (Real.exp_pos _)

theorem integral_polyA_moment (m : ℕ) {t : ℝ} (ht : 0 < t) :
    (∫ u : ℝ in Ioi 0, (u ^ m * polyA u) * Real.exp (-u * t)) =
      (m.factorial : ℝ) / t ^ (m + 1) - (m.factorial : ℝ) / (t + 1) ^ (m + 1) -
        ((m + 1).factorial : ℝ) / (t + 1) ^ (m + 2) := by
  have ht1 : 0 < t + 1 := by linarith
  have h0 := integrable_power_exponential m t ht
  have h1 := integrable_power_exponential m (t + 1) ht1
  have h2 := integrable_power_exponential (m + 1) (t + 1) ht1
  have h01 : IntegrableOn (fun u : ℝ => u ^ m * Real.exp (-u * t) -
      u ^ m * Real.exp (-u * (t + 1))) (Ioi 0) := h0.sub h1
  have he : (∫ u : ℝ in Ioi 0, (u ^ m * polyA u) * Real.exp (-u * t)) =
      ∫ u : ℝ in Ioi 0, u ^ m * Real.exp (-u * t) -
        u ^ m * Real.exp (-u * (t + 1)) - u ^ (m + 1) * Real.exp (-u * (t + 1)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    have hexp : Real.exp (-u * (t + 1)) = Real.exp (-u) * Real.exp (-u * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    dsimp only
    rw [hexp, polyA, pow_succ]
    ring
  rw [he, integral_sub h01 h2, integral_sub h0 h1,
    integral_power_exponential m t ht, integral_power_exponential m (t + 1) ht1,
    integral_power_exponential (m + 1) (t + 1) ht1]

theorem integral_polyB_moment (m : ℕ) {t : ℝ} (ht : 0 < t) :
    (∫ u : ℝ in Ioi 0, (u ^ m * polyB u) * Real.exp (-u * t)) =
      ((m + 1).factorial : ℝ) / t ^ (m + 2) - (m.factorial : ℝ) / t ^ (m + 1) +
        (m.factorial : ℝ) / (t + 1) ^ (m + 1) := by
  have ht1 : 0 < t + 1 := by linarith
  have h0 := integrable_power_exponential (m + 1) t ht
  have h1 := integrable_power_exponential m t ht
  have h2 := integrable_power_exponential m (t + 1) ht1
  have h01 : IntegrableOn (fun u : ℝ => u ^ (m + 1) * Real.exp (-u * t) -
      u ^ m * Real.exp (-u * t)) (Ioi 0) := h0.sub h1
  have he : (∫ u : ℝ in Ioi 0, (u ^ m * polyB u) * Real.exp (-u * t)) =
      ∫ u : ℝ in Ioi 0, u ^ (m + 1) * Real.exp (-u * t) -
        u ^ m * Real.exp (-u * t) + u ^ m * Real.exp (-u * (t + 1)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    have hexp : Real.exp (-u * (t + 1)) = Real.exp (-u) * Real.exp (-u * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    dsimp only
    rw [hexp, polyB, pow_succ]
    ring
  rw [he, integral_add h01 h2, integral_sub h0 h1,
    integral_power_exponential (m + 1) t ht, integral_power_exponential m t ht,
    integral_power_exponential m (t + 1) ht1]

end CenteredCircle.AllN

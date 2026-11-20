import CenteredCircle.DensityRatios
import CenteredCircle.PolynomialMoments
import CenteredCircle.IntegralProductComparison

/-! The finite-circle A/B ratio, obtained from the actual Laplace densities. -/

namespace CenteredCircle.AllN

open MeasureTheory Set Filter

theorem circleKernel_eq_density_integral {L : ℝ} (hL : 0 < L)
    (kind : CircleKernelKind) (t : ℝ) :
    circleKernel L kind t =
      ∫ u : ℝ in Ioi 0, circleDensity L kind u * Real.exp (-u * t) :=
  laplace_density_integral (circleDensity L kind)
    (continuous_circleDensity L kind).measurable
    (fun u hu => (circleDensity_pos hL kind hu).le) t

theorem circleDensity_laplace_integrable {L t : ℝ} (hL : 0 < L) (ht : 0 < t)
    (kind : CircleKernelKind) :
    IntegrableOn (fun u : ℝ => circleDensity L kind u * Real.exp (-u * t)) (Ioi 0) := by
  apply integrable_weighted_exponential_of_abs_bound _ (1 / 2) t 2
    (continuous_circleDensity L kind).measurable _ ht
  intro u hu
  rw [abs_of_pos (circleDensity_pos hL kind hu)]
  exact circleDensity_quadratic_bound kind hu

theorem circleKernel_a_lt_b {L t : ℝ} (hL : 0 < L) (ht : 0 < t) :
    circleKernel L .a t < circleKernel L .b t := by
  letI : NeZero (volume.restrict (Ioi (0 : ℝ))) := ⟨positiveHalfLine_ne_zero⟩
  rw [circleKernel_eq_density_integral hL, circleKernel_eq_density_integral hL]
  apply integral_strict_of_ae_lt _ (circleDensity_laplace_integrable hL ht .a)
    (circleDensity_laplace_integrable hL ht .b)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact mul_lt_mul_of_pos_right
    (mul_lt_mul_of_pos_left (polyA_lt_polyB hu) (circleWeight_pos hL hu)) (Real.exp_pos _)

theorem density_comparison_pair {L t u v : ℝ} (hL : 0 < L)
    (hu : 0 < u) (hv : 0 < v) :
    0 ≤ (circleDensity L .a u * Real.exp (-u * t)) *
        ((v * polyB v) * Real.exp (-v * t)) +
      (circleDensity L .a v * Real.exp (-v * t)) *
        ((u * polyB u) * Real.exp (-u * t)) -
      ((u * polyA u) * Real.exp (-u * t)) *
        (circleDensity L .b v * Real.exp (-v * t)) -
      ((v * polyA v) * Real.exp (-v * t)) *
        (circleDensity L .b u * Real.exp (-u * t)) := by
  have hp : 0 ≤ (polyA u * polyB v - polyA v * polyB u) *
      (circleWeight L u * v - circleWeight L v * u) := by
    rcases le_total u v with huv | hvu
    · exact mul_nonneg (density_polynomial_cross_nonneg hu hv huv)
        (circle_weight_cross_nonneg hL hu hv huv)
    · have h := mul_nonneg (density_polynomial_cross_nonneg hv hu hvu)
        (circle_weight_cross_nonneg hL hv hu hvu)
      nlinarith
  have h := mul_nonneg (mul_pos (Real.exp_pos (-u * t)) (Real.exp_pos (-v * t))).le hp
  convert h using 1 <;> dsimp [circleDensity, densityPolynomial] <;> ring

theorem circleKernel_moment_comparison {L t : ℝ} (hL : 0 < L) (ht : 0 < t) :
    (∫ u : ℝ in Ioi 0, (u * polyA u) * Real.exp (-u * t)) * circleKernel L .b t ≤
      circleKernel L .a t * (∫ u : ℝ in Ioi 0, (u * polyB u) * Real.exp (-u * t)) := by
  rw [circleKernel_eq_density_integral hL, circleKernel_eq_density_integral hL]
  apply integral_product_comparison (circleDensity_laplace_integrable hL ht .a)
    (by simpa only [pow_one, densityPolynomial] using densityPolynomial_moment_integrable .b 1 ht)
    (by simpa only [pow_one, densityPolynomial] using densityPolynomial_moment_integrable .a 1 ht)
    (circleDensity_laplace_integrable hL ht .b)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact density_comparison_pair hL hu hv

noncomputable def ratioFloor (t : ℝ) : ℝ := t * (3 * t + 1) / ((t + 1) * (3 * t + 2))

theorem polynomial_first_moment_ratio {t : ℝ} (ht : 0 < t) :
    (∫ u : ℝ in Ioi 0, (u * polyA u) * Real.exp (-u * t)) =
      ratioFloor t * (∫ u : ℝ in Ioi 0, (u * polyB u) * Real.exp (-u * t)) := by
  have ha := integral_polyA_moment 1 ht
  have hb := integral_polyB_moment 1 ht
  norm_num only [pow_one, Nat.factorial, Nat.cast_one, Nat.cast_ofNat, Nat.reduceAdd,
    Nat.cast_mul, mul_one] at ha hb
  rw [ha, hb]
  dsimp [ratioFloor]
  have ht1 : t + 1 ≠ 0 := ne_of_gt (by linarith : 0 < t + 1)
  have ht2 : 3 * t + 2 ≠ 0 := ne_of_gt (by linarith : 0 < 3 * t + 2)
  field_simp
  <;> ring

theorem circleKernel_ratio_lower {L t : ℝ} (hL : 0 < L) (ht : 0 < t) :
    ratioFloor t * circleKernel L .b t ≤ circleKernel L .a t := by
  have h := circleKernel_moment_comparison hL ht
  rw [polynomial_first_moment_ratio ht] at h
  have hp : 0 < ∫ u : ℝ in Ioi 0, (u * polyB u) * Real.exp (-u * t) := by
    simpa only [pow_one, densityPolynomial] using densityPolynomial_moment_pos .b 1 ht
  nlinarith

theorem ratioFloor_bounds {t : ℝ} (ht : 0 < t) : 0 < ratioFloor t ∧ ratioFloor t < 1 := by
  have h1 : 0 < t + 1 := by linarith
  have h2 : 0 < 3 * t + 2 := by linarith
  constructor
  · dsimp [ratioFloor]
    positivity
  · rw [ratioFloor, div_lt_one (mul_pos h1 h2)]
    nlinarith

theorem hasDerivAt_ratioFloor {t : ℝ} (ht : 0 < t) :
    HasDerivAt ratioFloor
      ((12 * t ^ 2 + 12 * t + 2) / ((t + 1) * (3 * t + 2)) ^ 2) t := by
  have hden : (t + 1) * (3 * t + 2) ≠ 0 := by positivity
  have hd := ((hasDerivAt_id t).mul
    (((hasDerivAt_id t).const_mul 3).add_const 1)).div
      (((hasDerivAt_id t).add_const 1).mul
        (((hasDerivAt_id t).const_mul 3).add_const 2)) hden
  convert hd using 1 <;> dsimp [ratioFloor] <;> ring

theorem strictMonoOn_ratioFloor : StrictMonoOn ratioFloor (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro t ht
    exact (hasDerivAt_ratioFloor ht).continuousAt.continuousWithinAt
  · intro t ht
    have ht' : 0 < t := by simpa using ht
    rw [(hasDerivAt_ratioFloor ht').deriv]
    positivity

end CenteredCircle.AllN

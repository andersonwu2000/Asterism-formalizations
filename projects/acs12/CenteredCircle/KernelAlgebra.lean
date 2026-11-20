import CenteredCircle.CircleKernelRigidity

/-!
The A/B Laplace densities agree with the manuscript's differences of radial
and torque kernels. The derivative identity U=-k' is a separate obligation.
-/

namespace CenteredCircle.AllN

open MeasureTheory Filter Set

theorem integrable_weighted_exponential_of_abs_bound (g : ℝ → ℝ) (C t : ℝ) (k : ℕ)
    (hg : Measurable g) (hbound : ∀ u, 0 < u → |g u| ≤ C * u ^ k)
    (ht : 0 < t) : IntegrableOn (fun u => g u * Real.exp (-u * t)) (Ioi 0) := by
  have hexp : Measurable (fun u : ℝ => Real.exp (-u * t)) := by fun_prop
  apply ((integrable_power_exponential k t ht).const_mul C).mono'
    (hg.mul hexp).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    |g u| * Real.exp (-u * t) ≤ (C * u ^ k) * Real.exp (-u * t) :=
      mul_le_mul_of_nonneg_right (hbound u hu) (Real.exp_pos _).le
    _ = C * (u ^ k * Real.exp (-u * t)) := by ring

noncomputable def radialKernel (L t : ℝ) : ℝ :=
  ∫ u : ℝ in Ioi 0, circleWeight L u * Real.exp (-u * t)

noncomputable def torqueKernel (L t : ℝ) : ℝ :=
  ∫ u : ℝ in Ioi 0, (u * circleWeight L u) * Real.exp (-u * t)

theorem radialKernel_integrable {L : ℝ} (hL : 0 < L) (t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun u => circleWeight L u * Real.exp (-u * t)) (Ioi 0) := by
  apply integrable_weighted_exponential_of_abs_bound (circleWeight L) 1 t 0
    (continuous_circleWeight L).measurable _ ht
  intro u hu
  rw [abs_of_pos (circleWeight_pos hL hu), pow_zero, mul_one]
  exact (circleWeight_lt_one L u).le

theorem torqueKernel_integrable {L : ℝ} (hL : 0 < L) (t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun u => (u * circleWeight L u) * Real.exp (-u * t)) (Ioi 0) := by
  apply integrable_weighted_exponential_of_abs_bound (fun u => u * circleWeight L u) 1 t 1
    (measurable_id.mul (continuous_circleWeight L).measurable) _ ht
  intro u hu
  rw [abs_of_pos (mul_pos hu (circleWeight_pos hL hu)), pow_one, one_mul]
  simpa using (mul_le_mul_of_nonneg_left (circleWeight_lt_one L u).le hu.le)

theorem positiveHalfLine_ne_zero : (volume.restrict (Ioi (0 : ℝ))) ≠ 0 := by
  intro hz
  have hm := congrArg (fun ν : Measure ℝ => ν univ) hz
  simpa using hm

theorem torqueKernel_pos {L : ℝ} (hL : 0 < L) (t : ℝ) (ht : 0 < t) :
    0 < torqueKernel L t := by
  letI : NeZero (volume.restrict (Ioi (0 : ℝ))) := ⟨positiveHalfLine_ne_zero⟩
  have h := integral_strict_of_ae_lt (volume.restrict (Ioi (0 : ℝ)))
    (integrable_zero ℝ ℝ _) (torqueKernel_integrable hL t ht) ?_
  · simpa only [integral_zero] using h
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_pos (mul_pos hu (circleWeight_pos hL hu)) (Real.exp_pos _)

theorem torqueKernel_lt_inverseSquare {L : ℝ} (hL : 0 < L) (t : ℝ) (ht : 0 < t) :
    torqueKernel L t < 1 / t ^ 2 := by
  letI : NeZero (volume.restrict (Ioi (0 : ℝ))) := ⟨positiveHalfLine_ne_zero⟩
  have hi : IntegrableOn (fun u : ℝ => u * Real.exp (-u * t)) (Ioi 0) := by
    simpa only [pow_one] using integrable_power_exponential 1 t ht
  have heval : (∫ u : ℝ in Ioi 0, u * Real.exp (-u * t)) = 1 / t ^ 2 := by
    simpa using integral_power_exponential 1 t ht
  have hcmp := integral_strict_of_ae_lt (volume.restrict (Ioi (0 : ℝ)))
    (torqueKernel_integrable hL t ht) hi ?_
  · rw [heval] at hcmp
    exact hcmp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hw : u * circleWeight L u < u := by
      simpa using mul_lt_mul_of_pos_left (circleWeight_lt_one L u) hu
    exact mul_lt_mul_of_pos_right hw (Real.exp_pos _)

theorem torqueKernel_one_bounds {L : ℝ} (hL : 0 < L) :
    0 < torqueKernel L 1 ∧ torqueKernel L 1 < 1 := by
  constructor
  · exact torqueKernel_pos hL 1 (by norm_num)
  · simpa using torqueKernel_lt_inverseSquare hL 1 (by norm_num)

theorem circleKernel_a_eq_difference {L : ℝ} (hL : 0 < L) (t : ℝ) (ht : 0 < t) :
    circleKernel L .a t =
      radialKernel L t - radialKernel L (t + 1) - torqueKernel L (t + 1) := by
  have ht1 : 0 < t + 1 := by linarith
  have h0 := radialKernel_integrable hL t ht
  have h1 := radialKernel_integrable hL (t + 1) ht1
  have h2 := torqueKernel_integrable hL (t + 1) ht1
  have h01 : IntegrableOn (fun u =>
      circleWeight L u * Real.exp (-u * t) -
      circleWeight L u * Real.exp (-u * (t + 1))) (Ioi 0) := h0.sub h1
  rw [circleKernel, laplace_density_integral (circleDensity L .a)
    (continuous_circleDensity L .a).measurable
    (fun u hu => (circleDensity_pos hL .a hu).le) t]
  unfold radialKernel torqueKernel
  rw [← integral_sub h0 h1, ← integral_sub h01 h2]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  have he : Real.exp (-u * (t + 1)) = Real.exp (-u * t) * Real.exp (-u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  dsimp [circleDensity, densityPolynomial, polyA]
  rw [he]
  ring

theorem circleKernel_b_eq_difference {L : ℝ} (hL : 0 < L) (t : ℝ) (ht : 0 < t) :
    circleKernel L .b t =
      torqueKernel L t - (radialKernel L t - radialKernel L (t + 1)) := by
  have ht1 : 0 < t + 1 := by linarith
  have h0 := torqueKernel_integrable hL t ht
  have h1 := radialKernel_integrable hL t ht
  have h2 := radialKernel_integrable hL (t + 1) ht1
  have h12 : IntegrableOn (fun u =>
      circleWeight L u * Real.exp (-u * t) -
      circleWeight L u * Real.exp (-u * (t + 1))) (Ioi 0) := h1.sub h2
  rw [circleKernel, laplace_density_integral (circleDensity L .b)
    (continuous_circleDensity L .b).measurable
    (fun u hu => (circleDensity_pos hL .b hu).le) t]
  unfold radialKernel torqueKernel
  rw [← integral_sub h1 h2, ← integral_sub h0 h12]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  have he : Real.exp (-u * (t + 1)) = Real.exp (-u * t) * Real.exp (-u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  dsimp [circleDensity, densityPolynomial, polyB]
  rw [he]
  ring

theorem circleKernel_add_eq_torque_difference {L : ℝ} (hL : 0 < L)
    (t : ℝ) (ht : 0 < t) :
    circleKernel L .a t + circleKernel L .b t = torqueKernel L t - torqueKernel L (t + 1) := by
  rw [circleKernel_a_eq_difference hL t ht, circleKernel_b_eq_difference hL t ht]
  ring

end CenteredCircle.AllN

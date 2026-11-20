import CenteredCircle.KernelRatio

/-! All polynomial moments of the actual finite-circle kernels. -/

namespace CenteredCircle.AllN

open MeasureTheory Set Filter

noncomputable def kernelMoment (L : ℝ) (kind : CircleKernelKind) (m : ℕ) (t : ℝ) : ℝ :=
  ∫ u : ℝ in Ioi 0, (u ^ m * circleDensity L kind u) * Real.exp (-u * t)

theorem kernelMoment_density_bound {L u : ℝ} (hL : 0 < L) (hu : 0 < u)
    (kind : CircleKernelKind) (m : ℕ) :
    |u ^ m * circleDensity L kind u| ≤ (1 / 2 : ℝ) * u ^ (m + 2) := by
  rw [abs_of_pos (mul_pos (pow_pos hu m) (circleDensity_pos hL kind hu))]
  calc
    u ^ m * circleDensity L kind u ≤ u ^ m * ((1 / 2 : ℝ) * u ^ 2) :=
      mul_le_mul_of_nonneg_left (circleDensity_quadratic_bound kind hu) (pow_pos hu m).le
    _ = (1 / 2 : ℝ) * u ^ (m + 2) := by rw [pow_add]; ring

theorem kernelMoment_integrable {L t : ℝ} (hL : 0 < L) (ht : 0 < t)
    (kind : CircleKernelKind) (m : ℕ) :
    IntegrableOn (fun u : ℝ => (u ^ m * circleDensity L kind u) * Real.exp (-u * t))
      (Ioi 0) :=
  integrable_weighted_exponential_of_abs_bound _ (1 / 2) t (m + 2)
    ((measurable_id.pow_const m).mul (continuous_circleDensity L kind).measurable)
    (fun _ hu => kernelMoment_density_bound hL hu kind m) ht

theorem kernelMoment_pos {L t : ℝ} (hL : 0 < L) (ht : 0 < t)
    (kind : CircleKernelKind) (m : ℕ) : 0 < kernelMoment L kind m t := by
  letI : NeZero (volume.restrict (Ioi (0 : ℝ))) := ⟨positiveHalfLine_ne_zero⟩
  have h := integral_strict_of_ae_lt (volume.restrict (Ioi (0 : ℝ)))
    (integrable_zero ℝ ℝ _) (kernelMoment_integrable hL ht kind m) ?_
  · simpa only [integral_zero, kernelMoment] using h
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_pos (mul_pos (pow_pos hu m) (circleDensity_pos hL kind hu)) (Real.exp_pos _)

theorem kernelMoment_zero {L : ℝ} (hL : 0 < L) (kind : CircleKernelKind) (t : ℝ) :
    kernelMoment L kind 0 t = circleKernel L kind t := by
  rw [circleKernel_eq_density_integral hL]
  simp only [kernelMoment, pow_zero, one_mul]

theorem hasDerivAt_kernelMoment {L t : ℝ} (hL : 0 < L) (ht : 0 < t)
    (kind : CircleKernelKind) (m : ℕ) :
    HasDerivAt (kernelMoment L kind m) (-kernelMoment L kind (m + 1) t) t := by
  have hd := hasDerivAt_weighted_laplace (fun u : ℝ => u ^ m * circleDensity L kind u)
    (1 / 2) (m + 2)
    ((measurable_id.pow_const m).mul (continuous_circleDensity L kind).measurable)
    (by norm_num) (fun _ hu => kernelMoment_density_bound hL hu kind m) ht
  convert hd using 1
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun u => by dsimp [kernelMoment]; rw [pow_succ]; ring)

theorem kernelMoment_a_lt_b {L t : ℝ} (hL : 0 < L) (ht : 0 < t) (m : ℕ) :
    kernelMoment L .a m t < kernelMoment L .b m t := by
  letI : NeZero (volume.restrict (Ioi (0 : ℝ))) := ⟨positiveHalfLine_ne_zero⟩
  apply integral_strict_of_ae_lt _ (kernelMoment_integrable hL ht .a m)
    (kernelMoment_integrable hL ht .b m)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left
    (mul_lt_mul_of_pos_left (polyA_lt_polyB hu) (circleWeight_pos hL hu)) (pow_pos hu m))
    (Real.exp_pos _)

theorem kernelMoment_comparison {L t : ℝ} (hL : 0 < L) (ht : 0 < t) (m : ℕ) :
    (∫ u : ℝ in Ioi 0, (u ^ (m + 1) * polyA u) * Real.exp (-u * t)) * kernelMoment L .b m t ≤
      kernelMoment L .a m t * (∫ u : ℝ in Ioi 0, (u ^ (m + 1) * polyB u) * Real.exp (-u * t)) := by
  apply integral_product_comparison (kernelMoment_integrable hL ht .a m)
    (densityPolynomial_moment_integrable .b (m + 1) ht)
    (densityPolynomial_moment_integrable .a (m + 1) ht)
    (kernelMoment_integrable hL ht .b m)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have h := mul_nonneg (mul_pos (pow_pos hu m) (pow_pos hv m)).le
    (density_comparison_pair (t := t) hL hu hv)
  convert h using 1 <;> dsimp [densityPolynomial] <;> rw [pow_succ, pow_succ] <;> ring

end CenteredCircle.AllN

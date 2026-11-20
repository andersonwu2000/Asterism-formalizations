import CenteredCircle.ScalarPointwise

/-! Weighted geometric sampling, including the integrability needed for scalar comparison. -/

namespace CenteredCircle.AllN

open MeasureTheory Set Filter

set_option backward.isDefEq.respectTransparency false

theorem integral_densityMeasure (g : ℝ → ℝ) (hg : Measurable g)
    (hg0 : ∀ u, 0 < u → 0 ≤ g u) (f : ℝ → ℝ) :
    (∫ u, f u ∂densityMeasure g) = ∫ u : ℝ in Ioi 0, g u * f u := by
  unfold densityMeasure
  have hw : Measurable (fun u => ENNReal.ofReal (g u)) := ENNReal.measurable_ofReal.comp hg
  rw [integral_withDensity_eq_integral_toReal_smul (μ := volume.restrict (Ioi (0 : ℝ)))
    hw (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [ENNReal.toReal_ofReal (hg0 u hu), smul_eq_mul]

theorem integrable_density_mul (g : ℝ → ℝ) (hg : Measurable g)
    (hg0 : ∀ u, 0 < u → 0 ≤ g u) (f : ℝ → ℝ)
    (hf : Integrable f (densityMeasure g)) :
    IntegrableOn (fun u : ℝ => g u * f u) (Ioi 0) := by
  have hw : Measurable (fun u => ENNReal.ofReal (g u)) := ENNReal.measurable_ofReal.comp hg
  rw [densityMeasure, integrable_withDensity_iff_integrable_smul'
    (μ := volume.restrict (Ioi (0 : ℝ))) hw
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))] at hf
  apply hf.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [ENNReal.toReal_ofReal (hg0 u hu), smul_eq_mul]

theorem samplingTail_exponential_zero {u s : ℝ} (hu : 0 < u) (hs : 0 < s) :
    samplingTail (fun x => Real.exp (-u * x)) 0 s = scaledExpTail u s := by
  rw [samplingTail_exponential u 0 s hu hs, scaledExpTail_eq_factor hu]
  simp only [mul_zero, Real.exp_zero]
  ring

theorem density_sampling_formula (g : ℝ → ℝ) (C : ℝ)
    (hg : Measurable g) (hpos : ∀ u, 0 < u → 0 < g u)
    (hbound : ∀ u, 0 < u → g u ≤ C * u ^ 2) (hC : 0 ≤ C)
    {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun u : ℝ => g u * scaledExpTail u s) (Ioi 0) ∧
      samplingTail (laplaceKernel (densityMeasure g)) 0 s =
        ∫ u : ℝ in Ioi 0, g u * scaledExpTail u s := by
  letI : NeZero (densityMeasure g) := ⟨densityMeasure_ne_zero g hg hpos⟩
  have hg0 : ∀ u, 0 < u → 0 ≤ g u := fun u hu => (hpos u hu).le
  have hint : ∀ x, 0 < x → Integrable (fun u => Real.exp (-u * x)) (densityMeasure g) :=
    fun x hx => integrable_exp_density g C x hg hg0 hbound hx
  have hsum : Summable (fun j : ℕ => laplaceKernel (densityMeasure g) (0 + s + j * s)) := by
    simpa only [zero_add] using summable_laplace_density g C s s hg hg0 hbound hC hs hs
  have hi := integrable_density_mul g hg hg0
    (fun u => samplingTail (fun x => Real.exp (-u * x)) 0 s)
    (integrable_samplingTail_exponential (densityMeasure g) 0 s (by norm_num) hs hint hsum)
  have he := samplingTail_laplace (densityMeasure g) 0 s (by norm_num) hs hint hsum
  rw [integral_densityMeasure g hg hg0] at he
  constructor
  · apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [samplingTail_exponential_zero hu hs]
  · rw [he]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [samplingTail_exponential_zero hu hs]

theorem circle_density_sampling {L s : ℝ} (hL : 0 < L) (hs : 0 < s)
    (kind : CircleKernelKind) :
    IntegrableOn (fun u : ℝ => circleDensity L kind u * scaledExpTail u s) (Ioi 0) ∧
      samplingTail (circleKernel L kind) 0 s =
        ∫ u : ℝ in Ioi 0, circleDensity L kind u * scaledExpTail u s :=
  density_sampling_formula (circleDensity L kind) (1 / 2)
    (continuous_circleDensity L kind).measurable (fun _ hu => circleDensity_pos hL kind hu)
    (fun _ hu => circleDensity_quadratic_bound kind hu) (by norm_num) hs

noncomputable def lineKernel (kind : CircleKernelKind) : ℝ → ℝ :=
  laplaceKernel (densityMeasure (densityPolynomial kind))

theorem line_density_sampling {s : ℝ} (hs : 0 < s) (kind : CircleKernelKind) :
    IntegrableOn (fun u : ℝ => densityPolynomial kind u * scaledExpTail u s) (Ioi 0) ∧
      samplingTail (lineKernel kind) 0 s =
        ∫ u : ℝ in Ioi 0, densityPolynomial kind u * scaledExpTail u s := by
  apply density_sampling_formula (densityPolynomial kind) (1 / 2)
    (continuous_densityPolynomial kind).measurable (fun _ hu => densityPolynomial_pos kind hu)
    (fun u hu => ?_) (by norm_num) hs
  have h := (densityPolynomial_lt_quadratic kind hu).le
  linarith

theorem lineKernel_summable (kind : CircleKernelKind) {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    Summable (fun j : ℕ => lineKernel kind (t + j * s)) := by
  apply summable_laplace_density (densityPolynomial kind) (1 / 2) t s
    (continuous_densityPolynomial kind).measurable (fun _ hu => (densityPolynomial_pos kind hu).le)
    (fun u hu => ?_) (by norm_num) ht hs
  have h := (densityPolynomial_lt_quadratic kind hu).le
  linarith

theorem samplingTail_sub_div (K H : ℝ → ℝ) (s c : ℝ)
    (hK : Summable (fun j : ℕ => K (s + j * s)))
    (hH : Summable (fun j : ℕ => H (s + j * s))) :
    samplingTail (fun t => K t - H t / c) 0 s =
      samplingTail K 0 s - samplingTail H 0 s / c := by
  simp_rw [samplingTail_eq_shift]
  simp only [zero_add, samplingHead]
  rw [hK.tsum_sub (hH.div_const c), tsum_div_const]
  ring

end CenteredCircle.AllN

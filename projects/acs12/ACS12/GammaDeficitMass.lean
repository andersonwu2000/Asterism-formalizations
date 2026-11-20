import ACS12.GammaPureLimit

/-! Total positive density loss and the literal once-only self return. -/

namespace ACS12.GammaMeasure

open MeasureTheory Set Filter
open scoped Topology
open GammaDeficit (lineDensity signedDensity signedDensity_exp_integrable signedDensity_exp_integral)

theorem signedDensity_pos {p L s : ℝ} (hp : 1 ≤ p) (hp₂ : p < 2) (hL : 0 < L) (hs : 0 < s) :
    0 < signedDensity p L s := sub_pos.mpr (imageDensity_lt_lineDensity hp hp₂ hL hs)

theorem signedDensity_total {p L : ℝ} (hp : 1 ≤ p) (hp₂ : p < 2) (hL : 0 < L) :
    IntegrableOn (signedDensity p L) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, signedDensity p L s) = imageSelf p L := by
  let e := signedDensity p L
  let μ := volume.restrict (Ioi (0 : ℝ))
  let t (n : ℕ) := 1 / ((n : ℝ) + 1)
  let f (n : ℕ) (s : ℝ) := e s * Real.exp (-s * t n)
  have hp₀ : 0 < p := zero_lt_one.trans_le hp
  have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  have htlim : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have htPos : Tendsto t atTop (𝓝[>] 0) := by
    rw [nhdsWithin, tendsto_inf]
    exact ⟨htlim, tendsto_principal.mpr (Eventually.of_forall ht)⟩
  have heM : Measurable e := by
    unfold e signedDensity lineDensity
    exact (by fun_prop : Measurable (fun s : ℝ => s ^ (p - 1) / Real.Gamma p)).sub
      (continuous_imageDensity hp₀ hL).measurable
  have he₀ : ∀ᵐ s ∂μ, 0 ≤ e s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (signedDensity_pos hp hp₂ hL hs).le
  have hfI (n : ℕ) : Integrable (f n) μ := signedDensity_exp_integrable hp₀ hL (ht n)
  have hf₀ (n : ℕ) : ∀ᵐ s ∂μ, 0 ≤ f n s := by
    filter_upwards [he₀] with s hs
    exact mul_nonneg hs (Real.exp_pos _).le
  have hfLim : Tendsto (fun n => ∫ s : ℝ, f n s ∂μ) atTop (𝓝 (imageSelf p L)) := by
    simp only [f, e, μ, signedDensity_exp_integral hp₀ hL (ht _)]
    exact (tendsto_line_sub_imagePotential_of_lt_two hp₀ hp₂ hL).comp htPos
  let F (n : ℕ) (s : ℝ) := ENNReal.ofReal (f n s)
  have hEq (n : ℕ) : (∫⁻ s : ℝ, F n s ∂μ) = ENNReal.ofReal (∫ s : ℝ, f n s ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal (hfI n) (hf₀ n)).symm
  have hM : ∀ᵐ s ∂μ, Monotone (fun n => F n s) := by
    filter_upwards [he₀, ae_restrict_mem measurableSet_Ioi] with s he hs
    have hs₀ : 0 < s := hs
    intro n m hnm
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ he
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr hs₀.le)
    apply one_div_le_one_div_of_le (by positivity)
    exact add_le_add (Nat.cast_le.mpr hnm) le_rfl
  have hPoint : ∀ᵐ s ∂μ, Tendsto (fun n => F n s) atTop (𝓝 (ENNReal.ofReal (e s))) := by
    apply Eventually.of_forall
    intro s
    have hc : Continuous (fun x : ℝ => ENNReal.ofReal (e s * Real.exp (-s * x))) :=
      ENNReal.continuous_ofReal.comp (by fun_prop)
    simpa only [F, f, mul_zero, Real.exp_zero, mul_one] using hc.continuousAt.tendsto.comp htlim
  have hLim := lintegral_tendsto_of_tendsto_of_monotone
    (fun n => (hfI n).aemeasurable.ennreal_ofReal) hM hPoint
  have hL' : Tendsto (fun n => ∫⁻ s : ℝ, F n s ∂μ) atTop (𝓝 (ENNReal.ofReal (imageSelf p L))) := by
    simp_rw [hEq]
    exact (ENNReal.continuous_ofReal.continuousAt.tendsto).comp hfLim
  have hE := tendsto_nhds_unique hLim hL'
  have heI : Integrable e μ := by
    refine ⟨heM.aestronglyMeasurable, (hasFiniteIntegral_iff_norm e).mpr ?_⟩
    have hN : (∫⁻ s : ℝ, ENNReal.ofReal ‖e s‖ ∂μ) =
        ∫⁻ s : ℝ, ENNReal.ofReal (e s) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [he₀] with s hs
      rw [Real.norm_of_nonneg hs]
    rw [hN, hE]
    exact ENNReal.ofReal_lt_top
  refine ⟨heI, ?_⟩
  change (∫ s : ℝ, e s ∂μ) = imageSelf p L
  rw [integral_eq_lintegral_of_nonneg_ae he₀ heI.aestronglyMeasurable, hE,
    ENNReal.toReal_ofReal (imageSelf_pos hp₀ hL).le]

end ACS12.GammaMeasure

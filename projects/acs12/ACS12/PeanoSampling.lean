import ACS12.GammaPeano

/-! Dependence of the original complete Peano samples on their spacing. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open scoped Topology

theorem peanoTail_strictAnti {p L h : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hh : 0 < h) (kind : CircleKernelKind) :
    StrictAntiOn (samplingTail (peanoKernel p L h kind) 0) (Ioi 0) := by
  intro b hb c hc hbc
  obtain ⟨hbI, hbE⟩ := peanoKernel_sampling hp hp₂ hL hh hb kind
  obtain ⟨hcI, hcE⟩ := peanoKernel_sampling hp hp₂ hL hh hc kind
  rw [hbE, hcE]
  letI : NeZero (volume.restrict (Ioi (0 : ℝ))) := ⟨positiveHalfLine_ne_zero⟩
  apply integral_strict_of_ae_lt _ hcI hbI
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs₀ : 0 < s := hs
  apply mul_lt_mul_of_pos_left _ (mul_pos (imageDensity_pos hp hL hs)
    (densityPolynomial_pos kind (mul_pos hh hs)))
  rw [scaledExpTail_eq_factor hs₀, scaledExpTail_eq_factor hs₀]
  exact div_lt_div_of_pos_right (strictAntiOn_expTailFactor (mul_pos hs₀ hb)
    (mul_pos hs₀ hc) (mul_lt_mul_of_pos_left hbc hs₀)) hs₀

theorem peanoTail_nonneg {p L h b : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hh : 0 < h) (hb : 0 < b) (kind : CircleKernelKind) :
    0 ≤ samplingTail (peanoKernel p L h kind) 0 b := by
  rw [(peanoKernel_sampling hp hp₂ hL hh hb kind).2]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  change 0 < s at hs
  exact mul_nonneg (mul_pos (imageDensity_pos hp hL hs)
    (densityPolynomial_pos kind (mul_pos hh hs))).le
    (div_pos hb (expTail_den_pos (mul_pos hs hb))).le

theorem peanoTail_continuousOn {p L h : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hh : 0 < h) (kind : CircleKernelKind) :
    ContinuousOn (samplingTail (peanoKernel p L h kind) 0) (Ioi 0) := by
  intro b hb
  have hb₀ : 0 < b := hb
  let d := b / 2
  have hd : 0 < d := by positivity
  have hdb : d < b := by dsimp [d]; linarith
  let g (s : ℝ) := peanoDensity p L h kind s
  have hG : Measurable g := ((continuous_imageDensity hp hL).mul
    ((continuous_densityPolynomial kind).comp (continuous_const.mul continuous_id))).measurable
  let f (c s : ℝ) := g s * scaledExpTail s c
  have hlim : Tendsto (fun c => ∫ s : ℝ in Ioi 0, f c s) (𝓝 b)
      (𝓝 (∫ s : ℝ in Ioi 0, f b s)) := by
    apply tendsto_integral_filter_of_dominated_convergence (f d)
    · exact Eventually.of_forall fun c => by
        unfold f scaledExpTail
        exact (hG.mul (by fun_prop)).aestronglyMeasurable
    · filter_upwards [Ioi_mem_nhds hdb] with c hc
      have hc₀ : 0 < c := hd.trans hc
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs₀ : 0 < s := hs
      have hg₀ : 0 ≤ g s := (mul_pos (imageDensity_pos hp hL hs₀)
        (densityPolynomial_pos kind (mul_pos hh hs₀))).le
      have hβ : 0 ≤ scaledExpTail s c := (div_pos hc₀ (expTail_den_pos (mul_pos hs₀ hc₀))).le
      rw [Real.norm_of_nonneg (mul_nonneg hg₀ hβ)]
      apply mul_le_mul_of_nonneg_left _ hg₀
      rw [scaledExpTail_eq_factor hs₀, scaledExpTail_eq_factor hs₀]
      exact div_le_div_of_nonneg_right (strictAntiOn_expTailFactor.antitoneOn
        (mul_pos hs₀ hd) (mul_pos hs₀ hc₀) (mul_le_mul_of_nonneg_left hc.le hs₀.le)) hs₀.le
    · exact (peanoKernel_sampling hp hp₂ hL hh hd kind).1
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hne := (expTail_den_pos (mul_pos (mem_Ioi.mp hs) hb₀)).ne'
      have hc : ContinuousAt (fun c : ℝ => f c s) b := by
        unfold f scaledExpTail
        fun_prop (disch := assumption)
      exact hc.tendsto
  have hbE := (peanoKernel_sampling hp hp₂ hL hh hb₀ kind).2
  change ContinuousWithinAt (samplingTail (peanoKernel p L h kind) 0) (Ioi 0) b
  apply ContinuousAt.continuousWithinAt
  change Tendsto (samplingTail (peanoKernel p L h kind) 0) (𝓝 b)
    (𝓝 (samplingTail (peanoKernel p L h kind) 0 b))
  rw [hbE]
  refine hlim.congr' ?_
  filter_upwards [Ioi_mem_nhds hb₀] with c hc
  exact (peanoKernel_sampling hp hp₂ hL hh hc kind).2.symm

theorem peanoTail_total {p L u : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hu : 0 < u) :
    samplingTail (peanoKernel p L u .a) 0 u + samplingTail (peanoKernel p L u .b) 0 u =
      u ^ 2 * imageSlope p L u := by
  obtain ⟨hA, hAE⟩ := peanoKernel_sampling hp hp₂ hL hu hu .a
  obtain ⟨hB, hBE⟩ := peanoKernel_sampling hp hp₂ hL hu hu .b
  rw [hAE, hBE]
  calc
    _ = ∫ s : ℝ in Ioi 0, peanoDensity p L u .a s * scaledExpTail s u +
        peanoDensity p L u .b s * scaledExpTail s u := (integral_add hA hB).symm
    _ = ∫ s : ℝ in Ioi 0, u ^ 2 * (imageDensity p L s * s * Real.exp (-s * u)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      have hs₀ : 0 < s := hs
      have hden := (expTail_den_pos (mul_pos hs₀ hu)).ne'
      have he : Real.exp (s * u) ≠ 0 := (Real.exp_pos _).ne'
      simp only [peanoDensity, densityPolynomial, polyA, polyB, scaledExpTail,
        show -s * u = -(u * s) by ring, mul_comm u s]
      rw [Real.exp_neg]
      field_simp [hden, he]
      ring
    _ = _ := integral_const_mul _ _

end ACS12.GammaMeasure

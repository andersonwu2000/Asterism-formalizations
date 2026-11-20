import ACS12.SignedSampling

/-! Differentiating a complete Bose stream for the pure and interpolated densities. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open scoped Topology

theorem boseStream_integrable {g : ℝ → ℝ} {B r : ℝ} (hg : Measurable g)
    (hB : ∀ s > 0, |g s| ≤ B * (s + s ^ 2)) (hr : 0 < r) :
    IntegrableOn (fun s => g s * scaledExpTail s r) (Ioi 0) := by
  simpa only [mul_zero, Real.exp_zero, mul_one] using
    (signedTail_sampling_of_majorant hg hr (signedTail_majorant_linearQuadratic hg hB le_rfl hr)).1

theorem boseStream_derivative {g : ℝ → ℝ} {B r : ℝ} (hg : Measurable g)
    (hB : ∀ s > 0, |g s| ≤ B * (s + s ^ 2)) (hr : 0 < r) :
    IntegrableOn (fun s => g s * BoseShape.C (s * r)) (Ioi 0) ∧
      HasDerivAt (fun t => ∫ s : ℝ in Ioi 0, g s * scaledExpTail s t)
        (-(∫ s : ℝ in Ioi 0, g s * BoseShape.C (s * r))) r := by
  let c := r / 2
  let μ := volume.restrict (Ioi (0 : ℝ))
  let f (t s : ℝ) := g s * scaledExpTail s t
  let f' (t s : ℝ) := -(g s * BoseShape.C (s * t))
  let K := B * BoseShape.decayConstant * (c + 1)
  let M (s : ℝ) := K * (s * Real.exp (-s * c) + 2 * (s ^ 2 * Real.exp (-s * c)) +
    s ^ 3 * Real.exp (-s * c))
  have hc : 0 < c := half_pos hr
  have hcr : c < r := by dsimp only [c]; linarith
  have hC : 0 ≤ B := by
    have h := (abs_nonneg _).trans (hB 1 zero_lt_one)
    norm_num at h
    linarith
  have hF : ∀ᶠ t in 𝓝 r, AEStronglyMeasurable (f t) μ := Eventually.of_forall fun t =>
    (hg.mul (by unfold scaledExpTail; fun_prop)).aestronglyMeasurable
  have hF' : AEStronglyMeasurable (f' r) μ :=
    (hg.mul (by unfold BoseShape.C; fun_prop)).neg.aestronglyMeasurable
  have h₁ : Integrable (fun s : ℝ => s * Real.exp (-s * c)) μ := by
    simpa only [pow_one] using expMoment_nat_integrable 1 hc
  have h₂ : Integrable (fun s : ℝ => s ^ 2 * Real.exp (-s * c)) μ := expMoment_nat_integrable 2 hc
  have h₃ : Integrable (fun s : ℝ => s ^ 3 * Real.exp (-s * c)) μ := expMoment_nat_integrable 3 hc
  have hM : Integrable M μ := ((h₁.add (h₂.const_mul 2)).add h₃).const_mul K
  have hDom : ∀ᵐ s ∂μ, ∀ t ∈ Ioi c, ‖f' t s‖ ≤ M s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    intro t ht
    have hs₀ : 0 < s := hs
    have ht₀ := hc.trans (mem_Ioi.mp ht)
    have hU := (BoseShape.C_antitone (mul_pos hs₀ hc) (mul_pos hs₀ ht₀)
      (mul_le_mul_of_nonneg_left (mem_Ioi.mp ht).le hs₀.le)).trans (BoseShape.C_le_decay (mul_pos hs₀ hc))
    have hP : s * c + 1 ≤ (c + 1) * (s + 1) := by nlinarith only [hs₀.le, hc.le]
    simp only [f', Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos (BoseShape.C_pos (mul_pos hs₀ ht₀))]
    calc
      _ ≤ B * (s + s ^ 2) * (BoseShape.decayConstant * (s * c + 1) * Real.exp (-(s * c))) :=
        mul_le_mul (hB s hs₀) hU (BoseShape.C_pos (mul_pos hs₀ ht₀)).le (by positivity)
      _ ≤ B * (s + s ^ 2) * (BoseShape.decayConstant * ((c + 1) * (s + 1)) * Real.exp (-(s * c))) := by
        gcongr
        exact BoseShape.decayConstant_pos.le
      _ = _ := by dsimp only [M, K]; rw [← neg_mul]; ring
  have hDeriv : ∀ᵐ s ∂μ, ∀ t ∈ Ioi c, HasDerivAt (fun x => f x s) (f' t s) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    intro t ht
    convert (scaledExpTail_derivative hs (hc.trans (mem_Ioi.mp ht))).const_mul (g s) using 1
    dsimp only [f']
    ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (Ioi_mem_nhds hcr) hF (boseStream_integrable hg hB hr) hF' hDom hM hDeriv
  have hInt : IntegrableOn (fun s => g s * BoseShape.C (s * r)) (Ioi 0) := by
    exact h.1.neg.congr (Eventually.of_forall fun s => neg_neg (g s * BoseShape.C (s * r)))
  refine ⟨hInt, ?_⟩
  simpa only [f', integral_neg, f, μ] using h.2

end ACS12.GammaMeasure

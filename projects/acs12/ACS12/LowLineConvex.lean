import ACS12.MellinLine

/-! The complete scalar exclusion interval after the Mellin endpoint. -/

namespace ACS12.LowScalar

open MeasureTheory Set Filter
open CenteredCircle.AllN
open scoped Topology
set_option backward.isDefEq.respectTransparency false

private noncomputable def tailCurvature (x : ℝ) : ℝ := (x - 2) * Real.exp x + x + 2
private noncomputable def tailCurvatureSlope (x : ℝ) : ℝ := (x - 1) * Real.exp x + 1

private theorem tailCurvature_pos {x : ℝ} (hx : 0 < x) : 0 < tailCurvature x := by
  have hSlope (t : ℝ) : HasDerivAt tailCurvatureSlope (t * Real.exp t) t := by
    have h := (((hasDerivAt_id t).sub_const 1).mul (Real.hasDerivAt_exp t)).add_const 1
    convert h using 1
    simp only [id_eq, one_mul]
    ring
  have hDer (t : ℝ) : HasDerivAt tailCurvature (tailCurvatureSlope t) t := by
    have h := ((((hasDerivAt_id t).sub_const 2).mul (Real.hasDerivAt_exp t)).add
      (hasDerivAt_id t)).add_const 2
    convert h using 1
    simp only [id_eq, one_mul, tailCurvatureSlope]
    ring
  have hs : StrictMonoOn tailCurvatureSlope (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
    · exact fun t _ => (hSlope t).continuousAt.continuousWithinAt
    · intro t ht
      rw [(hSlope t).deriv]
      exact mul_pos (by simpa only [interior_Ici, mem_Ioi] using ht) (Real.exp_pos _)
  have hz : tailCurvatureSlope 0 = 0 := by norm_num [tailCurvatureSlope]
  have hpos (t : ℝ) (ht : 0 < t) : 0 < tailCurvatureSlope t := by
    rw [← hz]
    exact hs (by simp) ht.le ht
  have hm : StrictMonoOn tailCurvature (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
    · exact fun t _ => (hDer t).continuousAt.continuousWithinAt
    · intro t ht
      rw [(hDer t).deriv]
      exact hpos t (by simpa only [interior_Ici, mem_Ioi] using ht)
  have h := hm (by simp : (0 : ℝ) ∈ Ici 0) hx.le hx
  simpa only [show tailCurvature 0 = 0 by norm_num [tailCurvature]] using h

theorem expTail_convex : ConvexOn ℝ (Ioi 0) expTailFactor := by
  apply StrictConvexOn.convexOn
  apply strictConvexOn_of_deriv2_pos' (convex_Ioi _)
  · exact fun x hx => (hasDerivAt_expTailFactor hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx0 : 0 < x := hx
    have he : deriv expTailFactor =ᶠ[𝓝 x]
        fun t => (Real.exp t - 1 - t * Real.exp t) / (Real.exp t - 1) ^ 2 := by
      filter_upwards [Ioi_mem_nhds hx0] with t ht
      exact (hasDerivAt_expTailFactor ht).deriv
    have hden := (Real.hasDerivAt_exp x).sub_const 1
    have hnum := hden.sub ((hasDerivAt_id x).mul (Real.hasDerivAt_exp x))
    have h := hnum.div (hden.pow 2) (pow_ne_zero _ (expTail_den_pos hx).ne')
    have h' : HasDerivAt
        (fun t => (Real.exp t - 1 - t * Real.exp t) / (Real.exp t - 1) ^ 2)
        (Real.exp x * tailCurvature x / (Real.exp x - 1) ^ 3) x := by
      convert h using 1
      simp only [id_eq, Pi.pow_apply, Pi.sub_apply, Pi.mul_apply, one_mul, tailCurvature,
        show (2 - 1 : ℕ) = 1 by decide, pow_one]
      field_simp [(expTail_den_pos hx).ne']
      ring
    change 0 < deriv (deriv expTailFactor) x
    rw [(h'.congr_of_eventuallyEq he).deriv]
    exact div_pos (mul_pos (Real.exp_pos _) (tailCurvature_pos hx)) (pow_pos (expTail_den_pos hx) _)

private theorem scaledTail_convex {s : ℝ} (hs : 0 < s) :
    ConvexOn ℝ (Ioi 0) (scaledExpTail s) := by
  refine ⟨convex_Ioi _, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := expTail_convex.2 (mul_pos hs hx) (mul_pos hs hy) ha hb hab
  simp only [smul_eq_mul] at h ⊢
  simp only [scaledExpTail_eq_factor hs]
  rw [show s * (a * x + b * y) = a * (s * x) + b * (s * y) by ring]
  exact (div_le_div_of_nonneg_right h hs.le).trans_eq (by ring)

noncomputable def lineDensity (p b s : ℝ) : ℝ :=
  s ^ (p - 1) *
    (rightMixPolynomial s * (scaledExpTail s b - scaledExpTail s 1) -
      (1 - b) * ((s / 4 + 5 / 4) * Real.exp (-s)))

noncomputable def lineValue (p b : ℝ) : ℝ := ∫ s in Ioi (0 : ℝ), lineDensity p b s

theorem lineDensity_endpoint {p s : ℝ} (hs : 0 < s) :
    lineDensity p (2 / 3) s = mellinIntegrand p s := by
  have hExp : Real.exp (-s) * Real.exp s = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hmul (v d c : ℝ) :
      Real.exp (-s) * (Real.exp s * v * d - c) = v * d - Real.exp (-s) * c := by
    simp only [mul_sub, ← mul_assoc, hExp, one_mul]
  unfold lineDensity mellinIntegrand
  rw [mellinDefect_eq hs, hmul]
  simp only [rightMixPolynomial, polyA, polyB, scaledExpTail, mul_one,
    mul_comm (2 / 3 : ℝ) s]
  ring

private noncomputable def correction (p s : ℝ) : ℝ :=
  s ^ (p - 1) * ((s / 4 + 5 / 4) * Real.exp (-s))

private theorem correction_integrable {p : ℝ} (hp : 0 < p) :
    IntegrableOn (correction p) (Ioi 0) := by
  have h1 := CenteredCircle.AllN.integrable_gamma_laplace hp (r := 1) one_pos
  have h2 := CenteredCircle.AllN.integrable_gamma_laplace (a := p + 1)
    (by positivity) (r := 1) one_pos
  have h := (h2.const_mul (1 / 4 : ℝ)).add (h1.const_mul (5 / 4 : ℝ))
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs0 : 0 < s := hs
  simp only [Pi.add_apply, correction]
  rw [add_sub_cancel_right, one_mul, show s ^ p = s ^ (p - 1) * s by
    rw [show s ^ p = s ^ ((p - 1) + 1) by congr 1; ring, Real.rpow_add hs0, Real.rpow_one]]
  ring

theorem lineDensity_integrable {p b : ℝ} (hp : 0 < p) (hb : 2 / 3 ≤ b) (hb1 : b ≤ 1) :
    IntegrableOn (lineDensity p b) (Ioi 0) := by
  have h0 : IntegrableOn (lineDensity p (2 / 3)) (Ioi 0) := by
    apply (mellinIntegrand_integrable hp).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (lineDensity_endpoint hs).symm
  have hd : IntegrableOn (fun s => lineDensity p (2 / 3) s + (2 / 3) * correction p s) (Ioi 0) :=
    h0.add ((correction_integrable hp).const_mul _)
  have hm : Measurable (lineDensity p b) := by
    unfold lineDensity rightMixPolynomial polyA polyB scaledExpTail
    fun_prop
  apply hd.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs0 : 0 < s := hs
  have hb0 : 0 < b := (by norm_num : (0 : ℝ) < 2 / 3).trans_le hb
  have hTail : scaledExpTail s b ≤ scaledExpTail s (2 / 3) := by
    rw [scaledExpTail_eq_factor hs0 b, scaledExpTail_eq_factor hs0 (2 / 3)]
    exact div_le_div_of_nonneg_right (strictAntiOn_expTailFactor.antitoneOn
      (mul_pos hs0 (by norm_num)) (mul_pos hs0 hb0) (mul_le_mul_of_nonneg_left hb hs0.le)) hs0.le
  have hTail0 : scaledExpTail s 1 ≤ scaledExpTail s b := scaledExpTail_one_le hs0 hb0 hb1
  let P := s ^ (p - 1) * rightMixPolynomial s
  let Q := correction p s
  have hP : 0 ≤ P := mul_nonneg (Real.rpow_nonneg hs0.le _) (rightMixPolynomial_pos hs0).le
  have hQ : 0 ≤ Q := by dsimp [Q, correction]; positivity
  have hV0 : 0 ≤ P * (scaledExpTail s b - scaledExpTail s 1) :=
    mul_nonneg hP (sub_nonneg.mpr hTail0)
  have hV : P * (scaledExpTail s b - scaledExpTail s 1) ≤
      P * (scaledExpTail s (2 / 3) - scaledExpTail s 1) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_right hTail _) hP
  have hE : 0 ≤ P * (scaledExpTail s (2 / 3) - scaledExpTail s 1) := hV0.trans hV
  have hc : (1 - b) * Q ≤ (1 / 3 : ℝ) * Q :=
    mul_le_mul_of_nonneg_right (by linarith) hQ
  have hc0 : 0 ≤ (1 - b) * Q := mul_nonneg (sub_nonneg.mpr hb1) hQ
  have hform (v : ℝ) : lineDensity p v s =
      P * (scaledExpTail s v - scaledExpTail s 1) - (1 - v) * Q := by
    dsimp only [lineDensity, P, Q, correction]
    ring
  rw [Real.norm_eq_abs, hform, hform, abs_le]
  constructor <;> linarith only [hV0, hV, hE, hc, hc0, hQ]

/-- The entire scalar interval closes by the endpoint sign and convexity of
the actual Bose factor. This excludes all (2/3 le b < 1) for the line bound. -/
theorem lineValue_neg {p b : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hb : 2 / 3 ≤ b) (hb1 : b < 1) :
    lineValue p b < 0 := by
  let u : ℝ := 3 * (1 - b)
  have hu : 0 < u := by dsimp only [u]; linarith
  have hu1 : 0 ≤ 1 - u := by dsimp only [u]; linarith
  have he : u * (2 / 3) + (1 - u) * 1 = b := by dsimp only [u]; ring
  have hI : IntegrableOn (lineDensity p b) (Ioi 0) := lineDensity_integrable hp hb hb1.le
  have hE : IntegrableOn (lineDensity p (2 / 3)) (Ioi 0) :=
    lineDensity_integrable hp le_rfl (by norm_num)
  have hpoint : lineDensity p b ≤ᵐ[volume.restrict (Ioi 0)] fun s => u * lineDensity p (2 / 3) s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 < s := hs
    have h := (scaledTail_convex hs0).2 (by norm_num : (2 / 3 : ℝ) ∈ Ioi 0)
      (by norm_num : (1 : ℝ) ∈ Ioi 0) hu.le hu1 (by ring : u + (1 - u) = 1)
    simp only [smul_eq_mul, he] at h
    have hh := mul_le_mul_of_nonneg_left h
      (mul_nonneg (Real.rpow_nonneg hs0.le (p - 1)) (rightMixPolynomial_pos hs0).le)
    dsimp only [lineDensity, u] at hh ⊢
    linarith only [hh]
  have hcmp := integral_mono_ae hI (hE.const_mul u) hpoint
  rw [integral_const_mul] at hcmp
  have hNeg : (∫ s in Ioi (0 : ℝ), lineDensity p (2 / 3) s) < 0 := by
    have heq : (∫ s in Ioi (0 : ℝ), lineDensity p (2 / 3) s) =
        ∫ s in Ioi (0 : ℝ), mellinIntegrand p s := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact lineDensity_endpoint hs
    rw [heq]
    exact actual_mellin_neg hp hp1
  exact hcmp.trans_lt (mul_neg_of_pos_of_neg hu hNeg)

/-- The cubic and line inequalities force the incident scalar mass to one. -/
theorem line_bounds_force_one {p b : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hb : 0 < b) (hb1 : b ≤ 1) (hcubic : 0 < massPolynomial p b)
    (hline : 0 ≤ lineValue p b) : b = 1 := by
  by_contra hne
  have hlow := two_thirds_lt_of_massPolynomial_pos hp1 hb hcubic
  exact (not_lt_of_ge hline) (lineValue_neg hp hp1 hlow.le (lt_of_le_of_ne hb1 hne))

end ACS12.LowScalar

import ACS12.GammaBalances
import ACS12.GammaOrder

/-! Laplace moments of the actual A/B kernels and their positive comparison
with the reference at exponent two. -/

namespace ACS12.GammaMeasure

open MeasureTheory Set Filter
open scoped Topology
open CenteredCircle.AllN (CircleKernelKind densityPolynomial densityPolynomial_pos
  densityPolynomial_lt_quadratic continuous_densityPolynomial polyA polyB polyA_lt_polyB
  integral_strict_of_ae_lt positiveHalfLine_ne_zero
  integrable_weighted_exponential_of_abs_bound hasDerivAt_weighted_laplace)

noncomputable def imageMomentWeight (p L : ℝ) (kind : CircleKernelKind)
    (j : ℕ) (s : ℝ) : ℝ :=
  s ^ j * (imageDensity p L s * densityPolynomial kind s)

noncomputable def imageMoment (p L : ℝ) (kind : CircleKernelKind) (j : ℕ) (t : ℝ) : ℝ :=
  ∫ s : ℝ in Ioi 0, imageMomentWeight p L kind j s * Real.exp (-s * t)

private theorem continuous_imageMomentWeight {p L : ℝ} (hp : 0 < p) (hL : 0 < L)
    (kind : CircleKernelKind) (j : ℕ) : Continuous (imageMomentWeight p L kind j) :=
  (continuous_id.pow j).mul ((continuous_imageDensity hp hL).mul
    (continuous_densityPolynomial kind))

private theorem imageMomentWeight_bound {p L C s : ℝ} (hp : 0 < p) (hL : 0 < L) (hs : 0 < s)
    (hC : ∀ s > 0, imageDensity p L s ≤ C * s) (kind : CircleKernelKind) (j : ℕ) :
    |imageMomentWeight p L kind j s| ≤ (C / 2) * s ^ (j + 3) := by
  have hw : 0 ≤ imageDensity p L s := (imageDensity_pos hp hL hs).le
  have hd : 0 ≤ densityPolynomial kind s := (densityPolynomial_pos kind hs).le
  have hCs : 0 ≤ C * s := hw.trans (hC s hs)
  rw [imageMomentWeight, abs_of_nonneg (by positivity)]
  calc
    _ ≤ s ^ j * ((C * s) * (s ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (hC s hs) (densityPolynomial_lt_quadratic kind hs).le hd hCs)
        (pow_nonneg hs.le j)
    _ = _ := by rw [pow_add, show s ^ (3 : ℕ) = s ^ 3 by rfl]; ring

theorem imageMoment_integrable {p L t : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2) (hL : 0 < L)
    (ht : 0 < t) (kind : CircleKernelKind) (j : ℕ) :
    IntegrableOn (fun s : ℝ => imageMomentWeight p L kind j s * Real.exp (-s * t)) (Ioi 0) := by
  obtain ⟨C, hC₀, hC⟩ := imageDensity_linear_bound hp hp₂ hL
  exact integrable_weighted_exponential_of_abs_bound _ (C / 2) t (j + 3)
    (continuous_imageMomentWeight hp hL kind j).measurable
    (fun s hs => imageMomentWeight_bound hp hL hs hC kind j) ht

theorem imageMoment_pos {p L t : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2) (hL : 0 < L)
    (ht : 0 < t) (kind : CircleKernelKind) (j : ℕ) : 0 < imageMoment p L kind j t := by
  letI : NeZero (volume.restrict (Ioi (0 : ℝ))) := ⟨positiveHalfLine_ne_zero⟩
  have h := integral_strict_of_ae_lt (volume.restrict (Ioi (0 : ℝ))) (integrable_zero ℝ ℝ _)
    (imageMoment_integrable hp hp₂ hL ht kind j) ?_
  · simpa only [imageMoment, integral_zero] using h
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    change 0 < s at hs
    exact mul_pos (mul_pos (pow_pos hs _) (mul_pos (imageDensity_pos hp hL hs)
      (densityPolynomial_pos kind hs))) (Real.exp_pos _)

theorem imageMoment_a_lt_b {p L t : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2) (hL : 0 < L)
    (ht : 0 < t) (j : ℕ) : imageMoment p L .a j t < imageMoment p L .b j t := by
  letI : NeZero (volume.restrict (Ioi (0 : ℝ))) := ⟨positiveHalfLine_ne_zero⟩
  apply integral_strict_of_ae_lt (volume.restrict (Ioi (0 : ℝ)))
    (imageMoment_integrable hp hp₂ hL ht .a j) (imageMoment_integrable hp hp₂ hL ht .b j)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  change 0 < s at hs
  exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left
    (mul_lt_mul_of_pos_left (polyA_lt_polyB hs) (imageDensity_pos hp hL hs))
    (pow_pos hs _)) (Real.exp_pos _)

theorem hasDerivAt_imageMoment {p L t : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2) (hL : 0 < L)
    (ht : 0 < t) (kind : CircleKernelKind) (j : ℕ) :
    HasDerivAt (imageMoment p L kind j) (-imageMoment p L kind (j + 1) t) t := by
  obtain ⟨C, hC₀, hC⟩ := imageDensity_linear_bound hp hp₂ hL
  have h := hasDerivAt_weighted_laplace (imageMomentWeight p L kind j) (C / 2) (j + 3)
    (continuous_imageMomentWeight hp hL kind j).measurable (by positivity)
    (fun s hs => imageMomentWeight_bound hp hL hs hC kind j) ht
  convert h using 1
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s _
  simp only [imageMomentWeight, pow_succ]
  ring

theorem imageMoment_zero_a {p L t : ℝ} (hp : 0 < p) (hL : 0 < L) (ht : 0 < t) :
    imageMoment p L .a 0 t = imageA p L t := by
  have hkt := imagePotential_integrable hp hL ht
  have ht' : 0 < t + 1 := by linarith
  have hks := imagePotential_integrable hp hL ht'
  have hus := imageSlope_integrable hp hL ht'
  have hk : IntegrableOn (fun s => imageDensity p L s * Real.exp (-s * t) -
      imageDensity p L s * Real.exp (-s * (t + 1))) (Ioi 0) := hkt.sub hks
  unfold imageA imagePotential imageSlope imageMoment
  rw [← integral_sub hkt hks, ← integral_sub hk hus]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s _
  simp only [imageMomentWeight, densityPolynomial, polyA, pow_zero, one_mul,
    show -s * (t + 1) = -s * t + -s by ring, Real.exp_add]
  ring

theorem imageMoment_zero_b {p L t : ℝ} (hp : 0 < p) (hL : 0 < L) (ht : 0 < t) :
    imageMoment p L .b 0 t = imageB p L t := by
  have hut := imageSlope_integrable hp hL ht
  have hkt := imagePotential_integrable hp hL ht
  have ht' : 0 < t + 1 := by linarith
  have hks := imagePotential_integrable hp hL ht'
  have hk : IntegrableOn (fun s => imageDensity p L s * Real.exp (-s * t) -
      imageDensity p L s * Real.exp (-s * (t + 1))) (Ioi 0) := hkt.sub hks
  unfold imageB imagePotential imageSlope imageMoment
  rw [← integral_sub hkt hks, ← integral_sub hut hk]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s _
  simp only [imageMomentWeight, densityPolynomial, polyB, pow_zero, one_mul,
    show -s * (t + 1) = -s * t + -s by ring, Real.exp_add]
  ring

theorem imageMoment_comparison {p L t : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2) (hL : 0 < L)
    (ht : 0 < t) (j : ℕ) :
    (∫ s : ℝ in Ioi 0, (s ^ (j + 1) * polyA s) * Real.exp (-s * t)) *
        imageMoment p L .b j t ≤
      imageMoment p L .a j t *
        (∫ s : ℝ in Ioi 0, (s ^ (j + 1) * polyB s) * Real.exp (-s * t)) := by
  unfold imageMoment
  apply CenteredCircle.AllN.integral_product_comparison
    (imageMoment_integrable hp hp₂ hL ht .a j)
    (CenteredCircle.AllN.densityPolynomial_moment_integrable .b (j + 1) ht)
    (CenteredCircle.AllN.densityPolynomial_moment_integrable .a (j + 1) ht)
    (imageMoment_integrable hp hp₂ hL ht .b j)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  change 0 < u at hu
  change 0 < v at hv
  have hw (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x ≤ y) :
      0 ≤ imageDensity p L x * y - imageDensity p L y * x :=
    sub_nonneg.mpr ((div_le_div_iff₀ hy hx).mp ((imageDensity_div_antitone hp hp₂ hL) hx hy hxy))
  have hpair : 0 ≤ (polyA u * polyB v - polyA v * polyB u) *
      (imageDensity p L u * v - imageDensity p L v * u) := by
    rcases le_total u v with huv | hvu
    · exact mul_nonneg (CenteredCircle.AllN.density_polynomial_cross_nonneg hu hv huv)
        (hw u v hu hv huv)
    · have h := mul_nonneg (CenteredCircle.AllN.density_polynomial_cross_nonneg hv hu hvu)
        (hw v u hv hu hvu)
      nlinarith
  have h := mul_nonneg (by positivity :
    0 ≤ u ^ j * v ^ j * Real.exp (-u * t) * Real.exp (-v * t)) hpair
  convert h using 1
  simp only [imageMomentWeight, densityPolynomial, pow_succ]
  ring

theorem imageMoment_ratio_lower {p L t : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2) (hL : 0 < L)
    (ht : 0 < t) :
    CenteredCircle.AllN.ratioFloor t * imageMoment p L .b 0 t ≤ imageMoment p L .a 0 t := by
  have h := imageMoment_comparison hp hp₂ hL ht 0
  simp only [zero_add, pow_one] at h
  rw [CenteredCircle.AllN.polynomial_first_moment_ratio ht] at h
  have hb : 0 < ∫ s : ℝ in Ioi 0, (s * polyB s) * Real.exp (-s * t) := by
    simpa only [pow_one, densityPolynomial] using
      CenteredCircle.AllN.densityPolynomial_moment_pos .b 1 ht
  nlinarith

noncomputable def imageLeftMoment (p L : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  imageMoment p L .a j t - imageMoment p L .b j t / 4

noncomputable def imageRightMoment (p L : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  imageMoment p L .b j t - imageMoment p L .a j t / 4

theorem imageLeftMoment_pos {p L t : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2) (hL : 0 < L)
    (ht : 1 ≤ t) (j : ℕ) (hj : j ≤ 2) : 0 < imageLeftMoment p L j t := by
  have htp : 0 < t := by linarith
  have hcmp := imageMoment_comparison hp hp₂ hL htp j
  have hline := CenteredCircle.AllN.polynomial_mixed_moment_pos j hj ht
  have hB := imageMoment_pos hp hp₂ hL htp .b j
  have hprod := mul_pos hline hB
  have hb : 0 < ∫ s : ℝ in Ioi 0, (s ^ (j + 1) * polyB s) * Real.exp (-s * t) :=
    CenteredCircle.AllN.densityPolynomial_moment_pos .b (j + 1) htp
  apply (mul_pos_iff_of_pos_right hb).mp
  dsimp [imageLeftMoment]
  nlinarith

theorem imageRightMoment_pos {p L t : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2) (hL : 0 < L)
    (ht : 0 < t) (j : ℕ) : 0 < imageRightMoment p L j t := by
  have ha := imageMoment_pos hp hp₂ hL ht .a j
  have hlt := imageMoment_a_lt_b hp hp₂ hL ht j
  dsimp [imageRightMoment]
  linarith

theorem hasDerivAt_imageLeftMoment {p L t : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2) (hL : 0 < L)
    (ht : 0 < t) (j : ℕ) :
    HasDerivAt (imageLeftMoment p L j) (-imageLeftMoment p L (j + 1) t) t := by
  convert (hasDerivAt_imageMoment hp hp₂ hL ht .a j).sub
    ((hasDerivAt_imageMoment hp hp₂ hL ht .b j).div_const 4) using 1
  dsimp [imageLeftMoment]
  ring

theorem hasDerivAt_imageRightMoment {p L t : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2) (hL : 0 < L)
    (ht : 0 < t) (j : ℕ) :
    HasDerivAt (imageRightMoment p L j) (-imageRightMoment p L (j + 1) t) t := by
  convert (hasDerivAt_imageMoment hp hp₂ hL ht .b j).sub
    ((hasDerivAt_imageMoment hp hp₂ hL ht .a j).div_const 4) using 1
  dsimp [imageRightMoment]
  ring

private theorem imageMoment_zero_le_quartic {p L C t : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (ht : 0 < t) (hC : ∀ s > 0, imageDensity p L s ≤ C * s)
    (kind : CircleKernelKind) :
    imageMoment p L kind 0 t ≤ 3 * C / t ^ 4 := by
  calc
    imageMoment p L kind 0 t ≤
        ∫ s : ℝ in Ioi 0, (C / 2) * (s ^ (3 : ℕ) * Real.exp (-s * t)) := by
      apply integral_mono_ae (imageMoment_integrable hp hp₂ hL ht kind 0)
        ((CenteredCircle.AllN.integrable_power_exponential 3 t ht).const_mul (C / 2))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have h := imageMomentWeight_bound hp hL hs hC kind 0
      calc
        _ ≤ |imageMomentWeight p L kind 0 s| * Real.exp (-s * t) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
        _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = _ := by
      rw [integral_const_mul, CenteredCircle.AllN.integral_power_exponential 3 t ht]
      norm_num
      ring

theorem imageMoment_samples_summable {p L t s : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (ht : 0 < t) (hs : 0 < s) (kind : CircleKernelKind) :
    Summable (fun j : ℕ => imageMoment p L kind 0 (t + (j : ℝ) * s)) := by
  obtain ⟨C, hC₀, hC⟩ := imageDensity_linear_bound hp hp₂ hL
  exact CenteredCircle.AllN.summable_of_power_decay
    (imageMoment p L kind 0) (3 * C) t s 4 (by norm_num) (by positivity) ht hs
    (fun t ht => (imageMoment_pos hp hp₂ hL ht kind 0).le)
    (fun t ht => imageMoment_zero_le_quartic hp hp₂ hL ht hC kind)

private theorem quadratureData_of_moment_family {p L d : ℝ}
    (hp : 0 < p) (hp₂ : p ≤ 2) (hL : 0 < L) (hd : 0 < d)
    (M : ℕ → ℝ → ℝ) (kind : CircleKernelKind)
    (hder : ∀ j t, 0 < t → HasDerivAt (M j) (-M (j + 1) t) t)
    (hpos : ∀ j ≤ 2, ∀ t, d ≤ t → 0 < M j t)
    (hupper : ∀ t, 0 < t → M 0 t ≤ imageMoment p L kind 0 t) :
    CenteredCircle.AllN.QuadratureData (M 0) d := by
  obtain ⟨C, hC₀, hC⟩ := imageDensity_linear_bound hp hp₂ hL
  have hc : StrictConvexOn ℝ (Ici d) (M 0) := by
    apply strictConvexOn_of_deriv2_pos' (convex_Ici d)
    · exact fun t ht => (hder 0 t (hd.trans_le ht)).continuousAt.continuousWithinAt
    · intro t ht
      have ht' : d ≤ t := ht
      have ht₀ : 0 < t := hd.trans_le ht'
      have he : deriv (M 0) =ᶠ[𝓝 t] fun x => -M 1 x := by
        filter_upwards [Ioi_mem_nhds ht₀] with x hx
        exact (hder 0 x hx).deriv
      have h := ((hder 1 t ht₀).neg).congr_of_eventuallyEq he
      change 0 < deriv (deriv (M 0)) t
      rw [h.deriv, neg_neg]
      exact hpos 2 le_rfl t ht'
  apply CenteredCircle.AllN.convex_cubic_quadratureData (C := 3 * C / d) hd (by positivity)
    hc.convexOn
  · exact fun x hx => (hpos 0 (by norm_num) x hx).le
  · exact fun x hx => (hder 0 x (hd.trans_le hx)).differentiableAt
  · intro x hx
    have hx₀ : 0 < x := hd.trans_le hx
    have hpow : d * x ^ 3 ≤ x ^ 4 := by
      rw [show x ^ (4 : ℕ) = x * x ^ 3 by ring]
      exact mul_le_mul_of_nonneg_right hx (by positivity)
    calc
      M 0 x ≤ 3 * C / x ^ 4 :=
        (hupper x hx₀).trans (imageMoment_zero_le_quartic hp hp₂ hL hx₀ hC kind)
      _ ≤ 3 * C / (d * x ^ 3) := div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
      _ = _ := (div_div _ _ _).symm
  · intro x s hx hs
    have hsum := imageMoment_samples_summable hp hp₂ hL (hd.trans_le hx) hs kind
    have hxj (j : ℕ) : d ≤ x + (j : ℝ) * s := hx.trans (le_add_of_nonneg_right (by positivity))
    exact Summable.of_nonneg_of_le
      (fun j => (hpos 0 (by norm_num) _ (hxj j)).le)
      (fun j => hupper _ (hd.trans_le (hxj j))) hsum

theorem imageLeft_quadratureData {p L : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2) (hL : 0 < L) :
    CenteredCircle.AllN.QuadratureData (imageLeftMoment p L 0) 1 := by
  apply quadratureData_of_moment_family hp hp₂ hL zero_lt_one (imageLeftMoment p L) .a
  · exact fun j _ ht => hasDerivAt_imageLeftMoment hp hp₂ hL ht j
  · exact fun j hj _ ht => imageLeftMoment_pos hp hp₂ hL ht j hj
  · intro t ht
    have h := imageMoment_pos hp hp₂ hL ht .b 0
    unfold imageLeftMoment
    linarith

theorem imageRight_quadratureData {p L d : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hd : 0 < d) :
    CenteredCircle.AllN.QuadratureData (imageRightMoment p L 0) d := by
  apply quadratureData_of_moment_family hp hp₂ hL hd (imageRightMoment p L) .b
  · exact fun j _ ht => hasDerivAt_imageRightMoment hp hp₂ hL ht j
  · exact fun j _ _ ht => imageRightMoment_pos hp hp₂ hL (hd.trans_le ht) j
  · intro t ht
    have h := imageMoment_pos hp hp₂ hL ht .a 0
    unfold imageRightMoment
    linarith

end ACS12.GammaMeasure

import ACS12.SpeedComparison
import ACS12.SignedSampling

/-! The shared positive Peano kernels along the exact original law path. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter

noncomputable def lawMoment (p L θ : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  ∫ s : ℝ in Ioi 0, lawDensity p L θ s * s ^ j * Real.exp (-s * t)

theorem lawMoment_integrable {p L θ t : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hL : 0 < L)
    (hθ : θ ∈ Icc (0 : ℝ) 1) (ht : 0 < t) (j : ℕ) :
    IntegrableOn (fun s => lawDensity p L θ s * s ^ j * Real.exp (-s * t)) (Ioi 0) := by
  obtain ⟨B, _, hB⟩ := lawDensity_linear_envelope hp hp₂ hL hθ
  have hI := ((expMoment_nat_integrable j ht).add (expMoment_nat_integrable (j + 1) ht)).const_mul B
  have hM := lawDensity_measurable (zero_lt_one.trans_le hp) hL (θ := θ)
  refine hI.mono' ((hM.mul (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs₀ : 0 < s := hs
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hs₀.le _),
    abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ B * (1 + s) * s ^ j * Real.exp (-s * t) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hB s hs₀)
        (pow_nonneg hs₀.le _)) (Real.exp_pos _).le
    _ = _ := by simp only [Pi.add_apply, pow_succ]; ring

theorem lawMoment_pos {p L θ t : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hL : 0 < L)
    (hθ : θ ∈ Icc (0 : ℝ) 1) (ht : 0 < t) (j : ℕ) :
    0 < lawMoment p L θ j t := by
  letI : NeZero (volume.restrict (Ioi (0 : ℝ))) := ⟨positiveHalfLine_ne_zero⟩
  have h := integral_strict_of_ae_lt (volume.restrict (Ioi (0 : ℝ))) (integrable_zero ℝ ℝ _)
    (lawMoment_integrable hp hp₂ hL hθ ht j) ?_
  · simpa only [lawMoment, integral_zero] using h
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    change 0 < s at hs
    exact mul_pos (mul_pos (lawDensity_pos (zero_lt_one.trans_le hp) hL hθ hs) (pow_pos hs _))
      (Real.exp_pos _)

@[simp] theorem lawMoment_one_radial (p L t : ℝ) :
    lawMoment p L 1 0 t = imagePotential p L t := by
  simp only [lawMoment, lawDensity, sub_self, zero_mul, one_mul, zero_add, pow_zero,
    mul_one, imagePotential]

@[simp] theorem lawMoment_one_slope (p L t : ℝ) :
    lawMoment p L 1 1 t = imageSlope p L t := by
  simp only [lawMoment, lawDensity, sub_self, zero_mul, one_mul, zero_add, pow_one, imageSlope]

noncomputable def lawPeanoDensity (p L θ h : ℝ) (kind : CircleKernelKind) (s : ℝ) : ℝ :=
  lawDensity p L θ s * densityPolynomial kind (h * s)

noncomputable def lawPeanoKernel (p L θ h : ℝ) (kind : CircleKernelKind) : ℝ → ℝ :=
  signedLaplace (lawPeanoDensity p L θ h kind)

@[simp] theorem lawPeanoKernel_one (p L h : ℝ) (kind : CircleKernelKind) :
    lawPeanoKernel p L 1 h kind = peanoKernel p L h kind := by
  funext t
  simp only [lawPeanoKernel, signedLaplace, lawPeanoDensity, lawDensity, sub_self,
    zero_mul, one_mul, zero_add, peanoKernel, peanoDensity]

theorem lawPeanoDensity_pos {p L θ h s : ℝ} (hp : 0 < p) (hL : 0 < L)
    (hθ : θ ∈ Icc (0 : ℝ) 1) (hh : 0 < h) (hs : 0 < s) (kind : CircleKernelKind) :
    0 < lawPeanoDensity p L θ h kind s := mul_pos (lawDensity_pos hp hL hθ hs)
      (densityPolynomial_pos kind (mul_pos hh hs))

theorem lawPeanoDensity_measurable {p L θ h : ℝ} (hp : 0 < p) (hL : 0 < L) (kind : CircleKernelKind) :
    Measurable (lawPeanoDensity p L θ h kind) :=
  (lawDensity_measurable hp hL).mul ((continuous_densityPolynomial kind).measurable.comp
    (measurable_id.const_mul h))

private theorem densityPolynomial_le_linear {x : ℝ} (hx : 0 < x) (kind : CircleKernelKind) :
    densityPolynomial kind x ≤ x := by
  have h : polyB x ≤ x := by
    unfold polyB
    linarith [Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx)]
  cases kind
  · exact (polyA_lt_polyB hx).le.trans h
  · exact h

theorem lawPeanoDensity_quadratic_bound {p L θ h : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hh : 0 < h) (kind : CircleKernelKind) :
    ∃ B ≥ 0, ∀ s > 0, |lawPeanoDensity p L θ h kind s| ≤ B * s ^ 2 := by
  obtain ⟨B, hB, hBound⟩ := lawDensity_linear_envelope hp hp₂ hL hθ
  refine ⟨B * (h ^ 2 + 2 * h), by positivity, ?_⟩
  intro s hs
  have hhs := mul_pos hh hs
  have hp₀ := zero_lt_one.trans_le hp
  have hW : lawDensity p L θ s ≤ B * (1 + s) := by
    simpa only [abs_of_pos (lawDensity_pos hp₀ hL hθ hs)] using hBound s hs
  have hD := (densityPolynomial_pos kind hhs).le
  rw [abs_of_pos (lawPeanoDensity_pos hp₀ hL hθ hh hs kind), lawPeanoDensity]
  rcases le_total s 1 with hs₁ | hs₁
  · have hWB : lawDensity p L θ s ≤ B * 2 :=
      hW.trans (mul_le_mul_of_nonneg_left (by linarith) hB)
    calc
      _ ≤ B * 2 * ((h * s) ^ 2 / 2) :=
        mul_le_mul hWB (densityPolynomial_lt_quadratic kind hhs).le hD (by positivity)
      _ = B * h ^ 2 * s ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (mul_nonneg zero_le_two hh.le)) hB) (sq_nonneg s)
  · have hWB : lawDensity p L θ s ≤ B * (2 * s) :=
      hW.trans (mul_le_mul_of_nonneg_left (by linarith) hB)
    calc
      _ ≤ B * (2 * s) * (h * s) :=
        mul_le_mul hWB (densityPolynomial_le_linear hhs kind) hD (by positivity)
      _ = B * (2 * h) * s ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (sq_nonneg h)) hB) (sq_nonneg s)

theorem lawPeanoKernel_integrable {p L θ h t : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hh : 0 < h) (ht : 0 < t)
    (kind : CircleKernelKind) :
    IntegrableOn (fun s => lawPeanoDensity p L θ h kind s * Real.exp (-s * t)) (Ioi 0) := by
  obtain ⟨B, _, hB⟩ := lawPeanoDensity_quadratic_bound hp hp₂ hL hθ hh kind
  exact integrable_weighted_exponential_of_abs_bound _ B t 2
    (lawPeanoDensity_measurable (zero_lt_one.trans_le hp) hL kind) hB ht

theorem lawPeanoKernel_pos {p L θ h t : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hh : 0 < h) (ht : 0 < t) (kind : CircleKernelKind) :
    0 < lawPeanoKernel p L θ h kind t := by
  letI : NeZero (volume.restrict (Ioi (0 : ℝ))) := ⟨positiveHalfLine_ne_zero⟩
  have h := integral_strict_of_ae_lt (volume.restrict (Ioi (0 : ℝ))) (integrable_zero ℝ ℝ _)
    (lawPeanoKernel_integrable hp hp₂ hL hθ hh ht kind) ?_
  · simpa only [lawPeanoKernel, signedLaplace, integral_zero] using h
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_pos (lawPeanoDensity_pos (zero_lt_one.trans_le hp) hL hθ hh hs kind) (Real.exp_pos _)

theorem lawPeanoTail_sampling {p L θ h t q : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hh : 0 < h) (ht : 0 ≤ t) (hq : 0 < q)
    (kind : CircleKernelKind) :
    IntegrableOn (fun s => lawPeanoDensity p L θ h kind s * Real.exp (-s * t) * scaledExpTail s q) (Ioi 0) ∧
      samplingTail (lawPeanoKernel p L θ h kind) t q =
        ∫ s : ℝ in Ioi 0, lawPeanoDensity p L θ h kind s * Real.exp (-s * t) * scaledExpTail s q := by
  obtain ⟨B, _, hB⟩ := lawPeanoDensity_quadratic_bound hp hp₂ hL hθ hh kind
  exact signedTail_sampling (lawPeanoDensity_measurable (zero_lt_one.trans_le hp) hL kind) hB ht hq

theorem lawPeanoTail_derivative {p L θ h t q : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hh : 0 < h) (ht : 0 ≤ t) (hq : 0 < q)
    (kind : CircleKernelKind) :
    HasDerivAt (samplingTail (lawPeanoKernel p L θ h kind) t)
      (-(∫ s : ℝ in Ioi 0, lawPeanoDensity p L θ h kind s *
        Real.exp (-s * t) * BoseShape.C (s * q))) q := by
  obtain ⟨B, _, hB⟩ := lawPeanoDensity_quadratic_bound hp hp₂ hL hθ hh kind
  exact signedTail_derivative (lawPeanoDensity_measurable (zero_lt_one.trans_le hp) hL kind) hB ht hq

end ACS12.GammaMeasure


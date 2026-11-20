import ACS12.GammaOrder
import ACS12.GammaTorque
import CenteredCircle.DensitySampling

/-! Positive Peano kernels for any actual edge length in the same period. -/

namespace ACS12.GammaMeasure

open MeasureTheory Set Filter
open CenteredCircle.AllN

noncomputable def peanoDensity (p L h : ℝ) (kind : CircleKernelKind) (s : ℝ) : ℝ :=
  imageDensity p L s * densityPolynomial kind (h * s)

noncomputable def peanoKernel (p L h : ℝ) (kind : CircleKernelKind) (t : ℝ) : ℝ :=
  ∫ s : ℝ in Ioi 0, peanoDensity p L h kind s * Real.exp (-s * t)

private theorem densityPolynomial_le_id {s : ℝ} (hs : 0 < s) (kind : CircleKernelKind) :
    densityPolynomial kind s ≤ s := by
  have hb : polyB s < s := by
    unfold polyB
    linarith [Real.exp_lt_one_iff.mpr (neg_neg_of_pos hs)]
  cases kind
  · exact ((polyA_lt_polyB hs).trans hb).le
  · exact hb.le

private theorem peanoDensity_properties {p L h : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hh : 0 < h) (kind : CircleKernelKind) :
    Measurable (peanoDensity p L h kind) ∧ (∀ s > 0, 0 < peanoDensity p L h kind s) ∧
      ∃ C ≥ 0, ∀ s > 0, peanoDensity p L h kind s ≤ C * s ^ 2 := by
  obtain ⟨C, hC₀, hC⟩ := imageDensity_linear_bound hp hp₂ hL
  refine ⟨?_, fun s hs => mul_pos (imageDensity_pos hp hL hs)
    (densityPolynomial_pos kind (mul_pos hh hs)), C * h, by positivity, ?_⟩
  · exact ((continuous_imageDensity hp hL).mul ((continuous_densityPolynomial kind).comp
      (continuous_const.mul continuous_id))).measurable
  · intro s hs
    calc
      _ ≤ (C * s) * (h * s) := mul_le_mul (hC s hs) (densityPolynomial_le_id (mul_pos hh hs) kind)
        (densityPolynomial_pos kind (mul_pos hh hs)).le ((imageDensity_pos hp hL hs).le.trans (hC s hs))
      _ = _ := by ring

private theorem laplace_peanoDensity {p L h : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hh : 0 < h) (kind : CircleKernelKind) :
    laplaceKernel (densityMeasure (peanoDensity p L h kind)) = peanoKernel p L h kind := by
  obtain ⟨hm, hpos, _⟩ := peanoDensity_properties hp hp₂ hL hh kind
  funext t
  exact laplace_density_integral _ hm (fun s hs => (hpos s hs).le) t

theorem peanoKernel_sampling {p L h d : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hh : 0 < h) (hd : 0 < d) (kind : CircleKernelKind) :
    IntegrableOn (fun s => peanoDensity p L h kind s * scaledExpTail s d) (Ioi 0) ∧
      samplingTail (peanoKernel p L h kind) 0 d =
        ∫ s : ℝ in Ioi 0, peanoDensity p L h kind s * scaledExpTail s d := by
  obtain ⟨hm, hpos, C, hC, hbound⟩ := peanoDensity_properties hp hp₂ hL hh kind
  rw [← laplace_peanoDensity hp hp₂ hL hh kind]
  exact density_sampling_formula _ C hm hpos hbound hC hd

theorem peanoKernel_quadratureData {p L h d : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hh : 0 < h) (hd : 0 < d) (kind : CircleKernelKind) :
    QuadratureData (peanoKernel p L h kind) d := by
  obtain ⟨hm, hpos, C, hC, hbound⟩ := peanoDensity_properties hp hp₂ hL hh kind
  let g := peanoDensity p L h kind
  let μ := densityMeasure g
  have hg₀ (s : ℝ) (hs : 0 < s) : 0 ≤ g s := (hpos s hs).le
  have hae := densityMeasure_positive_support g hm
  letI : NeZero μ := ⟨densityMeasure_ne_zero g hm hpos⟩
  have hi (t : ℝ) (ht : 0 < t) : Integrable (fun s : ℝ => Real.exp (-s * t)) μ :=
    integrable_exp_density g C t hm hg₀ hbound ht
  have hsum (t s : ℝ) (ht : 0 < t) (hs : 0 < s) :
      Summable (fun j : ℕ => laplaceKernel μ (t + j * s)) :=
    summable_laplace_density g C t s hm hg₀ hbound hC ht hs
  rw [← laplace_peanoDensity hp hp₂ hL hh kind]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t _
    exact integral_nonneg fun s => (Real.exp_pos (-s * t)).le
  · exact fun t s ht hs => hsum t s (hd.trans_le ht) hs
  · exact fun t ht => (strictMonoOn_samplingHead_laplace μ t (hd.trans_le ht) hae hi
      (fun s hs => hsum t s (hd.trans_le ht) hs)).monotoneOn
  · exact fun t ht => (strictAntiOn_samplingTail_laplace μ t (hd.le.trans ht) hae hi hsum).antitoneOn
  · exact (strictAntiOn_samplingTail_laplace μ 0 le_rfl hae hi hsum).antitoneOn.mono
      (fun t ht => hd.trans_le ht)

theorem peanoKernel_a_eq {p L h t : ℝ} (hp : 0 < p) (hL : 0 < L)
    (hh : 0 < h) (ht : 0 < t) :
    peanoKernel p L h .a t = imagePotential p L t - imagePotential p L (t + h) -
      h * imageSlope p L (t + h) := by
  have h₁ := imagePotential_integrable hp hL ht
  have h₂ := imagePotential_integrable hp hL (add_pos ht hh)
  have h₃ := imageSlope_integrable hp hL (add_pos ht hh)
  unfold peanoKernel imagePotential imageSlope
  rw [← integral_const_mul, ← integral_sub h₁ h₂]
  refine Eq.trans ?_ (integral_sub (h₁.sub h₂) (h₃.const_mul h))
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s _
  dsimp [Pi.sub_apply, peanoDensity, densityPolynomial, polyA]
  rw [show -s * (t + h) = -s * t + -(h * s) by ring, Real.exp_add]
  ring

theorem peanoKernel_b_eq {p L h t : ℝ} (hp : 0 < p) (hL : 0 < L)
    (hh : 0 < h) (ht : 0 < t) :
    peanoKernel p L h .b t = h * imageSlope p L t -
      (imagePotential p L t - imagePotential p L (t + h)) := by
  have h₁ := imagePotential_integrable hp hL ht
  have h₂ := imagePotential_integrable hp hL (add_pos ht hh)
  have h₃ := imageSlope_integrable hp hL ht
  unfold peanoKernel imagePotential imageSlope
  rw [← integral_const_mul, ← integral_sub h₁ h₂]
  refine Eq.trans ?_ (integral_sub (h₃.const_mul h) (h₁.sub h₂))
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s _
  dsimp [Pi.sub_apply, peanoDensity, densityPolynomial, polyB]
  rw [show -s * (t + h) = -s * t + -(h * s) by ring, Real.exp_add]
  ring

theorem peanoKernel_antitone {p L h : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hh : 0 < h) (kind : CircleKernelKind) :
    AntitoneOn (peanoKernel p L h kind) (Ioi 0) := by
  obtain ⟨hm, hpos, C, _, hbound⟩ := peanoDensity_properties hp hp₂ hL hh kind
  let g := peanoDensity p L h kind
  let μ := densityMeasure g
  have hi (t : ℝ) (ht : 0 < t) : Integrable (fun s : ℝ => Real.exp (-s * t)) μ :=
    integrable_exp_density g C t hm (fun s hs => (hpos s hs).le) hbound ht
  intro x hx y hy hxy
  rw [← laplace_peanoDensity hp hp₂ hL hh kind]
  change (∫ s : ℝ, Real.exp (-s * y) ∂μ) ≤ ∫ s : ℝ, Real.exp (-s * x) ∂μ
  apply integral_mono_ae (hi y hy) (hi x hx)
  filter_upwards [densityMeasure_positive_support g hm] with s hs
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left hxy (neg_nonpos.mpr hs.le)

theorem peanoHead_le_tail {p L h m r v : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hh : 0 < h) (hm : 0 < m) (hr : 0 < r) (hmv : m ≤ v) (hrv : r ≤ v)
    (kind : CircleKernelKind) :
    samplingHead (peanoKernel p L h kind) v r ≤ samplingTail (peanoKernel p L h kind) 0 m := by
  let K := peanoKernel p L h kind
  let d := min m r
  have hd : 0 < d := lt_min hm hr
  have hdm : d ≤ m := min_le_left _ _
  have hdr : d ≤ r := min_le_right _ _
  have hdv : d ≤ v := hdm.trans hmv
  have hK := peanoKernel_quadratureData hp hp₂ hL hh hd kind
  have hHead (x y s : ℝ) (hx : d ≤ x) (hxy : x ≤ y) (hs : 0 < s) :
      samplingHead K y s ≤ samplingHead K x s := by
    unfold samplingHead
    apply mul_le_mul_of_nonneg_left _ hs.le
    exact (hK.summable y s (hx.trans hxy) hs).tsum_le_tsum
      (fun j => peanoKernel_antitone hp hp₂ hL hh kind
        (show 0 < x + (j : ℝ) * s from add_pos_of_pos_of_nonneg (hd.trans_le hx) (by positivity))
        (show 0 < y + (j : ℝ) * s from add_pos_of_pos_of_nonneg (hd.trans_le (hx.trans hxy)) (by positivity))
        (add_le_add hxy le_rfl)) (hK.summable x s hx hs)
  rcases le_total r m with hrm | hmr
  · rw [samplingTail_eq_shift, zero_add]
    exact (hK.head_mono v hdv hr hm hrm).trans (hHead m v m hdm hmv hm)
  · have h := hK.boundary_anti hdm hdr hmr
    rw [samplingTail_eq_shift, zero_add] at h
    exact (hHead r v r hdr hrv hr).trans h

end ACS12.GammaMeasure

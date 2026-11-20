import ACS12.GammaPeriodization
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! The Abel boundary of the difference between the line and image
potentials, with the original positive self term retained. -/

namespace ACS12.GammaMeasure

open MeasureTheory Set Filter
open scoped Topology
open CenteredCircle.AllN (imageTail imageTail_split periodic_angle_sin_pos)

noncomputable def imageTailIntegrand (p L t s : ℝ) : ℝ :=
  imageDensity p L s * (Real.exp (-s * t) / (1 - Real.exp (-s * L)))

theorem imageTailIntegrand_integrable {p L t : ℝ} (hp : 0 < p)
    (hL : 0 < L) (ht : 0 < t) : IntegrableOn (imageTailIntegrand p L t) (Ioi 0) := by
  let d := min t (L / 2)
  have hd : 0 < d := lt_min ht (by positivity)
  have hdL : d < L := (min_le_right _ _).trans_lt (by linarith)
  have hdt : d ≤ t := min_le_left _ _
  refine (imageRowIntegrable hp hL hd hdL).mono' ?_ ?_
  · unfold imageTailIntegrand
    exact ((continuous_imageDensity hp hL).measurable.mul
      ((by fun_prop : Measurable (fun s : ℝ => Real.exp (-s * t))).div
        (by fun_prop))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    change 0 < s at hs
    have hw := (imageDensity_pos hp hL hs).le
    have hden : 0 < 1 - Real.exp (-s * L) :=
      sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))
    rw [imageTailIntegrand, Real.norm_of_nonneg (by positivity), imageRowIntegrand]
    apply mul_le_mul_of_nonneg_left _ hw
    apply div_le_div_of_nonneg_right _ hden.le
    exact (Real.exp_le_exp.mpr (by nlinarith)).trans
      (le_add_of_nonneg_right (Real.exp_pos _).le)

theorem imageTail_integral {p L t : ℝ} (hp : 0 < p) (hL : 0 < L) (ht : 0 < t) :
    imageTail (imagePotential p L) L t = ∫ s : ℝ in Ioi 0, imageTailIntegrand p L t s :=
  (hasSum_laplace_samples (imageDensity p L) (continuous_imageDensity hp hL).measurable
    (fun _ hs => (imageDensity_pos hp hL hs).le) hL
    (imageTailIntegrand_integrable hp hL ht)).tsum_eq

private theorem continuousAt_imageTail {p L t : ℝ} (hp : 0 < p) (hL : 0 < L) (ht : 0 < t) :
    ContinuousAt (imageTail (imagePotential p L) L) t := by
  have hd : 0 < t / 2 := by positivity
  have ht2 : t / 2 < t := by linarith
  have hpos : ∀ᶠ x : ℝ in 𝓝 t, 0 < x := Ioi_mem_nhds ht
  have hlim : Tendsto (fun x => ∫ s : ℝ in Ioi 0, imageTailIntegrand p L x s) (𝓝 t)
      (𝓝 (∫ s : ℝ in Ioi 0, imageTailIntegrand p L t s)) := by
    apply tendsto_integral_filter_of_dominated_convergence (imageTailIntegrand p L (t / 2))
    · exact Eventually.of_forall fun x => by
        unfold imageTailIntegrand
        exact ((continuous_imageDensity hp hL).measurable.mul
          ((by fun_prop : Measurable (fun s : ℝ => Real.exp (-s * x))).div
            (by fun_prop))).aestronglyMeasurable
    · filter_upwards [Ioi_mem_nhds ht2] with x hx
      change t / 2 < x at hx
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      change 0 < s at hs
      have hw := (imageDensity_pos hp hL hs).le
      have hden : 0 < 1 - Real.exp (-s * L) :=
        sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))
      simp only [imageTailIntegrand, Real.norm_of_nonneg
        (mul_nonneg hw (div_nonneg (Real.exp_pos _).le hden.le))]
      apply mul_le_mul_of_nonneg_left _ hw
      exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith)) hden.le
    · exact imageTailIntegrand_integrable hp hL hd
    · exact Eventually.of_forall fun s =>
        (by unfold imageTailIntegrand; fun_prop : Continuous
          (fun x => imageTailIntegrand p L x s)).continuousAt.tendsto
  rw [← imageTail_integral hp hL ht] at hlim
  refine hlim.congr' ?_
  exact hpos.mono fun x hx => (imageTail_integral hp hL hx).symm

theorem imageSelf_eq_tail (p L : ℝ) :
    imageSelf p L = 2 * imageTail (imagePotential p L) L L := by
  unfold imageSelf imageTail
  congr 1
  apply tsum_congr
  intro j
  congr 1
  ring

private theorem circlePower_difference_bound {p L t : ℝ} (hp : 0 < p) (hp₂ : p < 2)
    (hL : 0 < L) (ht : 0 < t) (htL : t < L) (hsmall : (Real.pi / L) * t ≤ 1) :
    |t ^ (-p) - circlePower p L t| ≤ (2 * (Real.pi / L) ^ 2) * t ^ (2 - p) := by
  let k := Real.pi / L
  let x := k * t
  have hk : 0 < k := div_pos Real.pi_pos hL
  have hx : 0 < x := mul_pos hk ht
  have hx₁ : x ≤ 1 := hsmall
  have hArg : Real.pi * t / L = x := by dsimp [x, k]; ring
  have hs : 0 < Real.sin x := hArg ▸ periodic_angle_sin_pos hL ht htL
  have hsx : Real.sin x ≤ x := by
    simpa only [abs_of_pos hs, abs_of_pos hx] using (Real.abs_sin_le_abs (x := x))
  have hsin := Real.sin_gt_sub_cube hx hx₁
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hx₁)]
  have hhalf : x / 2 ≤ Real.sin x := by
    have h := mul_le_mul_of_nonneg_left hx2 hx.le
    nlinarith
  have hfac : circlePower p L t = t ^ (-p) * (x / Real.sin x) ^ p := by
    unfold circlePower
    rw [hArg, Real.rpow_neg ht.le, Real.div_rpow hx.le hs.le]
    change k ^ p / Real.sin x ^ p = (t ^ p)⁻¹ * ((k * t) ^ p / Real.sin x ^ p)
    rw [Real.mul_rpow hk.le ht.le]
    field_simp [(Real.rpow_pos_of_pos ht p).ne', (Real.rpow_pos_of_pos hs p).ne']
  have hratio : 1 ≤ x / Real.sin x :=
    (le_div_iff₀ hs).mpr (by simpa only [one_mul] using hsx)
  have hpow : 1 ≤ (x / Real.sin x) ^ p := Real.one_le_rpow hratio hp.le
  have hpow' : (x / Real.sin x) ^ p ≤ (x / Real.sin x) ^ 2 :=
    (Real.rpow_le_rpow_of_exponent_le hratio hp₂.le).trans_eq (Real.rpow_two _)
  have hratio₂ : x / Real.sin x ≤ 2 := (div_le_iff₀ hs).mpr (by linarith)
  have hgap : x / Real.sin x - 1 ≤ x ^ 2 / 2 := by
    calc
      _ = (x - Real.sin x) / Real.sin x := by field_simp [hs.ne']
      _ ≤ (x ^ 3 / 4) / Real.sin x := div_le_div_of_nonneg_right (by linarith) hs.le
      _ ≤ (x ^ 3 / 4) / (x / 2) := div_le_div_of_nonneg_left (by positivity) (by positivity) hhalf
      _ = _ := by field_simp [hx.ne']; norm_num
  have hgap₂ : (x / Real.sin x) ^ 2 - 1 ≤ 2 * x ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hratio) (sub_nonneg.mpr hratio₂), sq_nonneg x]
  have htpos := (Real.rpow_pos_of_pos ht (-p)).le
  have hnonpos : t ^ (-p) - circlePower p L t ≤ 0 := by
    rw [hfac]
    linarith [mul_le_mul_of_nonneg_left hpow htpos]
  rw [abs_of_nonpos hnonpos, neg_sub, hfac]
  calc
    _ = t ^ (-p) * ((x / Real.sin x) ^ p - 1) := by ring
    _ ≤ t ^ (-p) * (2 * x ^ 2) :=
      mul_le_mul_of_nonneg_left ((sub_le_sub_right hpow' 1).trans hgap₂) htpos
    _ = (2 * k ^ 2) * (t ^ (-p) * t ^ (2 : ℕ)) := by dsimp [x]; ring
    _ = _ := by rw [← Real.rpow_two t, ← Real.rpow_add ht, show -p + 2 = 2 - p by ring]

private theorem tendsto_circlePower_difference {p L : ℝ} (hp : 0 < p) (hp₂ : p < 2)
    (hL : 0 < L) :
    Tendsto (fun t : ℝ => t ^ (-p) - circlePower p L t) (𝓝[>] 0) (𝓝 0) := by
  let k := Real.pi / L
  have hk : 0 < k := div_pos Real.pi_pos hL
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hlt : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < L :=
    (show ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), t < L from Iio_mem_nhds hL).filter_mono
      nhdsWithin_le_nhds
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), k * t ≤ 1 := by
    have hcont : ContinuousAt (fun t : ℝ => k * t) 0 := by fun_prop
    have h := hcont.tendsto
    simp only [mul_zero] at h
    exact ((h.eventually (Iio_mem_nhds zero_lt_one)).mono fun _ hx => hx.le).filter_mono
      nhdsWithin_le_nhds
  have hpow : 0 < 2 - p := by linarith
  have h := (Real.continuousAt_rpow_const 0 (2 - p) (Or.inr hpow.le)).tendsto.const_mul (2 * k ^ 2)
  simp only [Real.zero_rpow hpow.ne', mul_zero] at h
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ (h.mono_left nhdsWithin_le_nhds)
  filter_upwards [hpos, hlt, hsmall] with t ht htL htS
  simpa only [Real.norm_eq_abs] using circlePower_difference_bound hp hp₂ hL ht htL htS

/-- The line-minus-image potential tends to the literal radial self term.
The limit is taken on the positive side of the singular point. -/
theorem tendsto_line_sub_imagePotential_of_lt_two {p L : ℝ} (hp : 0 < p) (hp₂ : p < 2)
    (hL : 0 < L) :
    Tendsto (fun t : ℝ => t ^ (-p) - imagePotential p L t) (𝓝[>] 0) (𝓝 (imageSelf p L)) := by
  have hplus : Tendsto (fun t : ℝ => t + L) (𝓝[>] 0) (𝓝 L) := by
    have h : ContinuousAt (fun t : ℝ => t + L) 0 := by fun_prop
    simpa only [zero_add] using h.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hminus : Tendsto (fun t : ℝ => L - t) (𝓝[>] 0) (𝓝 L) := by
    have h : ContinuousAt (fun t : ℝ => L - t) 0 := by fun_prop
    simpa only [sub_zero] using h.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hTail := (continuousAt_imageTail hp hL hL).tendsto
  have h := ((tendsto_circlePower_difference hp hp₂ hL).add (hTail.comp hplus)).add
    (hTail.comp hminus)
  simp only [zero_add, ← two_mul, ← imageSelf_eq_tail] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), t < L from Iio_mem_nhds hL).filter_mono
      nhdsWithin_le_nhds] with t ht htL
  have ht₀ : 0 < t := ht
  have htL' : t < L := htL
  have hpair := imagePotential_pair hp hL ht₀ htL'
  rw [imageTail_split _ _ _ (imagePotential_samples_summable hp hL ht₀)] at hpair
  change t ^ (-p) - circlePower p L t + imageTail (imagePotential p L) L (t + L) +
    imageTail (imagePotential p L) L (L - t) = t ^ (-p) - imagePotential p L t
  linarith

theorem tendsto_line_sub_imagePotential {p L : ℝ} (hp : 0 < p) (hp₁ : p ≤ 1)
    (hL : 0 < L) :
    Tendsto (fun t : ℝ => t ^ (-p) - imagePotential p L t) (𝓝[>] 0) (𝓝 (imageSelf p L)) :=
  tendsto_line_sub_imagePotential_of_lt_two hp (hp₁.trans_lt (by norm_num)) hL

end ACS12.GammaMeasure

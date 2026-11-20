import ACS12.GammaBoseWeight
import ACS12.GammaLowSource

/-! The exact mixed deficit at a finite period, including its self correction. -/

namespace ACS12.GammaDeficit

open MeasureTheory Set Filter
open CenteredCircle.AllN
open ACS12.GammaMeasure

set_option backward.isDefEq.respectTransparency false

private theorem imageMoment_density_sampling {p L b : ℝ}
    (hp : 0 < p) (hp₂ : p ≤ 2) (hL : 0 < L) (hb : 0 < b) (kind : CircleKernelKind) :
    IntegrableOn (fun s => imageDensity p L s * densityPolynomial kind s * scaledExpTail s b)
      (Ioi 0) ∧ samplingTail (imageMoment p L kind 0) 0 b =
        ∫ s : ℝ in Ioi 0, imageDensity p L s * densityPolynomial kind s * scaledExpTail s b := by
  let g (s : ℝ) := imageDensity p L s * densityPolynomial kind s
  have hg : Measurable g := ((continuous_imageDensity hp hL).mul
    (continuous_densityPolynomial kind)).measurable
  have hpos (s : ℝ) (hs : 0 < s) : 0 < g s :=
    mul_pos (imageDensity_pos hp hL hs) (densityPolynomial_pos kind hs)
  have hK : laplaceKernel (densityMeasure g) = imageMoment p L kind 0 := by
    funext t
    rw [laplace_density_integral g hg (fun s hs => (hpos s hs).le)]
    simp only [imageMoment, imageMomentWeight, pow_zero, one_mul, g]
  obtain ⟨C, hC₀, hC⟩ := imageDensity_linear_bound hp hp₂ hL
  have hbound (s : ℝ) (hs : 0 < s) : g s ≤ C * s ^ 2 := by
    have hB : polyB s < s := by
      unfold polyB
      linarith [Real.exp_lt_one_iff.mpr (neg_neg_of_pos hs)]
    have hpoly : densityPolynomial kind s ≤ s := by
      cases kind
      · exact ((polyA_lt_polyB hs).trans hB).le
      · exact hB.le
    calc
      g s ≤ (C * s) * s := mul_le_mul (hC s hs) hpoly
        (densityPolynomial_pos kind hs).le ((imageDensity_pos hp hL hs).le.trans (hC s hs))
      _ = _ := by ring
  simpa only [hK, g] using density_sampling_formula g C hg hpos hbound hC₀ hb

private theorem mixedSampling {p L b : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hb : 0 < b) (kind other : CircleKernelKind) :
    let f := fun s : ℝ => imageDensity p L s *
      (densityPolynomial kind s - densityPolynomial other s / 4) * scaledExpTail s b
    IntegrableOn f (Ioi 0) ∧
      samplingTail (fun t => imageMoment p L kind 0 t - imageMoment p L other 0 t / 4) 0 b =
        ∫ s : ℝ in Ioi 0, f s := by
  dsimp only
  obtain ⟨hI₁, hS₁⟩ := imageMoment_density_sampling hp hp₂ hL hb kind
  obtain ⟨hI₂, hS₂⟩ := imageMoment_density_sampling hp hp₂ hL hb other
  have hE (s : ℝ) :
      imageDensity p L s * densityPolynomial kind s * scaledExpTail s b -
          imageDensity p L s * densityPolynomial other s * scaledExpTail s b / 4 =
        imageDensity p L s * (densityPolynomial kind s - densityPolynomial other s / 4) *
          scaledExpTail s b := by ring
  refine ⟨(hI₁.sub (hI₂.div_const 4)).congr (Eventually.of_forall hE), ?_⟩
  rw [samplingTail_sub_div _ _ _ _
    (imageMoment_samples_summable hp hp₂ hL hb hb kind)
    (imageMoment_samples_summable hp hp₂ hL hb hb other), hS₁, hS₂, ← integral_div]
  calc
    _ = ∫ s : ℝ in Ioi 0, imageDensity p L s * densityPolynomial kind s * scaledExpTail s b -
        imageDensity p L s * densityPolynomial other s * scaledExpTail s b / 4 :=
      (integral_sub hI₁ (hI₂.div_const 4)).symm
    _ = _ := integral_congr_ae (Eventually.of_forall hE)

theorem circleDefect_eq_integral {p L b : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2) (hL : 0 < L)
    (hb : 0 < b) :
    IntegrableOn (fun s => imageDensity p L s * defectCore b s) (Ioi 0) ∧
      circleDefect p L b = (∫ s : ℝ in Ioi 0, imageDensity p L s * defectCore b s) -
        defectConstant b * imageSelf p L := by
  let f (s : ℝ) := imageDensity p L s * leftMixPolynomial s * scaledExpTail s 1
  let g (s : ℝ) := imageDensity p L s * rightMixPolynomial s * scaledExpTail s b
  let u (s : ℝ) := (1 - b / 4) * (imageDensity p L s * s * Real.exp (-s))
  let k (s : ℝ) := defectConstant b * (imageDensity p L s * Real.exp (-s))
  obtain ⟨hf, hfS⟩ : IntegrableOn f (Ioi 0) ∧ samplingTail (imageLeftMoment p L 0) 0 1 =
      ∫ s : ℝ in Ioi 0, f s :=
    by simpa only [f, imageLeftMoment, leftMixPolynomial, densityPolynomial] using
      mixedSampling hp hp₂ hL zero_lt_one .a .b
  obtain ⟨hg, hgS⟩ : IntegrableOn g (Ioi 0) ∧ samplingTail (imageRightMoment p L 0) 0 b =
      ∫ s : ℝ in Ioi 0, g s :=
    by simpa only [g, imageRightMoment, rightMixPolynomial, densityPolynomial] using
      mixedSampling hp hp₂ hL hb .b .a
  have hu : IntegrableOn u (Ioi 0) := by
    simpa only [u, mul_one] using (imageSlope_integrable hp hL zero_lt_one).const_mul (1 - b / 4)
  have hk : IntegrableOn k (Ioi 0) := by
    simpa only [k, mul_one] using (imagePotential_integrable hp hL zero_lt_one).const_mul (defectConstant b)
  have he (s : ℝ) (hs : 0 < s) : f s + g s - u s - k s = imageDensity p L s * defectCore b s := by
    dsimp only [f, g, u, k, defectCore, defectConstant, tailDifference]
    have h := congrArg (imageDensity p L s * ·) (polynomial_total_sample hs)
    dsimp only at h
    linear_combination h
  have heAE : (fun s : ℝ => f s + g s - u s - k s) =ᵐ[volume.restrict (Ioi 0)]
      (fun s => imageDensity p L s * defectCore b s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact he s hs
  refine ⟨(((hf.add hg).sub hu).sub hk).congr heAE, ?_⟩
  have huI : (∫ s : ℝ in Ioi 0, u s) = (1 - b / 4) * imageSlope p L 1 := by
    simp only [u, imageSlope, mul_one, integral_const_mul]
  have hkI : (∫ s : ℝ in Ioi 0, k s) = defectConstant b * imagePotential p L 1 := by
    simp only [k, imagePotential, mul_one, integral_const_mul]
  have hi : (∫ s : ℝ in Ioi 0, f s + g s - u s - k s) =
      (∫ s : ℝ in Ioi 0, f s) + (∫ s : ℝ in Ioi 0, g s) -
        (∫ s : ℝ in Ioi 0, u s) - ∫ s : ℝ in Ioi 0, k s := by
    have hfg : (∫ s : ℝ in Ioi 0, (f + g) s) =
        (∫ s : ℝ in Ioi 0, f s) + ∫ s : ℝ in Ioi 0, g s := integral_add hf hg
    exact (integral_sub ((hf.add hg).sub hu) hk).trans
      (congrArg (fun x : ℝ => x - ∫ s : ℝ in Ioi 0, k s)
        ((integral_sub (hf.add hg) hu).trans
          (congrArg (fun x : ℝ => x - ∫ s : ℝ in Ioi 0, u s) hfg)))
  rw [circleDefect, hfS, hgS, ← integral_congr_ae heAE, hi, huI, hkI, defectConstant]
  ring

end ACS12.GammaDeficit

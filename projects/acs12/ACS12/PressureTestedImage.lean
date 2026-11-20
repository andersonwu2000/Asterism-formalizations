import ACS12.PressureMinimumTransfer
import ACS12.PressureMinimumGeometry

/-! Whole-image sums after testing an occupied ray. -/
namespace ACS12.Pressure

open Set Filter MeasureTheory CenteredCircle.AllN
open GammaMeasure (imageDensity_pos continuous_imageDensity imageTailIntegrand imageTailIntegrand_integrable
  imageSlopeTail_integrable imagePotential imageSlope hasSum_laplace_samples imagePotential_samples_summable)

noncomputable def testedImage (p L : ℝ) (T : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s : ℝ in Ioi 0, GammaMeasure.imageDensity p L s * T s * Real.exp (-s * t)

theorem testedImage_samples {p L a t : ℝ} (hp : 0 < p) (hL : 0 < L) (ha : 0 ≤ a) (ht : 0 < t)
    {T : ℝ → ℝ} (hM : Measurable T) (hT : ∀ s > 0, 0 ≤ T s ∧ T s ≤ a * s + 1) :
    let f (s : ℝ) := GammaMeasure.imageDensity p L s * T s * (Real.exp (-s * t) / periodicDen L s)
    IntegrableOn f (Ioi 0) ∧ HasSum (fun j : ℕ => testedImage p L T (t + (j : ℝ) * L))
      (∫ s : ℝ in Ioi 0, f s) := by
  let w := GammaMeasure.imageDensity p L
  let f (s : ℝ) := w s * T s * (Real.exp (-s * t) / periodicDen L s)
  have hg : Measurable (fun s => w s * T s) := (continuous_imageDensity hp hL).measurable.mul hM
  have hI : IntegrableOn f (Ioi 0) := by
    have hDom := ((imageSlopeTail_integrable hp hL ht).const_mul a).add (imageTailIntegrand_integrable hp hL ht)
    have hMf : Measurable f := by
      unfold f periodicDen
      exact hg.mul (by fun_prop)
    apply hDom.mono' hMf.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    obtain ⟨hP,hB⟩ := hT s hs
    have hw := (imageDensity_pos hp hL hs).le
    have hD := (div_pos (Real.exp_pos (-s * t)) (periodicDen_pos hL hs)).le
    have hF : 0 ≤ f s := mul_nonneg (mul_nonneg hw hP) hD
    rw [Real.norm_of_nonneg hF]
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB hw) hD
    dsimp only [f,w,periodicDen,imageTailIntegrand] at h ⊢
    simp only [Pi.add_apply,imageTailIntegrand]
    linarith only [h]
  exact ⟨hI,hasSum_laplace_samples _ hg (fun s hs => mul_nonneg (imageDensity_pos hp hL hs).le (hT s hs).1) hL hI⟩

private theorem testedImage_le_affine {p L a t : ℝ} (hp : 0 < p) (hL : 0 < L) (ht : 0 < t)
    {T : ℝ → ℝ} (hM : Measurable T) (hT : ∀ s > 0, 0 ≤ T s ∧ T s ≤ a * s + 1) :
    testedImage p L T t ≤ a * imageSlope p L t + imagePotential p L t := by
  let w := GammaMeasure.imageDensity p L
  let k (s : ℝ) := w s * Real.exp (-s * t)
  let U (s : ℝ) := w s * s * Real.exp (-s * t)
  let G (s : ℝ) := w s * T s * Real.exp (-s * t)
  have hk : IntegrableOn k (Ioi 0) := GammaMeasure.imagePotential_integrable hp hL ht
  have hU : IntegrableOn U (Ioi 0) := GammaMeasure.imageSlope_integrable hp hL ht
  have hM' : Measurable G := ((continuous_imageDensity hp hL).measurable.mul hM).mul (by fun_prop)
  have hPoint (s : ℝ) (hs : 0 < s) : 0 ≤ G s ∧ G s ≤ a * U s + k s := by
    obtain ⟨hP,hB⟩ := hT s hs
    have hw := (imageDensity_pos hp hL hs).le
    have hE := (Real.exp_pos (-s * t)).le
    refine ⟨mul_nonneg (mul_nonneg hw hP) hE,?_⟩
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB hw) hE
    dsimp only [G,U,k,w]
    linarith only [h]
  have hF : IntegrableOn (fun s => a * U s + k s) (Ioi 0) := (hU.const_mul a).add hk
  have hI : IntegrableOn G (Ioi 0) := by
    apply hF.mono' hM'.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_of_nonneg (hPoint s hs).1]
    exact (hPoint s hs).2
  have h := setIntegral_mono_on hI hF measurableSet_Ioi (fun s hs => (hPoint s hs).2)
  rw [integral_add (hU.const_mul a) hk,integral_const_mul] at h
  exact h

theorem testedImage_self_le {p L a t : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2) (hL : 0 < L)
    (ha : 0 < a) (ht : 0 < t) (haT : 2 * a ≤ t) :
    testedImage p L (minimumAtomTest a a a) t ≤ 2 * imagePotential p L t := by
  have hM : Measurable (minimumAtomTest a a a) := by unfold minimumAtomTest oppositeRayBose pressureBose periodicDen; fun_prop
  have hI := testedImage_le_affine hp hL ht hM (fun s hs => minimumAtomTest_bounds ha.le ha le_rfl hs)
  have hU := imageSlope_pos hp hL ht
  have h := (mul_le_mul_of_nonneg_right haT hU.le).trans (imageSlope_mul_le_double hp hp₂ hL ht)
  linarith only [h,hI]

theorem testedRay_integral {n : ℕ} {p L a : ℝ} (hp : 0 < p) (hL : 0 < L) (ha : 0 ≤ a)
    (m d : Fin n → ℝ) (hd : ∀ j, 0 < d j) (I : Finset (Fin n))
    {T : ℝ → ℝ} (hM : Measurable T) (hT : ∀ s > 0, 0 ≤ T s ∧ T s ≤ a * s + 1) :
    let f (s : ℝ) := GammaMeasure.imageDensity p L s * T s *
      (∑ j ∈ I, m j * (Real.exp (-s * d j) / periodicDen L s))
    IntegrableOn f (Ioi 0) ∧ (∫ s : ℝ in Ioi 0, f s) =
      ∑ j ∈ I, m j * imageTail (testedImage p L T) L (d j) := by
  let v (j : Fin n) (s : ℝ) := GammaMeasure.imageDensity p L s * T s * (Real.exp (-s * d j) / periodicDen L s)
  have hV (j : Fin n) := testedImage_samples hp hL ha (hd j) hM hT
  have hE (s : ℝ) : GammaMeasure.imageDensity p L s * T s *
      (∑ j ∈ I, m j * (Real.exp (-s * d j) / periodicDen L s)) = ∑ j ∈ I, m j * v j s := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by dsimp only [v]; ring)
  have hVI (j : Fin n) : IntegrableOn (fun s => m j * v j s) (Ioi 0) := (hV j).1.const_mul _
  refine ⟨(integrable_finsetSum I (fun j _ => hVI j)).congr (Eventually.of_forall fun s => (hE s).symm),?_⟩
  dsimp only
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => hE s),integral_finsetSum _ (fun j _ => hVI j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul]
  exact congrArg (m j * ·) (hV j).2.tsum_eq.symm

end ACS12.Pressure

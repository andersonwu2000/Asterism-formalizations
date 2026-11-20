import ACS12.HighPotentialScaling
import ACS12.PressureMaximumRadial

/-! The actual high maximum row has the complete quadratic zeta bound. -/
namespace ACS12.Pressure

open Set Filter MeasureTheory CenteredCircle.AllN
open GammaMeasure

private theorem high_boseRadial_integral {p L Q : ℝ} (hp : 0 < p)
    (hL : 0 < L) (hQ : 0 < Q) :
    let f (s : ℝ) := GammaMeasure.imageDensity p L s * pressureBose Q s
    IntegrableOn f (Ioi 0) ∧ (∫ s : ℝ in Ioi 0, f s) = Q * imageTail (imagePotential p L) Q Q := by
  let w := GammaMeasure.imageDensity p L
  let f (s : ℝ) := w s * pressureBose Q s
  have hM : Measurable f := (continuous_imageDensity hp hL).measurable.mul
    (by unfold pressureBose periodicDen; fun_prop)
  have hI : IntegrableOn f (Ioi 0) := by
    apply ((stressKernel_integrable_all hp hL hQ hQ).const_mul (Q ^ 2)).mono' hM.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0 < s := hs
    have hw := imageDensity_pos hp hL hs₀
    have hD := periodicDen_pos hQ hs₀
    have hDen : periodicDen Q s ≤ s * Q := by
      unfold periodicDen
      linarith only [Real.add_one_le_exp (-s * Q)]
    rw [Real.norm_of_nonneg (show 0 ≤ f s from mul_nonneg hw.le (pressureBose_pos hQ hs₀).le)]
    have h := mul_le_mul_of_nonneg_left hDen (show 0 ≤ Q * w s * Real.exp (-s * Q) by positivity)
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (sq_pos_of_pos hD)).mpr
    convert h using 1 <;> dsimp only [f,pressureBose,w] <;> field_simp [hD.ne'] <;> ring
  let g (s : ℝ) := w s * (Real.exp (-s * Q) / periodicDen Q s)
  have hF (s : ℝ) : f s = Q * g s := by dsimp only [f,g,pressureBose]; ring
  have hg : IntegrableOn g (Ioi 0) := (hI.const_mul Q⁻¹).congr
    (Eventually.of_forall fun s => by
      change Q⁻¹ * f s = g s
      rw [hF,← mul_assoc,inv_mul_cancel₀ hQ.ne',one_mul])
  have hSum := hasSum_laplace_samples w (continuous_imageDensity hp hL).measurable
    (fun s hs => (imageDensity_pos hp hL hs).le) hQ hg
  have hG : imageTail (imagePotential p L) Q Q = ∫ s : ℝ in Ioi 0, g s := hSum.tsum_eq
  exact ⟨hI,by
    change (∫ s : ℝ in Ioi 0, f s) = _
    rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => hF s),integral_const_mul,hG]⟩

theorem high_original_maximum_radial_bound {n : ℕ} {p : ℝ} (hn : 2 ≤ n) (hp : 2 ≤ p)
    (F : Configuration n p) (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi))
    (i : Fin n) (hMax : ∀ j, C.source.mass j ≤ C.source.mass i) :
    let S := C.source
    let Q := S.mass i
    let L := S.period
    F.chartRadialScale C * (2 * F.coefficient * F.radius ^ 2) + Q * imageSelf p L ≤
      2 * (Q * imagePotential p L Q) * powerTail 2 1 := by
  let S := C.source
  let Q := S.mass i
  let L := S.period
  let k := imagePotential p L
  let A := leftRay S i
  let B := rightRay S i
  let w := GammaMeasure.imageDensity p L
  let h (s : ℝ) := w s * pressureBose Q s
  have hp₀ := (by linarith only [hp] : 0 < p)
  have hL : 0 < L := S.period_pos
  have hQ : 0 < Q := S.mass_pos i
  obtain ⟨hAi,hA⟩ := ray_radial_integral hp₀ hL S.mass _ (fun j => S.forwardDistance_pos j i)
  obtain ⟨hBi,hB⟩ := ray_radial_integral hp₀ hL S.mass _ (S.forwardDistance_pos i)
  obtain ⟨hI,hE⟩ := high_boseRadial_integral hp₀ hL hQ
  change IntegrableOn h (Ioi 0) at hI
  change (∫ s : ℝ in Ioi 0, h s) = _ at hE
  have hXA : (∫ s : ℝ in Ioi 0, w s * A s) ≤ ∫ s : ℝ in Ioi 0, h s := by
    apply setIntegral_mono_on hAi hI measurableSet_Ioi
    intro s hs
    exact mul_le_mul_of_nonneg_left (maximum_rays_le hn S C.circular_caps i hMax hs).1
      (imageDensity_pos hp₀ hL hs).le
  have hXB : (∫ s : ℝ in Ioi 0, w s * B s) ≤ ∫ s : ℝ in Ioi 0, h s := by
    apply setIntegral_mono_on hBi hI measurableSet_Ioi
    intro s hs
    exact mul_le_mul_of_nonneg_left (maximum_rays_le hn S C.circular_caps i hMax hs).2
      (imageDensity_pos hp₀ hL hs).le
  have hRad := F.chart_radial_images C hp₀ i
  change S.forwardExterior k i + S.backwardExterior k i = _ at hRad
  change (∫ s : ℝ in Ioi 0, w s * A s) = S.backwardExterior k i at hA
  change (∫ s : ℝ in Ioi 0, w s * B s) = S.forwardExterior k i at hB
  have hBound : imageTail k Q Q ≤ k Q * powerTail 2 1 := by
    unfold imageTail powerTail
    rw [← tsum_mul_left]
    have hK : Summable (fun j : ℕ => k (Q + (j : ℝ) * Q)) := by
      have hS := hasSum_laplace_samples (t := Q) w (continuous_imageDensity hp₀ hL).measurable
        (fun s hs => (imageDensity_pos hp₀ hL hs).le) hQ
      have hI' : IntegrableOn (fun s => w s * (Real.exp (-s * Q) / (1 - Real.exp (-s * Q)))) (Ioi 0) :=
        (hI.const_mul Q⁻¹).congr (Eventually.of_forall fun s => by
          dsimp only [h,pressureBose,periodicDen]
          field_simp [hQ.ne'])
      exact (hS hI').summable
    apply hK.tsum_le_tsum _ ((powerTail_summable (by norm_num : (1 : ℝ) < 2) 1).mul_left (k Q))
    intro j
    have hT : Q ≤ Q + (j : ℝ) * Q := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg j) hQ.le)
    have h := high_imagePotential_scaled_upper hp hL hQ hT
    have hDiv : Q / (Q + (j : ℝ) * Q) = ((1 : ℝ) + j)⁻¹ := by
      have hE : Q + (j : ℝ) * Q = Q * (1 + j) := by ring
      rw [hE,div_mul_eq_div_div,div_self hQ.ne',one_div]
    rw [hDiv,inv_pow] at h
    rw [← Real.rpow_natCast,← Real.rpow_neg (by positivity)] at h
    simpa only [k,Nat.cast_one,mul_comm] using h
  rw [hA,hE] at hXA
  rw [hB,hE] at hXB
  change _ ≤ 2 * (Q * k Q) * powerTail 2 1
  nlinarith only [hXA,hXB,hRad,mul_le_mul_of_nonneg_left hBound hQ.le]

end ACS12.Pressure

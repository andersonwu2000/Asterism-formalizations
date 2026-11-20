import ACS12.PressureMinimumGeometry
import ACS12.PressureFloorGuards

/-! Full normalized original maximum row bounds. -/
namespace ACS12.Pressure

open Set Filter MeasureTheory CenteredCircle.AllN
open GammaMeasure (imageDensity_pos continuous_imageDensity imageDensity_linear_bound
  imagePotential imagePotential_pos imagePotential_samples_summable imageSelf imageSelf_pos
  hasSum_laplace_samples powerTail powerTail_summable)

private theorem boseRadial_integral {p L Q : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hQ : 0 < Q) :
    let f (s : ℝ) := GammaMeasure.imageDensity p L s * pressureBose Q s
    IntegrableOn f (Ioi 0) ∧ (∫ s : ℝ in Ioi 0, f s) = Q * imageTail (imagePotential p L) Q Q := by
  let w := GammaMeasure.imageDensity p L
  let f (s : ℝ) := w s * pressureBose Q s
  obtain ⟨C,hC,hD⟩ := imageDensity_linear_bound hp hp₂ hL
  have hM : Measurable f := (continuous_imageDensity hp hL).measurable.mul
    (by unfold pressureBose periodicDen; fun_prop)
  have hI : IntegrableOn f (Ioi 0) := by
    have h₀ : IntegrableOn (fun s : ℝ => Real.exp (-s * Q)) (Ioi 0) := by
      simpa only [pow_zero,one_mul] using integrable_power_exponential 0 Q hQ
    have h₁ : IntegrableOn (fun s : ℝ => s * Real.exp (-s * Q)) (Ioi 0) := by
      simpa only [pow_one] using integrable_power_exponential 1 Q hQ
    apply (h₀.add (h₁.const_mul Q) |>.const_mul C).mono' hM.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0 < s := hs
    have hB := pressureBose_pos hQ hs₀
    have hF : 0 ≤ f s := mul_nonneg (imageDensity_pos hp hL hs₀).le hB.le
    rw [Real.norm_of_nonneg hF]
    have h := mul_le_mul_of_nonneg_right (hD s hs₀) hB.le
    have hE : s * pressureBose Q s = Real.exp (-s * Q) * expHeadFactor (s * Q) := by
      unfold pressureBose periodicDen expHeadFactor
      rw [neg_mul]
      ring
    have hHead : expHeadFactor (s * Q) ≤ 1 + s * Q := by
      rw [GammaMeasure.expHeadFactor_eq_add_expTail (mul_pos hs₀ hQ)]
      linarith only [(BoseShape.expTail_bounds (mul_pos hs₀ hQ)).2]
    have hU := mul_le_mul_of_nonneg_left hHead (show 0 ≤ C * Real.exp (-s * Q) by positivity)
    simp only [Pi.add_apply]
    change w s * pressureBose Q s ≤ _
    dsimp only [w] at h ⊢
    nlinarith only [h,hU,congrArg (C * ·) hE]
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

theorem original_maximum_radial_bound {n : ℕ} {p : ℝ} (hn : 2 ≤ n) (hp : 1 < p) (hp₂ : p ≤ 2)
    (F : Configuration n p) (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi))
    (i : Fin n) (hMax : ∀ j, C.source.mass j ≤ C.source.mass i) :
    let S := C.source
    let Q := S.mass i
    let L := S.period
    F.chartRadialScale C * (2 * F.coefficient * F.radius ^ 2) + Q * imageSelf p L ≤
      2 * (Q * imagePotential p L Q) * powerTail p 1 := by
  let S := C.source
  let Q := S.mass i
  let L := S.period
  let k := imagePotential p L
  let A := leftRay S i
  let B := rightRay S i
  let w := GammaMeasure.imageDensity p L
  let h (s : ℝ) := w s * pressureBose Q s
  have hp₀ := zero_lt_one.trans hp
  have hL : 0 < L := S.period_pos
  have hQ : 0 < Q := S.mass_pos i
  obtain ⟨hAi,hA⟩ := ray_radial_integral hp₀ hL S.mass _ (fun j => S.forwardDistance_pos j i)
  obtain ⟨hBi,hB⟩ := ray_radial_integral hp₀ hL S.mass _ (S.forwardDistance_pos i)
  obtain ⟨hI,hE⟩ := boseRadial_integral hp₀ hp₂ hL hQ
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
  have hBound : imageTail k Q Q ≤ k Q * powerTail p 1 := by
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
    apply hK.tsum_le_tsum _ ((powerTail_summable hp 1).mul_left (k Q))
    intro j
    have hT : Q ≤ Q + (j : ℝ) * Q := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg j) hQ.le)
    have h := imagePotential_scaled_upper hp.le hp₂ hL hQ hT
    have hDiv : Q / (Q + (j : ℝ) * Q) = ((1 : ℝ) + j)⁻¹ := by
      have hE : Q + (j : ℝ) * Q = Q * (1 + j) := by ring
      rw [hE,div_mul_eq_div_div,div_self hQ.ne',one_div]
    rw [hDiv,Real.inv_rpow (by positivity),← Real.rpow_neg (by positivity)] at h
    simpa only [k,Nat.cast_one,mul_comm] using h
  rw [hA,hE] at hXA
  rw [hB,hE] at hXB
  change _ ≤ 2 * (Q * k Q) * powerTail p 1
  nlinarith only [hXA,hXB,hRad,mul_le_mul_of_nonneg_left hBound hQ.le]

theorem chartLevel_gt_potential_one {n : ℕ} {p : ℝ} (hp : 0 < p) (F : Configuration n p)
    (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi)) :
    imagePotential p C.source.period 1 < F.chartRadialScale C * (2 * F.coefficient * F.radius ^ 2) := by
  let S := C.source
  let L := S.period
  let k := imagePotential p L
  have hL : 0 < L := S.period_pos
  have hNe : S.root ≠ S.neighbor := fun h => S.root_neighbor_next.1.ne (congrArg S.coordinate h)
  have hD : S.forwardDistance S.root S.neighbor = 1 := by
    rw [S.forwardDistance_eq_sub S.root_neighbor_next.1,S.coordinate_root,S.coordinate_neighbor,sub_zero]
  have hFor := nonselfRayRow_point_le hL S.mass (S.forwardDistance S.neighbor) (fun j => (S.mass_pos j).le)
    (S.forwardDistance_pos S.neighbor) hNe (fun _ ht => (imagePotential_pos hp hL ht).le)
    (imagePotential_samples_summable hp hL (S.forwardDistance_pos S.neighbor S.root))
  have hBack := nonselfRayRow_point_le hL S.mass (fun j => S.forwardDistance j S.neighbor)
    (fun j => (S.mass_pos j).le) (fun j => S.forwardDistance_pos j S.neighbor) hNe
    (fun _ ht => (imagePotential_pos hp hL ht).le)
    (imagePotential_samples_summable hp hL (S.forwardDistance_pos S.root S.neighbor))
  have hRad := (original_nonself_rows hp F C S.neighbor).1
  have hK := imagePotential_pos hp hL (S.forwardDistance_pos S.neighbor S.root)
  change S.mass S.root * k (S.forwardDistance S.root S.neighbor) ≤ _ at hBack
  rw [hD,S.mass_root,one_mul] at hBack
  change S.mass S.root * k (S.forwardDistance S.neighbor S.root) ≤ _ at hFor
  rw [S.mass_root,one_mul] at hFor
  change k 1 < _
  linarith only [hRad,hBack,hFor,hK]

end ACS12.Pressure

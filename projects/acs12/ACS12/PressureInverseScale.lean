import ACS12.PressureScaling
import ACS12.GammaSourceElasticity

/-! The actual inverse radius for the radial mass and its force comparison. -/
namespace ACS12.Pressure

open Set MeasureTheory Filter CenteredCircle.AllN
open GammaMeasure (imageDensity_pos continuous_imageDensity imageDensity_linear_bound
  imagePotential imagePotential_pos imagePotential_integrable imageSlope imageSlope_integrable)

theorem imagePotential_deriv {p L t : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2) (hL : 0 < L) (ht : 0 < t) :
    HasDerivAt (imagePotential p L) (-imageSlope p L t) t := by
  obtain ⟨C,hC,hB⟩ := imageDensity_linear_bound hp hp₂ hL
  have h := hasDerivAt_weighted_laplace (GammaMeasure.imageDensity p L) C 1
    (continuous_imageDensity hp hL).measurable hC
    (fun s hs => by rw [abs_of_pos (imageDensity_pos hp hL hs),pow_one]; exact hB s hs) ht
  simpa only [imagePotential,imageSlope,mul_comm _ (GammaMeasure.imageDensity p L _)] using h

theorem imagePotential_strictAnti {p L : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hL : 0 < L) :
    StrictAntiOn (imagePotential p L) (Ioi 0) := by
  intro x hx y hy h
  have hx₀ : 0 < x := hx
  have hy₀ : 0 < y := hy
  have hp₀ := zero_lt_one.trans_le hp
  have hK := imagePotential_pos hp₀ hL hx₀
  have hR : (x / y) ^ p < 1 := by
    have hxy := div_lt_one hy₀ |>.mpr h
    simpa only [Real.one_rpow] using Real.rpow_lt_rpow (div_nonneg hx₀.le hy₀.le) hxy hp₀
  exact (imagePotential_scaled_upper hp hp₂ hL hx₀ h.le).trans_lt (mul_lt_of_lt_one_left hK hR)

theorem exists_imagePotential_eq {p L c : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hL : 0 < L) (hc : 0 < c) :
    ∃ t > 0, imagePotential p L t = c := by
  let k := imagePotential p L
  let r := (k 1 / c) ^ (1 / p)
  let x := min 1 r
  let y := max 1 r
  have hp₀ := zero_lt_one.trans_le hp
  have hK := imagePotential_pos hp₀ hL zero_lt_one
  have hD : 0 < k 1 / c := div_pos hK hc
  have hr : 0 < r := Real.rpow_pos_of_pos hD _
  have hx : 0 < x := lt_min zero_lt_one hr
  have hy : 0 < y := zero_lt_one.trans_le (le_max_left _ _)
  have hPow : r ^ (-p) * k 1 = c := by
    unfold r
    rw [← Real.rpow_mul hD.le,show (1 / p) * (-p) = -1 by field_simp [hp₀.ne'],Real.rpow_neg_one,inv_div]
    exact div_mul_cancel₀ _ hK.ne'
  have hL₁ : r ^ (-p) * k 1 ≤ k x := by
    have hS := imagePotential_scaled_upper hp hp₂ hL hx (min_le_left 1 r)
    change k 1 ≤ (x / 1) ^ p * k x at hS
    rw [div_one] at hS
    have hX : x ^ (-p) * k 1 ≤ k x := by
      rw [Real.rpow_neg hx.le,← div_eq_inv_mul]
      exact (div_le_iff₀ (Real.rpow_pos_of_pos hx p)).mpr (by simpa only [mul_comm] using hS)
    exact (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hx (min_le_right 1 r) (neg_nonpos.mpr hp₀.le)) hK.le).trans hX
  have hL₂ : k y ≤ r ^ (-p) * k 1 := by
    have hS := imagePotential_scaled_upper hp hp₂ hL zero_lt_one (le_max_left 1 r)
    change k y ≤ (1 / y) ^ p * k 1 at hS
    rw [one_div,Real.inv_rpow hy.le,← Real.rpow_neg hy.le] at hS
    exact hS.trans (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hr (le_max_right 1 r) (neg_nonpos.mpr hp₀.le)) hK.le)
  rw [hPow] at hL₁ hL₂
  have hxy : x ≤ y := (min_le_left 1 r).trans (le_max_left _ _)
  have hCont : ContinuousOn k (Icc x y) := by
    intro t ht
    exact (imagePotential_deriv hp₀ hp₂ hL (hx.trans_le ht.1)).continuousAt.continuousWithinAt
  obtain ⟨t,ht,hEq⟩ := intermediate_value_Icc' hxy hCont ⟨hL₂,hL₁⟩
  exact ⟨t,hx.trans_le ht.1,hEq⟩

theorem imageSlope_mul_potential_le {p L t u : ℝ} (hp : 0 < p) (hL : 0 < L)
    (ht : 0 < t) (htu : t ≤ u) :
    imageSlope p L u * imagePotential p L t ≤ imageSlope p L t * imagePotential p L u := by
  let A (x s : ℝ) := GammaMeasure.imageDensity p L s * Real.exp (-s * x)
  have hu := ht.trans_le htu
  have hI (x : ℝ) (hx : 0 < x) : IntegrableOn (A x) (Ioi 0) :=
    imagePotential_integrable hp hL hx
  have hS (x : ℝ) (hx : 0 < x) : IntegrableOn (fun s => A x s * s) (Ioi 0) := by
    simpa only [A,mul_right_comm] using imageSlope_integrable hp hL hx
  have hE (x : ℝ) : (∫ s : ℝ in Ioi 0, A x s * s) = imageSlope p L x := by
    simp only [A,imageSlope,mul_right_comm]
  have hRat : MonotoneOn (fun s => A t s / A u s) (Ioi 0) := by
    have hR (s : ℝ) (hs : 0 < s) : A t s / A u s = Real.exp ((u - t) * s) := by
      dsimp only [A]
      rw [mul_div_mul_left _ _ (imageDensity_pos hp hL hs).ne',← Real.exp_sub]
      congr 1
      ring
    intro s hs v hv h
    dsimp only
    rw [hR s hs,hR v hv]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h (sub_nonneg.mpr htu))
  have h := likelihood_test_mono (hI u hu) (hI t ht) (hS u hu) (hS t ht)
    (fun s hs => mul_pos (imageDensity_pos hp hL hs) (Real.exp_pos _)) hRat
    (show MonotoneOn (fun s : ℝ => s) (Ioi 0) by intro s hs v hv h; exact h)
  rw [hE,hE] at h
  exact h


theorem imageSlope_mul_le_double {p L t : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2) (hL : 0 < L) (ht : 0 < t) :
    t * imageSlope p L t ≤ 2 * imagePotential p L t := by
  let A (s : ℝ) := GammaMeasure.imageDensity p L s * Real.exp (-s * t)
  let B (s : ℝ) := s * Real.exp (-s * t)
  have hA : IntegrableOn A (Ioi 0) := imagePotential_integrable hp hL ht
  have hA' : IntegrableOn (fun s => A s * s) (Ioi 0) := by
    simpa only [A,mul_right_comm] using imageSlope_integrable hp hL ht
  have hB : IntegrableOn B (Ioi 0) := by simpa only [B,pow_one] using integrable_power_exponential 1 t ht
  have hE (s : ℝ) : B s * s = s ^ 2 * Real.exp (-s * t) := by dsimp only [B]; ring
  have hB' : IntegrableOn (fun s => B s * s) (Ioi 0) := (integrable_power_exponential 2 t ht).congr
    (Eventually.of_forall fun s => (hE s).symm)
  have hRat : MonotoneOn (fun s => B s / A s) (Ioi 0) := by
    have hR (s : ℝ) : B s / A s = (GammaMeasure.imageDensity p L s / s)⁻¹ := by
      rw [inv_div]
      exact mul_div_mul_right _ _ (Real.exp_pos (-s * t)).ne'
    intro s hs u hu h
    dsimp only
    rw [hR,hR]
    exact (inv_le_inv₀ (div_pos (imageDensity_pos hp hL hs) hs)
      (div_pos (imageDensity_pos hp hL hu) hu)).mpr
        (GammaMeasure.imageDensity_div_antitone hp hp₂ hL hs hu h)
  have h := likelihood_test_mono hA hB hA' hB' (fun s hs => mul_pos (imageDensity_pos hp hL hs) (Real.exp_pos _)) hRat
    (show MonotoneOn (fun s : ℝ => s) (Ioi 0) by intro s hs v hv h; exact h)
  have hR : (∫ s : ℝ in Ioi 0, B s) = 1 / t ^ 2 := by
    simpa [B] using integral_power_exponential 1 t ht
  have hR' : (∫ s : ℝ in Ioi 0, B s * s) = 2 / t ^ 3 := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => hE s),integral_power_exponential 2 t ht]
    norm_num
  have hA'E : (∫ s : ℝ in Ioi 0, A s * s) = imageSlope p L t := by
    simp only [A,imageSlope,mul_right_comm]
  rw [hR,hR',hA'E] at h
  change imageSlope p L t * (1 / t ^ 2) ≤ (2 / t ^ 3) * imagePotential p L t at h
  have h' := mul_le_mul_of_nonneg_right h (pow_nonneg ht.le 3)
  have h₁ : imageSlope p L t * (1 / t ^ 2) * t ^ 3 = t * imageSlope p L t := by field_simp [ht.ne']
  have h₂ : 2 / t ^ 3 * imagePotential p L t * t ^ 3 = 2 * imagePotential p L t := by field_simp [ht.ne']
  rwa [h₁,h₂] at h'

theorem imageSlope_pos {p L t : ℝ} (hp : 0 < p) (hL : 0 < L) (ht : 0 < t) :
    0 < imageSlope p L t := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  letI : NeZero μ := ⟨positiveHalfLine_ne_zero⟩
  have h := integral_strict_of_ae_lt μ (integrable_zero _ _ μ) (imageSlope_integrable hp hL ht) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_pos (mul_pos (imageDensity_pos hp hL hs) hs) (Real.exp_pos _))
  simpa only [imageSlope,integral_zero] using h

theorem pressureLaplaceMoment_upper {p L t : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (ht : 0 < t) (j : ℕ) :
    t * GammaMeasure.sourceLaplaceMoment p L (j + 1) t ≤
      ((j : ℝ) + 2) * GammaMeasure.sourceLaplaceMoment p L j t := by
  let A (s : ℝ) := GammaMeasure.imageDensity p L s * s ^ j * Real.exp (-s * t)
  let B (s : ℝ) := s ^ (j + 1) * Real.exp (-s * t)
  have hA : IntegrableOn A (Ioi 0) := GammaMeasure.sourceLaplaceMoment_integrable hp hL ht j
  have hA' : IntegrableOn (fun s => A s * s) (Ioi 0) := by
    exact (GammaMeasure.sourceLaplaceMoment_integrable hp hL ht (j + 1)).congr
      (Eventually.of_forall fun s => by dsimp only [A]; rw [pow_succ]; ring)
  have hB : IntegrableOn B (Ioi 0) := integrable_power_exponential (j + 1) t ht
  have hB' : IntegrableOn (fun s => B s * s) (Ioi 0) := by
    exact (integrable_power_exponential (j + 2) t ht).congr
      (Eventually.of_forall fun s => by dsimp only [B]; rw [show j + 2 = j + 1 + 1 by omega,pow_succ]; ring)
  have hRat : MonotoneOn (fun s => B s / A s) (Ioi 0) := by
    have hE (s : ℝ) (hs : 0 < s) : B s / A s = s / GammaMeasure.imageDensity p L s := by
      unfold A B
      rw [mul_div_mul_right _ _ (Real.exp_ne_zero _),pow_succ]
      field_simp [pow_ne_zero j hs.ne',(imageDensity_pos hp hL hs).ne']
    intro s hs u hu h
    change B s / A s ≤ B u / A u
    rw [hE s hs,hE u hu]
    simpa only [inv_div] using (inv_le_inv₀
      (div_pos (imageDensity_pos hp hL hs) hs) (div_pos (imageDensity_pos hp hL hu) hu)).mpr
        (GammaMeasure.imageDensity_div_antitone hp hp₂ hL hs hu h)
  have hPos (s : ℝ) (hs : 0 < s) : 0 < A s :=
    mul_pos (mul_pos (imageDensity_pos hp hL hs) (pow_pos hs _)) (Real.exp_pos _)
  have h := likelihood_test_mono hA hB hA' hB' hPos hRat (fun _ _ _ _ h => h)
  have hAE : (∫ s : ℝ in Ioi 0, A s * s) = GammaMeasure.sourceLaplaceMoment p L (j + 1) t := by
    unfold A GammaMeasure.sourceLaplaceMoment
    apply integral_congr_ae
    exact Eventually.of_forall fun s => by dsimp only; rw [pow_succ]; ring
  have hBE : (∫ s : ℝ in Ioi 0, B s * s) =
      ((j + 2).factorial : ℝ) / t ^ (j + 3) := by
    have hB' (s : ℝ) : B s * s = s ^ (j + 2) * Real.exp (-s * t) := by
      unfold B
      rw [show j + 2 = j + 1 + 1 by omega,pow_succ]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => hB' s),integral_power_exponential (j + 2) t ht]
  have hB₀ : (∫ s : ℝ in Ioi 0, B s) = ((j + 1).factorial : ℝ) / t ^ (j + 2) :=
    integral_power_exponential (j + 1) t ht
  rw [hAE,hBE,hB₀] at h
  have hF : (0 : ℝ) < ((j + 1).factorial : ℝ) := by positivity
  let c := ((j + 1).factorial : ℝ) / t ^ (j + 2)
  have hc : 0 < c := div_pos hF (pow_pos ht _)
  have hB₁ : ((j + 2).factorial : ℝ) / t ^ (j + 3) = (((j : ℝ) + 2) / t) * c := by
    unfold c
    rw [show j + 3 = j + 2 + 1 by omega,pow_succ t (j + 2),
      show ((j + 2).factorial : ℝ) = ((j : ℝ) + 2) * ((j + 1).factorial : ℝ) by
        rw [show j + 2 = j + 1 + 1 by omega,Nat.factorial_succ,Nat.cast_mul]
        push_cast
        ring]
    field_simp [ht.ne']
  change GammaMeasure.sourceLaplaceMoment p L (j + 1) t * c ≤
    (((j + 2).factorial : ℝ) / t ^ (j + 3)) * GammaMeasure.sourceLaplaceMoment p L j t at h
  rw [hB₁, mul_right_comm] at h
  have h' := (mul_le_mul_iff_left₀ hc).mp h
  have h'' := mul_le_mul_of_nonneg_right h' ht.le
  convert h'' using 1 <;> field_simp [ht.ne'] <;> ring

end ACS12.Pressure

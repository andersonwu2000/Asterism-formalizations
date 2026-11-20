import ACS12.OuterPureDensity
import ACS12.PureOuterUnit
import ACS12.PureOuterGeometry

/-! Complete source-corrected moments along the finite outer scaling arc. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaDeficit (lineDensity)

noncomputable def outerJ (p t : ℝ) : ℝ :=
  ∫ s : ℝ in Ioi 0, lineDensity p s * outerR 1 s * BoseShape.C (s * t)

theorem outerJ_one_eq {p : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) :
    outerJ p 1 = 1 + (6 / 25) * p + outerUnitValue p := by
  obtain ⟨hS, hSE⟩ := pureC_slope hp hp₂
  obtain ⟨hD, hDE⟩ := pureC_difference hp
  obtain ⟨hQ, hQE⟩ := pureC_slope_difference hp
  let A (s : ℝ) := lineDensity p s * s * BoseShape.C s
  let B (s : ℝ) := lineDensity p s * (1 - Real.exp (-s)) * BoseShape.C s
  let D (s : ℝ) := lineDensity p s * s * (1 - Real.exp (-s)) * BoseShape.C s
  have hI : IntegrableOn (fun s => (81 / 100) * A s - (81 / 100) * B s) (Ioi 0) :=
    (hS.const_mul _).sub (hD.const_mul _)
  have hEq (s : ℝ) : lineDensity p s * outerR 1 s * BoseShape.C (s * 1) =
      (81 / 100) * A s - (81 / 100) * B s - (6 / 25) * D s := by
    rw [outerR_one_eq]
    simp only [A, B, D, polyB, mul_one]
    ring
  rw [outerJ, setIntegral_congr_fun measurableSet_Ioi (fun s _ => hEq s),
    integral_sub hI (hQ.const_mul (6 / 25)),
    integral_sub (hS.const_mul (81 / 100)) (hD.const_mul (81 / 100)),
    integral_const_mul, integral_const_mul, integral_const_mul]
  change (81 / 100) * (∫ s : ℝ in Ioi 0, A s) - (81 / 100) * (∫ s : ℝ in Ioi 0, B s) -
    (6 / 25) * (∫ s : ℝ in Ioi 0, D s) = _
  rw [show (∫ s : ℝ in Ioi 0, A s) = p * pureZ p from hSE,
    show (∫ s : ℝ in Ioi 0, B s) = pureZ p - 1 from hDE,
    show (∫ s : ℝ in Ioi 0, D s) = pureQ p - p from hQE]
  unfold outerUnitValue
  ring

theorem pureC_integrable_of_linear {p t B : ℝ} {f : ℝ → ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (ht : 0 < t) (hB : 0 ≤ B) (hf : Measurable f) (hF : ∀ s > 0, |f s| ≤ B * s) :
    IntegrableOn (fun s => lineDensity p s * f s * BoseShape.C (s * t)) (Ioi 0) := by
  obtain ⟨_, _, h⟩ := pureLinear_envelope hp hp₂ hB hF
  have hM : Measurable (lineDensity p) := by unfold lineDensity; fun_prop
  exact (boseStream_derivative (hM.mul hf) h ht).1

private theorem pureC_integrable_scaled {p t : ℝ} {f : ℝ → ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (ht : 0 < t) (hf : Measurable f) (hF : ∃ B ≥ 0, ∀ s > 0, |f s| ≤ B * s) :
    IntegrableOn (fun s => lineDensity p s * f (s / t) * BoseShape.C s) (Ioi 0) := by
  obtain ⟨B, hB, hB'⟩ := hF
  have h := pureC_integrable_of_linear (f := fun s => f (s / t)) hp hp₂ zero_lt_one
    (div_nonneg hB ht.le) (hf.comp (by fun_prop)) (fun s hs => (hB' (s / t) (div_pos hs ht)).trans_eq (by ring))
  simpa only [mul_one] using h

private theorem outerR_measurable (u : ℝ) : Measurable (outerR u) := by
  unfold outerR middleRightDensity middleA0 polyB
  fun_prop

private theorem outerK_measurable (u : ℝ) : Measurable (outerK u) := by unfold outerK; fun_prop

private theorem outerR0_integrable {p t : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) (ht : 0 < t) :
    IntegrableOn (fun s => lineDensity p s * outerR 1 s * BoseShape.C (s * t)) (Ioi 0) := by
  obtain ⟨_, hB, hF⟩ := outerR_linear_bound zero_lt_one
  exact pureC_integrable_of_linear hp hp₂ ht hB (outerR_measurable 1) hF

theorem outerJ_one_nonneg {p : ℝ} (hp : 1 ≤ p) : 0 ≤ outerJ p 1 := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact (mul_pos (mul_pos (lineDensity_pos (zero_lt_one.trans_le hp) hs) (outerR_one_pos hs))
    (BoseShape.C_pos (mul_pos hs zero_lt_one))).le

theorem outerJ_scaled_upper {p t : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (ht : 0 < t) (ht₁ : t ≤ 1) :
    outerJ p t ≤ t ^ (-(p + 2)) * outerJ p 1 := by
  let f (s : ℝ) := outerR 1 (s / t) * BoseShape.C s
  have hE : outerJ p t = t ^ (-p) * ∫ s : ℝ in Ioi 0, lineDensity p s * f s := by
    rw [← pureIntegral_scale ht f, outerJ]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s _
    dsimp only [f]
    rw [mul_div_cancel_left₀ _ ht.ne', mul_comm t s]
    ring
  have hM : (∫ s : ℝ in Ioi 0, lineDensity p s * f s) ≤ (1 / t ^ 2) * outerJ p 1 := by
    rw [outerJ, ← integral_const_mul]
    have h := integral_mono_ae
      (pureC_integrable_scaled hp hp₂ ht (outerR_measurable 1) (outerR_linear_bound zero_lt_one))
      ((outerR0_integrable hp hp₂ zero_lt_one).const_mul (1 / t ^ 2)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have h := mul_le_mul_of_nonneg_left (outerR_one_scale_upper ht ht₁ hs)
        (mul_pos (lineDensity_pos (zero_lt_one.trans_le hp) hs) (BoseShape.C_pos hs)).le
      rw [mul_one]
      calc
        _ = (lineDensity p s * BoseShape.C s) * outerR 1 (s / t) := by ring
        _ ≤ (lineDensity p s * BoseShape.C s) * (outerR 1 s / t ^ 2) := h
        _ = _ := by ring)
    simpa only [f, mul_assoc] using h
  rw [hE]
  refine (mul_le_mul_of_nonneg_left hM (Real.rpow_nonneg ht.le _)).trans_eq ?_
  rw [show -(p + 2) = -p - 2 by ring, Real.rpow_sub ht, Real.rpow_two]
  ring

private theorem outerK_reference {p u : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) :
    let f (s : ℝ) := lineDensity p s *
      (s * (1 - (12 / 25) * (1 - Real.exp (-s))) - (1 + u) * (1 - Real.exp (-s))) * BoseShape.C s
    IntegrableOn f (Ioi 0) ∧ (∫ s : ℝ in Ioi 0, f s) =
      (p - 1 - u) * pureZ p - (12 / 25) * pureQ p + (12 / 25) * p + 1 + u := by
  obtain ⟨hS, hSE⟩ := pureC_slope hp hp₂
  obtain ⟨hD, hDE⟩ := pureC_difference hp
  obtain ⟨hQ, hQE⟩ := pureC_slope_difference hp
  let A (s : ℝ) := lineDensity p s * s * BoseShape.C s
  let B (s : ℝ) := lineDensity p s * (1 - Real.exp (-s)) * BoseShape.C s
  let D (s : ℝ) := lineDensity p s * s * (1 - Real.exp (-s)) * BoseShape.C s
  let f (s : ℝ) := lineDensity p s *
    (s * (1 - (12 / 25) * (1 - Real.exp (-s))) - (1 + u) * (1 - Real.exp (-s))) * BoseShape.C s
  have hI : IntegrableOn (fun s => A s - (12 / 25) * D s) (Ioi 0) := hS.sub (hQ.const_mul _)
  have hEq (s : ℝ) : f s = A s - (12 / 25) * D s - (1 + u) * B s := by
    dsimp only [f, A, B, D]
    ring
  refine ⟨(hI.sub (hD.const_mul (1 + u))).congr (Eventually.of_forall fun s => (hEq s).symm), ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => hEq s),
    integral_sub hI (hD.const_mul (1 + u)), integral_sub hS (hQ.const_mul (12 / 25)),
    integral_const_mul, integral_const_mul]
  change (∫ s : ℝ in Ioi 0, A s) - (12 / 25) * (∫ s : ℝ in Ioi 0, D s) -
    (1 + u) * (∫ s : ℝ in Ioi 0, B s) = _
  rw [show (∫ s : ℝ in Ioi 0, A s) = p * pureZ p from hSE,
    show (∫ s : ℝ in Ioi 0, B s) = pureZ p - 1 from hDE,
    show (∫ s : ℝ in Ioi 0, D s) = pureQ p - p from hQE]
  ring

theorem outerK_scaled_reference_le {p u t : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) (hu : 7 / 8 ≤ u)
    (hut : u ≤ t) (ht₁ : t ≤ 1) :
    (∫ s : ℝ in Ioi 0, lineDensity p s * outerK u s * BoseShape.C (s * t)) ≤
      t ^ (-p) * ((p - 1 - u) * pureZ p - (12 / 25) * pureQ p + (12 / 25) * p + 1 + u) := by
  have hp₂ := hP.trans (by norm_num : (9 / 5 : ℝ) ≤ 2)
  have hu₀ := (by norm_num : (0 : ℝ) < 7 / 8).trans_le hu
  have ht := hu₀.trans_le hut
  let f (s : ℝ) := outerK u (s / t) * BoseShape.C s
  have hE : (∫ s : ℝ in Ioi 0, lineDensity p s * outerK u s * BoseShape.C (s * t)) =
      t ^ (-p) * ∫ s : ℝ in Ioi 0, lineDensity p s * f s := by
    rw [← pureIntegral_scale ht f]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s _
    dsimp only [f]
    rw [mul_div_cancel_left₀ _ ht.ne', mul_comm t s]
    ring
  obtain ⟨hI, hR⟩ := outerK_reference (u := u) hp hp₂
  have hM := integral_mono_ae
    (pureC_integrable_scaled hp hp₂ ht (outerK_measurable u) (outerK_linear_bound hu₀)) hI (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have h := mul_le_mul_of_nonneg_left (outerK_scale_upper hu₀ hut ht₁ hs)
      (mul_pos (lineDensity_pos (zero_lt_one.trans_le hp) hs) (BoseShape.C_pos hs)).le
    nlinarith only [h])
  rw [hR] at hM
  rw [hE]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg ht.le _)
  simpa only [f, mul_assoc] using hM

private theorem outerK_scaled_upper {p u t : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) (hu : 7 / 8 ≤ u)
    (hut : u ≤ t) (ht₁ : t ≤ 1) :
    (∫ s : ℝ in Ioi 0, lineDensity p s * outerK u s * BoseShape.C (s * t)) ≤ 21 / 100 := by
  have hZ : 1 ≤ pureZ p := by
    have h := pureZ_trapezoid_lower hp
    have h' : 0 ≤ (2 : ℝ) ^ (-p) * (1 + p / 4) := by positivity
    linarith
  have hU := mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hZ)
  have hB : (p - 1 - u) * pureZ p - (12 / 25) * pureQ p + (12 / 25) * p + 1 + u ≤ 4 / 25 := by
    nlinarith only [hU, pureK_unit_bound hp hP]
  refine (outerK_scaled_reference_le hp hP hu hut ht₁).trans ?_
  have ht := (by norm_num : (0 : ℝ) < 7 / 8).trans_le (hu.trans hut)
  refine (mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg ht.le _)).trans ?_
  have hP' := high_gap_inv_power_lt hp hP (hu.trans hut)
  linarith only [hP']

theorem outerR_direction_bound {p u t : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) (hu : 7 / 8 ≤ u)
    (hut : u ≤ t) (ht₁ : t ≤ 1) :
    (∫ s : ℝ in Ioi 0, lineDensity p s * outerR u s * BoseShape.C (s * t)) ≤
      u ^ 2 * t ^ (-(p + 2)) * outerJ p 1 + (1 - u) * (21 / 100) := by
  have hu₀ := (by norm_num : (0 : ℝ) < 7 / 8).trans_le hu
  have hu₁ := hut.trans ht₁
  have ht := hu₀.trans_le hut
  have hp₂ := hP.trans (by norm_num : (9 / 5 : ℝ) ≤ 2)
  obtain ⟨_, hRB, hR⟩ := outerR_linear_bound hu₀
  obtain ⟨_, hKB, hK⟩ := outerK_linear_bound hu₀
  have hI := pureC_integrable_of_linear hp hp₂ ht hRB (outerR_measurable u) hR
  have hJ := outerR0_integrable hp hp₂ ht
  have hK' := pureC_integrable_of_linear hp hp₂ ht hKB (outerK_measurable u) hK
  have h := integral_mono_ae hI ((hJ.const_mul (u ^ 2)).add (hK'.const_mul (1 - u))) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have h := mul_le_mul_of_nonneg_left (outerR_scale_bound hu₀ hu₁ hs)
      (mul_pos (lineDensity_pos (zero_lt_one.trans_le hp) hs) (BoseShape.C_pos (mul_pos hs ht))).le
    simp only [Pi.add_apply]
    nlinarith only [h])
  simp only [Pi.add_apply] at h
  rw [integral_add (hJ.const_mul (u ^ 2)) (hK'.const_mul (1 - u)),
    integral_const_mul, integral_const_mul] at h
  refine h.trans ?_
  have hJ' := mul_le_mul_of_nonneg_left (outerJ_scaled_upper hp hp₂ ht ht₁) (sq_nonneg u)
  have hK'' := mul_le_mul_of_nonneg_left (outerK_scaled_upper hp hP hu hut ht₁) (sub_nonneg.mpr hu₁)
  exact (add_le_add hJ' hK'').trans_eq (by ring)

end ACS12.GammaMeasure

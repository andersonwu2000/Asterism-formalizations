import ACS12.PureBose
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-! A whole-band bound for the exponentially shifted pure Bose moment. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaDeficit (lineDensity)

theorem Gamma_le_one_of_band {p : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) :
    Real.Gamma p ≤ 1 := by
  have h := Real.convexOn_Gamma.2 (mem_Ioi.mpr (show (0 : ℝ) < 1 from zero_lt_one))
    (show (2 : ℝ) ∈ Ioi 0 by norm_num) (sub_nonneg.mpr hp₂) (sub_nonneg.mpr hp)
    (show (2 - p) + (p - 1) = 1 by ring)
  have h2 : Real.Gamma 2 = 1 := by
    simpa using Real.Gamma_nat_eq_factorial 1
  simp only [smul_eq_mul, Real.Gamma_one, h2, mul_one] at h
  rwa [show (2 - p) + (p - 1) * 2 = p by ring,
    show (2 - p) + (p - 1) = 1 by ring] at h

private theorem Gamma_band_lower {p : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) :
    3 / 4 < Real.Gamma p := by
  have hp₀ := zero_lt_one.trans_le hp
  have hq : 1 ≤ 3 - p := by linarith
  have hq₀ := zero_lt_one.trans_le hq
  have hG := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma
    hp₀ hq₀ (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hMid : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
    ring
  rw [show (1 / 2 : ℝ) * p + 1 / 2 * (3 - p) = 3 / 2 by ring, hMid,
    ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hG
  have hA := pow_le_pow_left₀ (show 0 ≤ Real.sqrt Real.pi / 2 by positivity) hG 2
  rw [div_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le,
    Real.sq_sqrt (Real.Gamma_pos_of_pos hp₀).le, Real.sq_sqrt (Real.Gamma_pos_of_pos hq₀).le] at hA
  have hB := mul_le_of_le_one_right (Real.Gamma_pos_of_pos hp₀).le
    (Gamma_le_one_of_band hq (by linarith))
  linarith only [hA, hB, Real.pi_gt_three]

private theorem zetaThree_lower : (7 / 6 : ℝ) < powerTail 3 1 := by
  have hS := powerTail_summable (by norm_num : (1 : ℝ) < 3) 1
  have h := hS.sum_le_tsum (Finset.range 4) (fun _ _ => Real.rpow_nonneg (by positivity) _)
  have hE (j : ℕ) : ((1 : ℝ) + j) ^ (-(3 : ℝ)) = 1 / ((1 : ℝ) + j) ^ 3 := by
    rw [Real.rpow_neg (by positivity), show (3 : ℝ) = (3 : ℕ) by norm_num,
      Real.rpow_natCast, inv_eq_one_div]
  have hFin : (7 / 6 : ℝ) < ∑ j ∈ Finset.range 4, 1 / ((1 : ℝ) + (j : ℝ)) ^ 3 := by
    norm_num [Finset.sum_range_succ]
  unfold powerTail
  simp_rw [Nat.cast_one, hE] at h ⊢
  exact hFin.trans_le h

noncomputable def shiftedBoseMoment (p : ℝ) : ℝ :=
  ∫ s : ℝ in Ioi 0, lineDensity p s * polyB s * Real.exp (-s) * BoseShape.C s

private theorem shiftedBoseMoment_eq {p : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) :
    shiftedBoseMoment p =
      (2 : ℝ) ^ (-p) + p * (p - 1) * powerTail (p + 1) 1 +
        2 * p - p * (p + 1) * powerTail (p + 2) 1 := by
  have h := pureBoseB_moment hp hp₂ 1
  simp only [Nat.cast_one, mul_one, show (1 : ℕ) + 1 = 2 by decide,
    show (1 : ℝ) + 1 = 2 by norm_num] at h
  rw [powerTail_shift (by linarith : 1 < p + 1) 1, powerTail_shift (by linarith : 1 < p + 2) 1] at h
  simp only [Nat.cast_one, Real.one_rpow] at h
  unfold shiftedBoseMoment
  linarith only [h]

theorem shiftedBoseMoment_integrable {p : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) :
    IntegrableOn (fun s => lineDensity p s * polyB s * Real.exp (-s) * BoseShape.C s) (Ioi 0) := by
  have hG := Real.Gamma_pos_of_pos (zero_lt_one.trans_le hp)
  let f (s : ℝ) := lineDensity p s * polyB s * Real.exp (-s) * BoseShape.C s
  have hM : Measurable f := by
    unfold f lineDensity polyB BoseShape.C
    fun_prop
  have hMaj := ((expMoment_nat_integrable 1 zero_lt_one).add
    (expMoment_nat_integrable 2 zero_lt_one)).const_mul (Real.Gamma p)⁻¹
  apply hMaj.mono' hM.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs₀ : 0 < s := hs
  have hExp := Real.exp_pos (-s)
  have hP : s ^ (p - 1) ≤ 1 + s := by
    rcases le_total s 1 with h | h
    · exact (show s ^ (p - 1) ≤ 1 by
        simpa only [Real.one_rpow] using Real.rpow_le_rpow hs₀.le h (by linarith : 0 ≤ p - 1)).trans
        (le_add_of_nonneg_right hs₀.le)
    · exact (show s ^ (p - 1) ≤ s by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le h (by linarith : p - 1 ≤ 1)).trans
        (le_add_of_nonneg_left zero_le_one)
  have hB : polyB s ≤ s := by
    unfold polyB
    linarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs₀.le)]
  rw [Real.norm_of_nonneg (by
    exact mul_nonneg (mul_nonneg (mul_nonneg (lineDensity_pos (zero_lt_one.trans_le hp) hs₀).le
      (polyB_pos hs₀).le) hExp.le) (BoseShape.C_pos hs₀).le : 0 ≤ f s)]
  dsimp only [f, Pi.add_apply, pow_one, lineDensity]
  have hProd := mul_le_mul (div_le_div_of_nonneg_right hP hG.le) hB
    (polyB_pos hs₀).le (show 0 ≤ (1 + s) / Real.Gamma p by positivity)
  calc
    _ ≤ ((1 + s) / Real.Gamma p * s * Real.exp (-s)) * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hProd hExp.le)
        (BoseShape.C_lt_one hs₀).le (BoseShape.C_pos hs₀).le (by positivity)
    _ = _ := by ring

theorem shiftedBoseMoment_lt {p : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) :
    shiftedBoseMoment p < 17 / 75 := by
  have h1 : shiftedBoseMoment 1 < 17 / 100 := by
    have h := shiftedBoseMoment_eq le_rfl (by norm_num : (1 : ℝ) ≤ 2)
    rw [Real.rpow_neg (by norm_num), Real.rpow_one] at h
    norm_num at h
    linarith only [h, zetaThree_lower]
  have h2 : shiftedBoseMoment 2 < 17 / 100 := by
    have h := shiftedBoseMoment_eq (by norm_num : (1 : ℝ) ≤ 2) le_rfl
    rw [Real.rpow_neg (by norm_num), Real.rpow_two] at h
    norm_num at h
    linarith only [h, powerTail_three_lt, powerTail_four_gt]
  let f (q s : ℝ) := lineDensity q s * polyB s * Real.exp (-s) * BoseShape.C s
  have hΓ₁ : Real.Gamma 1 = 1 := Real.Gamma_one
  have hΓ₂ : Real.Gamma 2 = 1 := by simpa using Real.Gamma_nat_eq_factorial 1
  have hW (s : ℝ) (hs : 0 < s) :
      Real.Gamma p * f p s ≤ (2 - p) * f 1 s + (p - 1) * f 2 s := by
    have hC := (convexOn_rpow_left hs).2
      (show (0 : ℝ) ∈ univ from trivial) (show (1 : ℝ) ∈ univ from trivial)
      (sub_nonneg.mpr hp₂) (sub_nonneg.mpr hp) (show 2 - p + (p - 1) = 1 by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, mul_one, Real.rpow_zero, Real.rpow_one] at hC
    have hMul := mul_le_mul_of_nonneg_right hC
      (mul_nonneg (mul_nonneg (polyB_pos hs).le (Real.exp_pos (-s)).le) (BoseShape.C_pos hs).le)
    simp only [f, lineDensity, hΓ₁, hΓ₂, div_one, sub_self, Real.rpow_zero,
      show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    have hGp := (Real.Gamma_pos_of_pos (zero_lt_one.trans_le hp)).ne'
    calc
      _ = s ^ (p - 1) * (polyB s * Real.exp (-s) * BoseShape.C s) := by
        field_simp [hGp]
      _ ≤ _ := hMul.trans_eq (by ring)
  have hIp : IntegrableOn (f p) (Ioi 0) := shiftedBoseMoment_integrable hp hp₂
  have hI1 : IntegrableOn (f 1) (Ioi 0) := shiftedBoseMoment_integrable le_rfl (by norm_num)
  have hI2 : IntegrableOn (f 2) (Ioi 0) := shiftedBoseMoment_integrable (by norm_num) le_rfl
  have h := integral_mono_ae (hIp.const_mul (Real.Gamma p))
    ((hI1.const_mul (2 - p)).add (hI2.const_mul (p - 1))) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact hW s hs)
  simp only [Pi.add_apply] at h
  rw [integral_const_mul, integral_add (hI1.const_mul (2 - p)) (hI2.const_mul (p - 1)),
    integral_const_mul, integral_const_mul] at h
  change Real.Gamma p * shiftedBoseMoment p ≤ (2 - p) * shiftedBoseMoment 1 +
    (p - 1) * shiftedBoseMoment 2 at h
  have hMax := add_le_add (mul_le_mul_of_nonneg_left h1.le (sub_nonneg.mpr hp₂))
    (mul_le_mul_of_nonneg_left h2.le (sub_nonneg.mpr hp))
  by_contra! h'
  have hΓ := Gamma_band_lower hp hp₂
  have hProduct := mul_lt_mul_of_lt_of_le_of_nonneg_of_pos hΓ h' (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (show 0 < shiftedBoseMoment p by linarith)
  nlinarith only [h, hMax, hProduct]

end ACS12.GammaMeasure

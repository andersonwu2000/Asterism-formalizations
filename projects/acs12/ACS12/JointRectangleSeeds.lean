import ACS12.JointHeatCurvature
import ACS12.JointSharpGapEndpoint
import ACS12.PressureLikelihood
import ACS12.NativeLiteralRows

/-! Full curvature moments and the signed native seed on the joint rectangle. -/
namespace ACS12.GammaMeasure

open Set MeasureTheory Filter CenteredCircle.AllN
open GammaDeficit (lineDensity lineDensity_exp_integrable lineDensity_exp_integral)

theorem jointGapKp_lower {p : ℝ} (hp : 1 ≤ p) : (7 / 10 : ℝ) * p < jointGapKp p := by
  let W (q s : ℝ) := lineDensity (q + 1) s * Real.exp (-s)
  let T (s : ℝ) := polyA s * BoseShape.curvatureHeat s
  let F (q s : ℝ) := lineDensity q s * polyA s * s * (-BoseShape.C₁ s)
  have hp₀ := zero_lt_one.trans_le hp
  have hW (q : ℝ) (hq : 0 < q) : IntegrableOn (W q) (Ioi 0) := by
    simpa only [W,mul_one] using lineDensity_exp_integrable (show 0 < q + 1 by positivity) zero_lt_one
  have hW₁ (q : ℝ) (hq : 0 < q) : (∫ s : ℝ in Ioi 0, W q s) = 1 := by
    simpa only [W,mul_one,Real.one_rpow] using lineDensity_exp_integral (show 0 < q + 1 by positivity) zero_lt_one
  have hScale (q s : ℝ) (hq : 0 < q) (hs : 0 < s) : W q s * T s = q⁻¹ * F q s := by
    have he : Real.exp (-s) * Real.exp s = 1 := by rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
    have hs' : s ^ q = s ^ (q - 1) * s := by rw [← Real.rpow_add_one hs.ne',sub_add_cancel]
    unfold W T F lineDensity BoseShape.curvatureHeat
    rw [show q + 1 - 1 = q by ring,hs',Real.Gamma_add_one hq.ne']
    field_simp [hq.ne',(Real.Gamma_pos_of_pos hq).ne']
    linear_combination -(polyA s * BoseShape.C₁ s) * he
  have hWT (q : ℝ) (hq : 0 < q) : IntegrableOn (fun s => W q s * T s) (Ioi 0) := by
    apply ((jointGapKp_integral_bound hq).1.const_mul q⁻¹).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hScale q s hq hs).symm
  have hWM (q : ℝ) (hq : 0 < q) : (∫ s : ℝ in Ioi 0, W q s * T s) = q⁻¹ * jointGapKp q := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun s hs => hScale q s hq hs),integral_const_mul]
    rfl
  have hPos (s : ℝ) (hs : 0 < s) : 0 < W 1 s :=
    mul_pos (lineDensity_pos (by norm_num : (0 : ℝ) < 1 + 1) hs) (Real.exp_pos _)
  have hTM : MonotoneOn T (Ioi 0) := by
    intro x hx y hy hxy
    exact mul_le_mul (polyA_monotone_nonneg (show x∈Ici (0:ℝ) from (show 0<x from hx).le) (show y∈Ici (0:ℝ) from (show 0<y from hy).le) hxy) (BoseShape.curvatureHeat_mono hx hy hxy)
      (BoseShape.curvatureHeat_pos hx).le (polyA_pos hy).le
  have hRat (s : ℝ) (hs : 0 < s) : W p s / W 1 s =
      (Real.Gamma (1 + 1) / Real.Gamma (p + 1)) * s ^ (p - 1) := by
    have he : s ^ p = s ^ (p - 1) * s := by rw [← Real.rpow_add_one hs.ne',sub_add_cancel]
    unfold W lineDensity
    rw [show p + 1 - 1 = p by ring,show (1 + 1 - 1 : ℝ) = 1 by norm_num,he,Real.rpow_one]
    field_simp [hs.ne',Real.exp_ne_zero _, (Real.Gamma_pos_of_pos (by positivity : 0 < p + 1)).ne',
      (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 + 1)).ne']
  have hR : MonotoneOn (fun s => W p s / W 1 s) (Ioi 0) := by
    intro x hx y hy hxy
    change W p x / W 1 x ≤ W p y / W 1 y
    rw [hRat x hx,hRat y hy]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (show 0 < x from hx).le hxy (sub_nonneg.mpr hp))
      (by positivity : 0 ≤ Real.Gamma (1 + 1) / Real.Gamma (p + 1))
  have h := Pressure.likelihood_test_mono (hW 1 zero_lt_one) (hW p hp₀)
    (hWT 1 zero_lt_one) (hWT p hp₀) hPos hR hTM
  rw [hW₁ 1 zero_lt_one,hW₁ p hp₀,hWM 1 zero_lt_one,hWM p hp₀] at h
  norm_num at h
  have hK : (7 / 10 : ℝ) < jointGapKp 1 := by
    rw [jointGapKp_exact zero_lt_one]
    norm_num [pureQ,pureR,NativeCells.powerTail_four_eq]
    have hPi := pow_lt_pow_left₀ Real.pi_lt_d6 Real.pi_pos.le (by decide : 4 ≠ 0)
    linarith only [hPi,powerTail_three_bounds.1]
  have hMult := mul_lt_mul_of_pos_left (hK.trans_le h) hp₀
  rwa [← mul_assoc,mul_inv_cancel₀ hp₀.ne',one_mul,mul_comm p] at hMult

theorem jointNative_seed_pos {p u m : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (huL : 7 / 8 ≤ u) (hu₁ : u ≤ 1) (hmL : 2 * u - 1 ≤ m) (hmU : m ≤ u) :
    0 < pureRight p u (u + m) := by
  let x := u + m
  let A := middleA u
  have hxL : 13 / 8 ≤ x := by unfold x; linarith only [huL,hmL]
  have hxU : x ≤ 2 := by unfold x; linarith only [hu₁,hmU]
  have hx : 0 < x := (by norm_num : (0 : ℝ) < 13 / 8).trans_le hxL
  have hu : 0 < u := (by norm_num : (0 : ℝ) < 7 / 8).trans_le huL
  have hAL : (189 / 800 : ℝ) ≤ A := by
    have h := pow_le_pow_left₀ (sub_nonneg.mpr hu₁) (show 1 - u ≤ 1 / 8 by linarith only [huL]) 2
    unfold A middleA
    nlinarith only [h]
  have hAU : A ≤ 6 / 25 := middleA_le u
  have hδ : 0 ≤ 1 - u := sub_nonneg.mpr hu₁
  have hx₂ : x ^ 2 ≤ 2 * x := by nlinarith only [mul_le_mul_of_nonneg_right hxU hx.le]
  have hδX : (1 - u) * x ^ 2 ≤ (1 / 8) * 2 * x := by
    have h := mul_le_mul (show 1 - u ≤ 1 / 8 by linarith only [huL]) hx₂ (sq_nonneg x)
      (by norm_num : (0 : ℝ) ≤ 1 / 8)
    nlinarith only [h]
  have hδ' : (1 - u) * x ^ 2 / (p + 1) ≤ x / 8 := by
    apply (div_le_iff₀ (show 0 < p + 1 by positivity)).mpr
    nlinarith only [hδX,mul_nonneg (sub_nonneg.mpr hp) hx.le]
  have hB : (13 / 50 : ℝ) * x ≤ (1 / 2 - A) * x := by
    exact mul_le_mul_of_nonneg_right (by linarith only [hAU]) hx.le
  have hC : (1 / 6 - A / 2) * (p + 2) ≤ (1 / 6 - (189 / 800) / 2) * (19 / 5) := by
    exact mul_le_mul (by linarith only [hAL]) (by linarith only [hP]) (by positivity)
      (by norm_num)
  have hPoly : 0 < -(1 - u) * x ^ 2 / (p + 1) + (1 / 2 - A) * x - (1 / 6 - A / 2) * (p + 2) := by
    rw [neg_mul,neg_div]
    nlinarith only [hδ',hB,hC,hxL]
  have hBracket : 0 < -(1 - u) + ((1 / 2 - A) * (p + 1)) / x -
      ((1 / 6 - A / 2) * (p + 1) * (p + 2)) / x ^ 2 := by
    have he : (-(1 - u) + ((1 / 2 - A) * (p + 1)) / x -
        ((1 / 6 - A / 2) * (p + 1) * (p + 2)) / x ^ 2) * (x ^ 2 / (p + 1)) =
        -(1 - u) * x ^ 2 / (p + 1) + (1 / 2 - A) * x - (1 / 6 - A / 2) * (p + 2) := by
      field_simp [hx.ne',show p + 1 ≠ 0 by positivity] <;> ring
    exact pos_of_mul_pos_left (he.symm ▸ hPoly) (by positivity)
  exact (mul_pos (mul_pos (zero_lt_one.trans_le hp) (Real.rpow_pos_of_pos hx _)) hBracket).trans
    (pureRight_quadratic_lower hp (hP.trans (by norm_num)) hu hu₁ hx)

end ACS12.GammaMeasure

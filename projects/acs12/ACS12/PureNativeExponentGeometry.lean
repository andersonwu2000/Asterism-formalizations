import ACS12.PureNativeExponent

/-! Common logarithmic ranges and the monotone cap-log product. -/

namespace ACS12.GammaMeasure

open Set

theorem nativeL_mono_rev : AntitoneOn nativeL (Ioi 0) := by
  intro x hx y _ hxy
  exact neg_le_neg (Real.log_le_log hx hxy)

theorem nativeL_nonneg {u : ℝ} (hu : 0 < u) (hu' : u ≤ 1) : 0 ≤ nativeL u :=
  neg_nonneg.mpr (Real.log_nonpos hu.le hu')

theorem nativeL_half_bounds :
    (693 / 1000 : ℝ) < nativeL (1 / 2) ∧ nativeL (1 / 2) < 694 / 1000 := by
  unfold nativeL
  rw [one_div, Real.log_inv, neg_neg]
  exact ⟨by linarith only [Real.log_two_gt_d9], by linarith only [Real.log_two_lt_d9]⟩

theorem nativeL_threeFourths_bounds :
    (287 / 1000 : ℝ) < nativeL (3 / 4) ∧ nativeL (3 / 4) < 288 / 1000 := by
  have hL := Real.sum_range_le_log_div (x := 1 / 7) (by norm_num) (by norm_num) 3
  have hU := Real.log_div_le_sum_range_add (x := 1 / 7) (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at hL hU
  unfold nativeL
  rw [show (3 / 4 : ℝ) = (4 / 3)⁻¹ by norm_num, Real.log_inv, neg_neg]
  exact ⟨by linarith only [hL], by linarith only [hU]⟩

theorem nativeL_sevenEighths_bounds :
    (1335 / 10000 : ℝ) < nativeL (7 / 8) ∧ nativeL (7 / 8) < 134 / 1000 := by
  have hL := Real.sum_range_le_log_div (x := 1 / 15) (by norm_num) (by norm_num) 3
  have hU := Real.log_div_le_sum_range_add (x := 1 / 15) (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at hL hU
  unfold nativeL
  rw [show (7 / 8 : ℝ) = (8 / 7)⁻¹ by norm_num, Real.log_inv, neg_neg]
  exact ⟨by linarith only [hL], by linarith only [hU]⟩

theorem nativeCapLog_antitone {p : ℝ} (hP : p ≤ 9 / 5) :
    AntitoneOn (fun u => adjacentRatio u p * nativeL u) (Ioc 0 1) := by
  let B : ℝ := 2304 / 8575
  let d (u : ℝ) := 2 * B * u * nativeL u - adjacentRatio u p / u
  have hτ (u : ℝ) : HasDerivAt (fun u => adjacentRatio u p) (2 * B * u) u := by
    convert (((hasDerivAt_id u).pow 2).const_mul B).const_add
      (5 / 7 + (3 / 20) * (9 / 5 - p)) using 1
    · funext t
      unfold adjacentRatio
      dsimp only [B, Pi.pow_apply, id_eq]
      ring
    · norm_num [id_eq] <;> ring
  have hD (u : ℝ) (hu : 0 < u) : HasDerivAt (fun u => adjacentRatio u p * nativeL u) (d u) u := by
    convert (hτ u).mul (Real.hasDerivAt_log hu.ne').neg using 1
    simp only [d, nativeL, Pi.neg_apply]
    ring
  apply antitoneOn_of_deriv_nonpos (convex_Ioc _ _)
  · exact fun x hx => (hD x hx.1).continuousAt.continuousWithinAt
  · exact fun x hx => (hD x (interior_subset hx).1).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : x ∈ Ioc (0 : ℝ) 1 := interior_subset hx
    rw [(hD x hx'.1).deriv]
    have hL := Real.log_le_sub_one_of_pos (inv_pos.mpr hx'.1)
    rw [Real.log_inv] at hL
    change nativeL x ≤ x⁻¹ - 1 at hL
    have hQ := mul_le_mul_of_nonneg_left hL (show 0 ≤ x ^ 2 by positivity)
    have hE : x ^ 2 * (x⁻¹ - 1) = x * (1 - x) := by field_simp [hx'.1.ne'] <;> ring
    rw [hE] at hQ
    have hA : 5 / 7 ≤ adjacentRatio x p := by
      unfold adjacentRatio
      nlinarith only [sq_nonneg x, hP]
    apply nonpos_of_mul_nonpos_left (b := x) ?_ hx'.1
    unfold d
    have hF : (2 * B * x * nativeL x - adjacentRatio x p / x) * x =
        2 * B * (x ^ 2 * nativeL x) - adjacentRatio x p := by field_simp [hx'.1.ne'] <;> ring
    rw [hF]
    have hG := mul_le_mul_of_nonneg_left hQ (show 0 ≤ 2 * B by norm_num [B])
    dsimp only [B] at hG ⊢
    nlinarith only [hG, hA, sq_nonneg (x - 1 / 2)]

theorem nativeCapLog_middle_lower {p u : ℝ} (hP : p ≤ 9 / 5) (hu : 0 < u) (hu' : u ≤ 3 / 4) :
    248 / 1000 < adjacentRatio u p * nativeL u := by
  have hA := nativeCapLog_antitone hP (show u ∈ Ioc 0 1 from ⟨hu, hu'.trans (by norm_num)⟩)
    (show (3 / 4 : ℝ) ∈ Ioc 0 1 by constructor <;> norm_num) hu'
  have hτ := (adjacentRatio_antitone (3 / 4)) hP
  have hE := mul_le_mul hτ nativeL_threeFourths_bounds.1.le (by norm_num : (0 : ℝ) ≤ 287 / 1000)
    (adjacentRatio_pos (u := 3 / 4) hP).le
  exact ((show (248 / 1000 : ℝ) < adjacentRatio (3 / 4) (9 / 5) * (287 / 1000) by
    norm_num [adjacentRatio]).trans_le hE).trans_le hA

theorem nativeCapLog_upper_band {p u : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hu : 3 / 4 ≤ u) (hu' : u ≤ 7 / 8) :
    1228 / 10000 < adjacentRatio u p * nativeL u ∧ adjacentRatio u p * nativeL u < 284 / 1000 := by
  have hu₀ := (by norm_num : (0 : ℝ) < 3 / 4).trans_le hu
  have hU : u ∈ Ioc (0 : ℝ) 1 := ⟨hu₀, hu'.trans (by norm_num)⟩
  have hA := nativeCapLog_antitone hP hU (show (7 / 8 : ℝ) ∈ Ioc 0 1 by constructor <;> norm_num) hu'
  have hB := nativeCapLog_antitone hP (show (3 / 4 : ℝ) ∈ Ioc 0 1 by constructor <;> norm_num) hU hu
  have hτ₁ := (adjacentRatio_antitone (7 / 8)) hP
  have hτ₂ := (adjacentRatio_antitone (3 / 4)) hp
  have h₁ := mul_le_mul hτ₁ nativeL_sevenEighths_bounds.1.le (by norm_num : (0 : ℝ) ≤ 1335 / 10000)
    (adjacentRatio_pos (u := 7 / 8) hP).le
  have h₂ := mul_le_mul hτ₂ nativeL_threeFourths_bounds.2.le
    (nativeL_nonneg (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num))
    (adjacentRatio_pos (u := 3 / 4) (p := 1) (by norm_num)).le
  constructor
  · exact ((show (1228 / 10000 : ℝ) < adjacentRatio (7 / 8) (9 / 5) * (1335 / 10000) by
      norm_num [adjacentRatio]).trans_le h₁).trans_le hA
  · exact (hB.trans h₂).trans_lt (by norm_num [adjacentRatio])

end ACS12.GammaMeasure

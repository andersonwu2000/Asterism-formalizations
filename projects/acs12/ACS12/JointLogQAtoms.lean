import ACS12.JointLogEndpoint

/-! The retained finite atoms of the complete Q curvature bounds. -/
namespace ACS12.GammaMeasure

open Set

private theorem slope_positive_chord {x c p : ℝ} (hx : 0 < x) (hc : 0 < c)
    (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (h₁ : c < zetaCurvatureSlope 1 x) (h₂ : c < zetaCurvatureSlope (9 / 5) x) :
    c < zetaCurvatureSlope p x := by
  let t := (5 / 4) * (p - 1)
  let l := Real.log x
  let B (q : ℝ) := peanoExponentQuadratic q l
  let W (q : ℝ) := x ^ (-(q + 2))
  have ht : 0 ≤ t := by dsimp only [t]; linarith only [hp]
  have ht' : t ≤ 1 := by dsimp only [t]; linarith only [hP]
  have hB₁ : 0 < B 1 := pos_of_mul_pos_right (hc.trans h₁) (Real.rpow_nonneg hx.le _)
  have hB₂ : 0 < B (9 / 5) := pos_of_mul_pos_right (hc.trans h₂) (Real.rpow_nonneg hx.le _)
  have hA : 0 < (1 - t) * B 1 + t * B (9 / 5) := by
    rcases lt_or_eq_of_le ht' with h | h
    · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr h) hB₁) (mul_nonneg ht hB₂.le)
    · simpa only [h,sub_self,zero_mul,one_mul,zero_add] using hB₂
  have hE : B p = (1 - t) * B 1 + t * B (9 / 5) +
      (16 / 25) * ((1 - t) * t * l ^ 2) := by dsimp only [B,t,peanoExponentQuadratic]; ring
  have hB : (1 - t) * B 1 + t * B (9 / 5) ≤ B p := by
    rw [hE]
    exact le_add_of_nonneg_right (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (sub_nonneg.mpr ht') ht) (sq_nonneg l)))
  have hLog := strictConcaveOn_log_Ioi.concaveOn.2 (show B 1 ∈ Ioi 0 from hB₁)
    (show B (9 / 5) ∈ Ioi 0 from hB₂) (sub_nonneg.mpr ht') ht (sub_add_cancel 1 t)
  simp only [smul_eq_mul] at hLog
  have hQ := hLog.trans (Real.log_le_log hA hB)
  have hEq (q : ℝ) (hq : 0 < B q) : Real.log (zetaCurvatureSlope q x) =
      -(q + 2) * l + Real.log (B q) := by
    change Real.log (W q * B q) = _
    dsimp only [W]
    rw [Real.log_mul (Real.rpow_pos_of_pos hx _).ne' hq.ne', Real.log_rpow hx]
  have hLog₁ := Real.log_lt_log hc h₁
  have hLog₂ := Real.log_lt_log hc h₂
  rw [hEq 1 hB₁] at hLog₁
  rw [hEq (9 / 5) hB₂] at hLog₂
  have hMix : 0 < (1 - t) * (-(1 + 2) * l + Real.log (B 1) - Real.log c) +
      t * (-(9 / 5 + 2) * l + Real.log (B (9 / 5)) - Real.log c) := by
    rcases lt_or_eq_of_le ht' with h | h
    · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr h) (sub_pos.mpr hLog₁))
        (mul_nonneg ht (sub_nonneg.mpr hLog₂.le))
    · simpa only [h,sub_self,zero_mul,one_mul,zero_add] using sub_pos.mpr hLog₂
  have hEq' : (1 - t) * (-(1 + 2) * l) + t * (-(9 / 5 + 2) * l) = -(p + 2) * l := by
    dsimp only [t]; ring
  have hPos : 0 < zetaCurvatureSlope p x := mul_pos (Real.rpow_pos_of_pos hx _) (hA.trans_le hB)
  apply (Real.log_lt_log_iff hc hPos).mp
  rw [hEq p (hA.trans_le hB)]
  nlinarith only [hQ,hMix,hEq']

private theorem slope_lower_from_log {p x l u r c : ℝ} (hp : 1 ≤ p) (hl : 0 ≤ l)
    (hL : l ≤ Real.log x) (hU : Real.log x ≤ u) (hr : 0 ≤ r)
    (hR : r ≤ x ^ (-(p + 2))) (hB : 0 ≤ -(p * (p + 1)) * u ^ 2 + (4 * p + 2) * l - 2)
    (hc : c < r * (-(p * (p + 1)) * u ^ 2 + (4 * p + 2) * l - 2)) :
    c < zetaCurvatureSlope p x := by
  have hP := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hl.trans hL) hU 2)
    (show 0 ≤ p * (p + 1) by positivity)
  have hQ := mul_le_mul_of_nonneg_left hL (show 0 ≤ 4 * p + 2 by positivity)
  have h := show -(p * (p + 1)) * u ^ 2 + (4 * p + 2) * l - 2 ≤ peanoExponentQuadratic p (Real.log x) by
    unfold peanoExponentQuadratic
    nlinarith only [hP,hQ]
  exact hc.trans_le (mul_le_mul hR h hB (hr.trans hR))

theorem zetaSlope_two_gt {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    7 / 50 < zetaCurvatureSlope p 2 := by
  have hL : (693147 / 1000000 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hU : Real.log 2 ≤ 693148 / 1000000 := by linarith only [Real.log_two_lt_d9]
  apply slope_positive_chord (by norm_num) (by norm_num) hp hP
  · exact slope_lower_from_log le_rfl (by norm_num) hL hU (r := 1 / 8) (by norm_num)
      (by norm_num [Real.rpow_neg, Real.rpow_ofNat]) (by norm_num) (by norm_num)
  · have h : (71793 / 1000000 : ℝ) ≤ (2 : ℝ) ^ (-(19 : ℝ) / 5) := by
      apply (Real.rpow_le_rpow_iff (by norm_num) (Real.rpow_nonneg (by norm_num) _)
        (z := (5 : ℝ)) (by norm_num)).mp
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    exact slope_lower_from_log (by norm_num) (by norm_num) hL hU (r := 71793 / 1000000) (by norm_num)
      (by simpa only [show -(9 / 5 + 2 : ℝ) = -(19 : ℝ) / 5 by norm_num] using h) (by norm_num) (by norm_num)

theorem zetaSlope_three_gt {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    3 / 100 < zetaCurvatureSlope p 3 := by
  have hL := log_three_tight.1.le
  have hU := log_three_tight.2.le
  apply slope_positive_chord (by norm_num) (by norm_num) hp hP
  · exact slope_lower_from_log le_rfl (by norm_num) hL hU (r := 1 / 27) (by norm_num)
      (by norm_num [Real.rpow_neg, Real.rpow_ofNat]) (by norm_num) (by norm_num)
  · have h : (15379 / 1000000 : ℝ) ≤ (3 : ℝ) ^ (-(19 : ℝ) / 5) := by
      apply (Real.rpow_le_rpow_iff (by norm_num) (Real.rpow_nonneg (by norm_num) _)
        (z := (5 : ℝ)) (by norm_num)).mp
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
    exact slope_lower_from_log (by norm_num) (by norm_num) hL hU (r := 15379 / 1000000) (by norm_num)
      (by simpa only [show -(9 / 5 + 2 : ℝ) = -(19 : ℝ) / 5 by norm_num] using h) (by norm_num) (by norm_num)

theorem zetaSlope_two_lt {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    zetaCurvatureSlope p 2 < 23 / 125 := by
  let t := p - 1
  let l := Real.log 2
  have ht : 0 ≤ t := sub_nonneg.mpr hp
  have hl : 693 / 1000 < l := by dsimp only [l]; linarith only [Real.log_two_gt_d9]
  have hu : l < 694 / 1000 := by dsimp only [l]; linarith only [Real.log_two_lt_d9]
  have hL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 693 / 1000) hl.le 2
  have hA : peanoExponentQuadratic p l ≤ 121 / 100 + (67 / 50) * t := by
    have hC : peanoExponentQuadratic p l =
        -2 * l ^ 2 + 6 * l - 2 + t * (4 * l - 3 * l ^ 2) - t ^ 2 * l ^ 2 := by
      dsimp only [t,peanoExponentQuadratic]; ring
    have hT := mul_le_mul_of_nonneg_left (show 4 * l - 3 * l ^ 2 ≤ 67 / 50 by linarith only [hL,hu]) ht
    rw [hC]
    nlinarith only [hT,hL,hu,mul_nonneg (sq_nonneg t) (sq_nonneg l)]
  have hExp : (2 : ℝ) ^ (-(p + 2)) ≤ (8 * (1 + (693 / 1000) * t))⁻¹ := by
    have h1 : (2 : ℝ) ^ (-(p + 2)) = (8 * Real.exp (l * t))⁻¹ := by
      rw [show -(p + 2) = -(3 + t) by dsimp only [t]; ring, Real.rpow_neg (by norm_num),
        Real.rpow_add (by norm_num), Real.rpow_def_of_pos (by norm_num) (y := t)]
      norm_num [Real.rpow_ofNat,l]
    rw [h1]
    apply inv_anti₀ (by positivity)
    have h := Real.add_one_le_exp (l * t)
    have hLt := mul_le_mul_of_nonneg_right hl.le ht
    linarith only [h,hLt]
  have hDen : 0 < 8 * (1 + (693 / 1000) * t) := by positivity
  have hB : 0 ≤ 121 / 100 + (67 / 50) * t := by positivity
  unfold zetaCurvatureSlope
  change _ * peanoExponentQuadratic p l < _
  have h := (mul_le_mul_of_nonneg_left hA (Real.rpow_nonneg (by norm_num) _)).trans
    (mul_le_mul_of_nonneg_right hExp hB)
  refine h.trans_lt ?_
  rw [inv_mul_eq_div]
  apply (div_lt_iff₀ hDen).mpr
  have ht' : t ≤ 4 / 5 := by dsimp only [t]; linarith only [hP]
  linarith only [ht']

end ACS12.GammaMeasure

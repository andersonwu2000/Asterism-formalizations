import ACS12.JointLowerFiniteAlgebra

/-! Uniform price of the second literal native atom. -/
namespace ACS12.GammaMeasure

open Set

private theorem lowerHeadOne_poly {p : ℝ} (hp : 1 ≤ p) (hpP : p ≤ 9 / 5) :
    let a := lowerNativeAlpha p
    let A := (p - 1) * (96 * p / 25 - 18)
    let B := (p + 2) * (39 * p / 25 + 9)
    let C := (9 / 5) * (p + 2) * (p + 3)
    10 < -a * (13 / 8) ^ 2 + A * (13 / 8) + B - C / (13 / 8) ∧
      0 < -(87 / 64) * a + (3 / 8) * A + (3 / 26) * C := by
  let a := lowerNativeAlpha p
  let A := (p - 1) * (96 * p / 25 - 18)
  let B := (p + 2) * (39 * p / 25 + 9)
  let C := (9 / 5) * (p + 2) * (p + 3)
  let z := (5 / 4) * (p - 1)
  have hz : 0 ≤ z := mul_nonneg (by norm_num) (sub_nonneg.mpr hp)
  have hz₁ : 0 ≤ 1 - z := by unfold z; linarith only [hpP]
  have hp₁ : 0 < p + 1 := by linarith only [hp]
  constructor
  · change 10 < -a * (13 / 8) ^ 2 + A * (13 / 8) + B - C / (13 / 8)
    apply (lt_of_mul_lt_mul_left _ hp₁.le)
    have he : (p + 1) * (-a * (13 / 8) ^ 2 + A * (13 / 8) + B - C / (13 / 8) - 10) =
        1 / 4 + (21483 / 1300) * (1 - z) ^ 3 + (98911 / 3250) * z * (1 - z) ^ 2 +
          (322499 / 32500) * z ^ 2 * (1 - z) + (3644 / 40625) * z ^ 3 := by
      unfold a A B C z lowerNativeAlpha
      field_simp [hp₁.ne']
      ring
    have hP : 0 < (1 / 4 : ℝ) + (21483 / 1300) * (1 - z) ^ 3 + (98911 / 3250) * z * (1 - z) ^ 2 +
        (322499 / 32500) * z ^ 2 * (1 - z) + (3644 / 40625) * z ^ 3 := by positivity
    rw [← he,mul_sub] at hP
    linarith only [hP]
  · apply pos_of_mul_pos_right _ hp₁.le
    have he : (p + 1) * (-(87 / 64) * a + (3 / 8) * A + (3 / 26) * C) =
        1 + (259 / 65) * (1 - z) ^ 3 + (47163 / 6500) * z * (1 - z) ^ 2 +
          (35733 / 16250) * z ^ 2 * (1 - z) + (17131 / 162500) * z ^ 3 := by
      unfold a A C z lowerNativeAlpha
      field_simp [hp₁.ne']
      ring
    rw [he]
    positivity

private theorem lowerHeadOne_quotient {p x : ℝ} (hp : 1 ≤ p) (hpP : p ≤ 9 / 5)
    (hx : x ∈ Icc (13 / 8 : ℝ) 2) :
    0 < lowerHead₁Left p (13 / 8) / (13 / 8) ∧
      lowerHead₁Left p (13 / 8) / (13 / 8) ≤ lowerHead₁Left p x / x := by
  let a := lowerNativeAlpha p
  let A := (p - 1) * (96 * p / 25 - 18)
  let B := (p + 2) * (39 * p / 25 + 9)
  let C := (9 / 5) * (p + 2) * (p + 3)
  let c : ℝ := 13 / 8
  have hc : 0 < c := by norm_num [c]
  have hx₀ := hc.trans_le hx.1
  have ha : 0 ≤ a := (lowerNativeAlpha_bounds hp hpP).1
  have hC : 0 ≤ C := by unfold C; have := zero_lt_one.trans_le hp; positivity
  have hP := lowerHeadOne_poly hp hpP
  change 10 < -a * c ^ 2 + A * c + B - C / c ∧
    0 < -(87 / 64) * a + (3 / 8) * A + (3 / 26) * C at hP
  have hEq (y : ℝ) (hy : 0 < y) : lowerHead₁Left p y / y = -a * y ^ 2 + A * y + B - C / y := by
    unfold lowerHead₁Left a A B C
    field_simp [hy.ne']
  rw [hEq c hc,hEq x hx₀]
  constructor
  · linarith only [hP.1]
  · have hC' : C / (2 * c) ≤ C / (x * c) :=
      div_le_div_of_nonneg_left hC (mul_pos hx₀ hc) (mul_le_mul_of_nonneg_right hx.2 hc.le)
    have hA' := mul_le_mul_of_nonneg_left (show x + c ≤ 2 + c by linarith only [hx.2]) ha
    have hQ : 0 ≤ -a * (x + c) + A + C / (x * c) := by
      have he : (3 / 8 : ℝ) * (-a * (2 + c) + A + C / (2 * c)) =
          -(87 / 64) * a + (3 / 8) * A + (3 / 26) * C := by unfold c; ring
      have h := pos_of_mul_pos_right (he ▸ hP.2 : 0 < (3 / 8 : ℝ) * (-a * (2 + c) + A + C / (2 * c)))
        (by norm_num : (0 : ℝ) ≤ 3 / 8)
      linarith only [h,hC',hA']
    have he : (-a * x ^ 2 + A * x + B - C / x) - (-a * c ^ 2 + A * c + B - C / c) =
        (x - c) * (-a * (x + c) + A + C / (x * c)) := by
      field_simp [hx₀.ne',hc.ne']
      ring
    exact sub_nonneg.mp (he.symm ▸ mul_nonneg (sub_nonneg.mpr hx.1) hQ)

private theorem lowerHeadOne_ratio {p : ℝ} (hp : 1 ≤ p) :
    (2479 / 1000) * (p + 1) < (3 / 2 : ℝ) ^ (p + 3) := by
  let l := Real.log (3 / 2)
  let t := l * (p + 1)
  have hL : 4054 / 10000 < l := by
    have h := Real.hasSum_log_one_add (a := (1 / 2 : ℝ)) (by norm_num)
    have hS := h.summable.sum_le_tsum (Finset.range 8) (fun _ _ => by positivity)
    rw [h.tsum_eq] at hS
    norm_num [Finset.sum_range_succ] at hS
    exact (by norm_num : (4054 / 10000 : ℝ) < _).trans_le hS
  have he : (27182 / 10000 : ℝ) < Real.exp 1 := by
    have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num) 8
    norm_num [Finset.sum_range_succ] at h
    exact (by norm_num : (27182 / 10000 : ℝ) < _).trans_le h
  have hT : t ≤ Real.exp (t - 1) := by linarith only [Real.add_one_le_exp (t - 1)]
  have hE : Real.exp 1 * t ≤ Real.exp t := by
    have h := mul_le_mul_of_nonneg_left hT (Real.exp_pos 1).le
    rwa [← Real.exp_add,show (1 : ℝ) + (t - 1) = t by ring] at h
  have hP : 0 < p + 1 := by linarith only [hp]
  have hK : (2479 / 1000 : ℝ) < (9 / 4) * l * Real.exp 1 := by
    have h := mul_lt_mul'' hL he (by norm_num : (0 : ℝ) ≤ 4054 / 10000) (by norm_num : (0 : ℝ) ≤ 27182 / 10000)
    linarith only [h]
  have h' := mul_lt_mul_of_pos_right hK hP
  rw [show p + 3 = ((2 : ℕ) : ℝ) + (p + 1) by push_cast; ring,Real.rpow_add (by norm_num),
    Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num)]
  change _ < (3 / 2 : ℝ) ^ 2 * Real.exp t
  unfold t at hE ⊢
  nlinarith only [h',hE]

private noncomputable def lowerHeadOneReceiver (p : ℝ) : ℝ :=
  (2479 / 1000) * (p + 1) * ((87 / 13) * p ^ 2 - (37581 / 1300) * p + 10557 / 260) -
    (2479 / 1000) * (2028 / 1600) * p * (p - 1) * (2 - p) +
    (513 / 100) * p ^ 2 + (54 / 25) * p - 405 / 4

private theorem lowerHeadOneReceiver_gt {p : ℝ} (hp : 1 ≤ p) (hpP : p ≤ 9 / 5) :
    -(189 / 80) * (3 : ℝ) ^ p < lowerHeadOneReceiver p := by
  let t := (549 / 500) * (p - 1)
  let P := lowerHeadOneReceiver p + (189 / 80) * 3 * (1 + t + t ^ 2 / 2)
  have hL : (549 / 500 : ℝ) ≤ Real.log 3 := by linarith only [log_three_tight.1]
  have ht : 0 ≤ t := mul_nonneg (by norm_num) (sub_nonneg.mpr hp)
  have hExp : 1 + t + t ^ 2 / 2 ≤ Real.exp ((p - 1) * Real.log 3) :=
    (Real.quadratic_le_exp_of_nonneg ht).trans
      (Real.exp_le_exp.mpr (by unfold t; simpa only [mul_comm] using mul_le_mul_of_nonneg_right hL (sub_nonneg.mpr hp)))
  have hPow : (3 : ℝ) ^ p = 3 * Real.exp ((p - 1) * Real.log 3) := by
    conv_lhs => rw [show p = 1 + (p - 1) by ring,Real.rpow_add (by norm_num),Real.rpow_one,
      Real.rpow_def_of_pos (by norm_num),mul_comm (Real.log 3) (p - 1)]
  have hP : 0 < P := by
    by_cases hp₀ : p ≤ 7 / 5
    · let z := (5 / 2) * (p - 1)
      have hz : 0 ≤ z := mul_nonneg (by norm_num) (sub_nonneg.mpr hp)
      have hz₁ : 0 ≤ 1 - z := by unfold z; linarith only [hp₀]
      have he : P = 1 / 4 + (2628391 / 650000) * (1 - z) ^ 3 + (83217633 / 13000000) * z * (1 - z) ^ 2 +
          (4314538671 / 3250000000) * z ^ 2 * (1 - z) + (756416981 / 3250000000) * z ^ 3 := by
        unfold P t z lowerHeadOneReceiver
        ring
      rw [he]
      positivity
    · let z := (5 / 2) * (p - 7 / 5)
      have hz : 0 ≤ z := mul_nonneg (by norm_num) (sub_nonneg.mpr (le_of_not_ge hp₀))
      have hz₁ : 0 ≤ 1 - z := by unfold z; linarith only [hpP]
      have he : P = 1 / 4 + (756416981 / 3250000000) * (1 - z) ^ 3 + (44792643 / 650000000) * z * (1 - z) ^ 2 +
          (6311628669 / 1625000000) * z ^ 2 * (1 - z) + (2157505333 / 406250000) * z ^ 3 := by
        unfold P t z lowerHeadOneReceiver
        ring
      rw [he]
      positivity
  rw [hPow]
  unfold P at hP
  linarith only [hP,hExp]

theorem lowerNative_head_one_third {p d : ℝ} (hp : 1 ≤ p) (hpP : p ≤ 9 / 5)
    (hd : d ∈ Icc (0 : ℝ) (1 / 8)) :
    let m := 1 - 2 * d;
    -(1 / 10 : ℝ) < m ^ (p + 2) / (p * (p + 1)) * lowerNativeSite 3 p 1 d := by
  let m := 1 - 2 * d
  let x := 2 - 3 * d
  let y := x + 1
  let B := lowerHead₁Left p (13 / 8) / (13 / 8)
  let N := m ^ (p + 2) * y ^ (-p - 3)
  have hm : 0 < m := by unfold m; linarith only [hd.2]
  have hx : x ∈ Icc (13 / 8 : ℝ) 2 := ⟨by unfold x; linarith only [hd.2],by unfold x; linarith only [hd.1]⟩
  have hx₀ : 0 < x := (by norm_num : (0 : ℝ) < 13 / 8).trans_le hx.1
  have hy : 21 / 8 ≤ y := by unfold y; linarith only [hx.1]
  have hy₀ : 0 < y := (by norm_num : (0 : ℝ) < 21 / 8).trans_le hy
  have hN : 0 < N := by unfold N; positivity
  have h₂ := lowerHeadOne_quotient hp hpP hx
  have hp₀ := zero_lt_one.trans_le hp
  have hp₁ : 0 < p + 1 := by positivity
  have hR : (2479 / 1000) * (p + 1) < (y / x) ^ (p + 3) := by
    apply (lowerHeadOne_ratio hp).trans_le
    apply Real.rpow_le_rpow (by norm_num) _ (by positivity)
    apply (le_div_iff₀ hx₀).mpr
    unfold y
    linarith only [hx.2]
  have hL : (2479 / 1000) * (p + 1) * B ≤ (y / x) ^ (p + 3) * (lowerHead₁Left p x / x) :=
    mul_le_mul hR.le h₂.2 h₂.1.le (Real.rpow_nonneg (by positivity) _)
  have hA := (lowerNativeAlpha_bounds hp hpP).1
  have hRight : (513 / 100) * p ^ 2 + (54 / 25) * p - 405 / 4 ≤ lowerHead₁Right p y := by
    have h := mul_le_mul_of_nonneg_left hy (show 0 ≤ (18 / 5) * (p - 1) * (p + 5) from
      mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hp)) (by positivity))
    have h₀ := mul_nonneg hA (sq_nonneg y)
    unfold lowerHead₁Right
    nlinarith only [h,h₀]
  have hSum : lowerHeadOneReceiver p ≤ (y / x) ^ (p + 3) * (lowerHead₁Left p x / x) + lowerHead₁Right p y := by
    have he : lowerHeadOneReceiver p = (2479 / 1000) * (p + 1) * B +
        ((513 / 100) * p ^ 2 + (54 / 25) * p - 405 / 4) := by
      unfold lowerHeadOneReceiver B lowerHead₁Left lowerNativeAlpha
      field_simp [hp₁.ne']
      ring
    rw [he]
    linarith only [hL,hRight]
  have hScale : N ≤ (8 / 7) * (3 : ℝ) ^ (-p - 3) := by
    have hN' : N = (m / y) ^ (p + 2) / y := by
      unfold N
      rw [Real.div_rpow hm.le hy₀.le,show -p - 3 = -(p + 2) - 1 by ring,Real.rpow_sub_one hy₀.ne',
        Real.rpow_neg hy₀.le]
      ring
    have hmy : m / y ≤ 1 / 3 := by
      apply (div_le_iff₀ hy₀).mpr
      unfold m y x
      linarith only [hd.1]
    have hP := Real.rpow_le_rpow (div_nonneg hm.le hy₀.le) hmy (show 0 ≤ p + 2 by positivity)
    have hY : y⁻¹ ≤ 8 / 21 := by
      simpa only [show (8 / 21 : ℝ) = (21 / 8 : ℝ)⁻¹ by norm_num] using inv_anti₀ (by norm_num : (0 : ℝ) < 21 / 8) hy
    rw [hN',div_eq_mul_inv]
    refine (mul_le_mul hP hY (inv_nonneg.mpr hy₀.le) (Real.rpow_nonneg (by norm_num) _)).trans_eq ?_
    rw [one_div,Real.inv_rpow (by norm_num),← Real.rpow_neg (by norm_num),
      show -p - 3 = -(p + 2) - 1 by ring,Real.rpow_sub_one (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  have hEq := lowerNativeHead_one_eq hp (show d < 1 / 2 by linarith only [hd.2])
  change lowerNativeSite 3 p 1 d / (p * (p + 1)) =
    x ^ (-p - 4) * lowerHead₁Left p x + y ^ (-p - 3) * lowerHead₁Right p y at hEq
  have hF : y ^ (-p - 3) * ((y / x) ^ (p + 3) * (lowerHead₁Left p x / x)) =
      x ^ (-p - 4) * lowerHead₁Left p x := by
    rw [Real.div_rpow hy₀.le hx₀.le,show -p - 3 = -(p + 3) by ring,Real.rpow_neg hy₀.le,
      show -p - 4 = -(p + 3) - 1 by ring,Real.rpow_sub_one hx₀.ne',Real.rpow_neg hx₀.le]
    field_simp [(Real.rpow_pos_of_pos hy₀ (p + 3)).ne']
  have hStrict := mul_lt_mul_of_pos_left ((lowerHeadOneReceiver_gt hp hpP).trans_le hSum) hN
  have hBottom : -(1 / 10 : ℝ) ≤ N * (-(189 / 80) * (3 : ℝ) ^ p) := by
    have h := mul_le_mul_of_nonpos_right hScale (show -(189 / 80 : ℝ) * (3 : ℝ) ^ p ≤ 0 by
      exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _))
    have he : (3 : ℝ) ^ (-p - 3) * (3 : ℝ) ^ p = (1 / 27 : ℝ) := by
      rw [← Real.rpow_add (by norm_num),show -p - 3 + p = -(3 : ℝ) by ring,
        Real.rpow_neg (by norm_num),show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,Real.rpow_natCast]
      norm_num
    rw [show (8 / 7 : ℝ) * (3 : ℝ) ^ (-p - 3) * (-(189 / 80) * (3 : ℝ) ^ p) =
      (8 / 7) * (-(189 / 80)) * ((3 : ℝ) ^ (-p - 3) * (3 : ℝ) ^ p) by ring,he] at h
    norm_num at h
    linarith only [h]
  have h := hBottom.trans_lt hStrict
  unfold N at h
  rw [mul_assoc,mul_add,hF,← hEq] at h
  change _ < m ^ (p + 2) / (p * (p + 1)) * lowerNativeSite 3 p 1 d
  simpa only [div_mul_eq_mul_div,← mul_div_assoc] using h

end ACS12.GammaMeasure

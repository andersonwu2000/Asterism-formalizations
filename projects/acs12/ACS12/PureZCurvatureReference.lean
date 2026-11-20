import ACS12.PureZCurvatureDensity

/-! Directed whole-band bounds for the three-site trapezoidal reference. -/

namespace ACS12.GammaMeasure

open Set

noncomputable def zetaCurvatureReference (p : ℝ) : ℝ :=
  -zetaCurvaturePrimitive p 4 + zetaCurvature p 2 + zetaCurvature p 3 + (1 / 2) * zetaCurvature p 4

private theorem log_three_bounds : (1098 / 1000 : ℝ) < Real.log 3 ∧ Real.log 3 < 1099 / 1000 := by
  have hL := Real.sum_range_le_log_div (x := 1 / 2) (by norm_num) (by norm_num) 5
  have hU := Real.log_div_le_sum_range_add (x := 1 / 2) (by norm_num) (by norm_num) 7
  norm_num [Finset.sum_range_succ] at hL hU
  constructor <;> linarith only [hL, hU]

private theorem log_four_eq : Real.log (4 : ℝ) = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  ring

private theorem exp_chord {a k t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) (ht' : t ≤ 4 / 5)
    (h : a ^ (4 / 5 : ℝ) ≤ 1 + (4 / 5) * k) :
    a ^ t ≤ 1 + k * t := by
  let b := (5 / 4) * t
  have hb : 0 ≤ b := mul_nonneg (by norm_num) ht
  have ha₀ : 0 ≤ 1 - b := by dsimp only [b]; linarith only [ht']
  have H := (convexOn_rpow_left (b := a) ha).2
    (mem_univ (0 : ℝ)) (mem_univ (4 / 5 : ℝ)) ha₀ hb (sub_add_cancel 1 b)
  have hE : (1 - b) * 0 + b * (4 / 5) = t := by dsimp only [b]; ring
  simp only [smul_eq_mul, hE, Real.rpow_zero, mul_one] at H
  have hP := mul_le_mul_of_nonneg_left h hb
  dsimp only [b] at H hP
  nlinarith only [H, hP]

private theorem reference_derivative {p : ℝ} :
    HasDerivAt zetaCurvatureReference
      (4 ^ (-p) * (-(Real.log 4) ^ 3 +
        2 ^ (p - 1) * (Real.log 2) ^ 2 * (3 - p * Real.log 2) +
        (1 / 3) * (4 / 3) ^ p * (Real.log 3) ^ 2 * (3 - p * Real.log 3) +
        (Real.log 4) ^ 2 / 8 * (3 - p * Real.log 4))) p := by
  have hpow (a : ℝ) (ha : 0 < a) (k : ℝ) :
      HasDerivAt (fun p => a ^ (-(p + k))) (a ^ (-(p + k)) * (-Real.log a)) p := by
    simp_rw [Real.rpow_def_of_pos ha]
    convert (((hasDerivAt_id p).add_const k).neg.const_mul (Real.log a)).exp using 1
    simp only [Pi.neg_apply, id_eq]
    ring
  have hf (a : ℝ) (ha : 0 < a) : HasDerivAt (fun p => zetaCurvature p a)
      (a ^ (-(p + 1)) * (Real.log a) ^ 2 * (3 - p * Real.log a)) p := by
    convert ((hpow a ha 1).mul_const (Real.log a)).mul
      (((hasDerivAt_id p).mul_const (Real.log a)).sub_const 2) using 1
    simp only [id_eq]
    ring
  have hg := ((hpow 4 (by norm_num) 0).mul_const ((Real.log 4) ^ 2)).add
    (hf 2 (by norm_num)) |>.add (hf 3 (by norm_num)) |>.add ((hf 4 (by norm_num)).const_mul (1 / 2))
  have hX (a : ℝ) (ha : 0 < a) :
      a ^ (-(p + 1)) = 4 ^ (-p) * ((4 / a) ^ p / a) := by
    rw [show -(p + 1) = -p - 1 by ring, Real.rpow_sub_one ha.ne',
      Real.div_rpow (by norm_num : (0 : ℝ) ≤ 4) ha.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4),
      Real.rpow_neg ha.le]
    field_simp [ha.ne', (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) p).ne',
      (Real.rpow_pos_of_pos ha p).ne']
  have h2 : (2 : ℝ) ^ p / 2 = 2 ^ (p - 1) := (Real.rpow_sub_one (by norm_num : (2 : ℝ) ≠ 0) p).symm
  convert hg using 1
  · funext q
    simp only [zetaCurvatureReference, zetaCurvaturePrimitive, neg_neg, add_zero, Pi.add_apply]
  · simp only [add_zero]
    rw [hX 2 (by norm_num), hX 3 (by norm_num), hX 4 (by norm_num)]
    norm_num
    rw [h2]
    ring

private theorem referenceDerivative_neg {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    -(Real.log 4) ^ 3 +
        2 ^ (p - 1) * (Real.log 2) ^ 2 * (3 - p * Real.log 2) +
        (1 / 3) * (4 / 3) ^ p * (Real.log 3) ^ 2 * (3 - p * Real.log 3) +
        (Real.log 4) ^ 2 / 8 * (3 - p * Real.log 4) < 0 := by
  let t := p - 1
  let l := Real.log 2
  let m := Real.log 3
  let n := Real.log 4
  have ht : 0 ≤ t := sub_nonneg.mpr hp
  have ht' : t ≤ 4 / 5 := by dsimp only [t]; linarith only [hP]
  have hp₀ : 0 ≤ p := by linarith only [hp]
  have hl : 693 / 1000 < l := by dsimp only [l]; linarith only [Real.log_two_gt_d9]
  have hl' : l < 694 / 1000 := by dsimp only [l]; linarith only [Real.log_two_lt_d9]
  have hm : 1098 / 1000 < m := log_three_bounds.1
  have hm' : m < 1099 / 1000 := log_three_bounds.2
  have hn : 1386 / 1000 < n := by change _ < Real.log 4; rw [log_four_eq]; linarith only [hl]
  have hn' : n < 1388 / 1000 := by change Real.log 4 < _; rw [log_four_eq]; linarith only [hl']
  have hl₂ : l ^ 2 ≤ 482 / 1000 := by
    have h := pow_le_pow_left₀ (by linarith only [hl] : 0 ≤ l) hl'.le 2
    linarith only [h]
  have hm₂ : m ^ 2 ≤ 1208 / 1000 := by
    have h := pow_le_pow_left₀ (by linarith only [hm] : 0 ≤ m) hm'.le 2
    linarith only [h]
  have hn₂ : n ^ 2 / 8 ≤ 240818 / 1000000 := by
    have h := pow_le_pow_left₀ (by linarith only [hn] : 0 ≤ n) hn'.le 2
    linarith only [h]
  have hn₃ : 266 / 100 < n ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1386 / 1000) hn.le 3
    linarith only [h]
  have hA : (2 : ℝ) ^ t ≤ 1 + (928 / 1000) * t := by
    apply exp_chord (by norm_num) ht ht'
    apply (Real.rpow_le_rpow_iff (by positivity) (by positivity) (z := (5 : ℝ)) (by norm_num)).mp
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hB₀ : (4 / 3 : ℝ) ^ t ≤ 1 + (324 / 1000) * t := by
    apply exp_chord (by norm_num) ht ht'
    apply (Real.rpow_le_rpow_iff (by positivity) (by positivity) (z := (5 : ℝ)) (by norm_num)).mp
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4 / 3)]
    norm_num
  have hB : (4 / 3 : ℝ) ^ p ≤ (4 / 3) * (1 + (324 / 1000) * t) := by
    calc
      _ = (4 / 3 : ℝ) * (4 / 3 : ℝ) ^ t := by
        have h := Real.rpow_add (by norm_num : (0 : ℝ) < 4 / 3) (1 : ℝ) t
        simpa only [Real.rpow_one, show (1 : ℝ) + t = p by dsimp only [t]; ring] using h
      _ ≤ _ := mul_le_mul_of_nonneg_left hB₀ (by norm_num)
  have hL : 3 - p * l ≤ 2307 / 1000 - (693 / 1000) * t := by
    have h := mul_le_mul_of_nonneg_left hl.le hp₀
    dsimp only [t]; linarith only [h]
  have hM : 3 - p * m ≤ 1902 / 1000 - (1098 / 1000) * t := by
    have h := mul_le_mul_of_nonneg_left hm.le hp₀
    dsimp only [t]; linarith only [h]
  have hN : 3 - p * n ≤ 1614 / 1000 - (1386 / 1000) * t := by
    have h := mul_le_mul_of_nonneg_left hn.le hp₀
    dsimp only [t]; linarith only [h]
  have hL₀ : 0 ≤ 3 - p * l := by
    have h := mul_le_mul hP hl'.le (by linarith only [hl]) (by norm_num)
    linarith only [h]
  have hM₀ : 0 ≤ 3 - p * m := by
    have h := mul_le_mul hP hm'.le (by linarith only [hm]) (by norm_num)
    linarith only [h]
  have hN₀ : 0 ≤ 3 - p * n := by
    have h := mul_le_mul hP hn'.le (by linarith only [hn]) (by norm_num)
    linarith only [h]
  have h₁ := mul_le_mul (mul_le_mul hA hl₂ (sq_nonneg l) (by positivity)) hL hL₀
    (by positivity : 0 ≤ (1 + (928 / 1000) * t) * (482 / 1000))
  have h₂ := mul_le_mul_of_nonneg_left
    (mul_le_mul (mul_le_mul hB hm₂ (sq_nonneg m) (by positivity)) hM hM₀
      (by positivity : 0 ≤ (4 / 3) * (1 + (324 / 1000) * t) * (1208 / 1000)))
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have h₃ := mul_le_mul hn₂ hN hN₀ (by norm_num : (0 : ℝ) ≤ 240818 / 1000000)
  change -n ^ 3 + 2 ^ t * l ^ 2 * (3 - p * l) + (1 / 3) * (4 / 3) ^ p * m ^ 2 *
    (3 - p * m) + n ^ 2 / 8 * (3 - p * n) < 0
  nlinarith only [h₁, h₂, h₃, hn₃, ht', sq_nonneg t]

private theorem reference_one_lt : zetaCurvatureReference 1 < 119 / 1000 := by
  let l := Real.log 2
  let m := Real.log 3
  have hl : 693 / 1000 < l := by dsimp only [l]; linarith only [Real.log_two_gt_d9]
  have hl' : l < 694 / 1000 := by dsimp only [l]; linarith only [Real.log_two_lt_d9]
  have hm : 1098 / 1000 < m := log_three_bounds.1
  have hm' : m < 1099 / 1000 := log_three_bounds.2
  have h₁ := mul_nonneg (sub_nonneg.mpr hl'.le) (show 0 ≤ (11 / 8) * (694 / 1000 + l) - 5 / 8 by linarith only [hl])
  have h₂ := mul_nonneg (sub_nonneg.mpr hm'.le) (show 0 ≤ 1099 / 1000 + m - 2 by linarith only [hm])
  unfold zetaCurvatureReference zetaCurvaturePrimitive zetaCurvature
  norm_num [Real.rpow_neg_one]
  rw [log_four_eq]
  change 1 / 4 * (2 * l) ^ 2 + 1 / 4 * l * (l - 2) +
    1 / 9 * m * (m - 2) + (1 / 2) * (1 / 16 * (2 * l) * (2 * l - 2)) < _
  nlinarith only [h₁, h₂]

theorem zetaCurvatureReference_antitone : AntitoneOn zetaCurvatureReference (Icc 1 (9 / 5)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · exact fun x _ => (reference_derivative (p := x)).continuousAt.continuousWithinAt
  · exact fun x _ => (reference_derivative (p := x)).differentiableAt.differentiableWithinAt
  · intro q hq
    have hq' : q ∈ Icc (1 : ℝ) (9 / 5) := interior_subset hq
    rw [reference_derivative.deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (by norm_num) _) (referenceDerivative_neg hq'.1 hq'.2).le
theorem zetaCurvatureReference_lt {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    zetaCurvatureReference p < 119 / 1000 := by
  exact (zetaCurvatureReference_antitone (show (1 : ℝ) ∈ Icc 1 (9 / 5) by constructor <;> norm_num) ⟨hp, hP⟩ hp).trans_lt reference_one_lt


theorem zetaCurvatureReference_gt {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    2 / 25 < zetaCurvatureReference p := by
  have hL (b v : ℝ) (k : ℕ) (hb : 0 < b) (hv : 0 ≤ v) (h : v ^ 5 < (b ^ k)⁻¹) :
      v < b ^ (-(k : ℝ) / 5) := by
    apply (Real.rpow_lt_rpow_iff hv (Real.rpow_nonneg hb.le _) (z := (5 : ℝ)) (by norm_num)).mp
    rw [← Real.rpow_mul hb.le, show -(k : ℝ) / 5 * 5 = -(k : ℝ) by ring,
      Real.rpow_neg hb.le, Real.rpow_natCast, show (5 : ℝ) = (5 : ℕ) by norm_num, Real.rpow_natCast]
    exact h
  have hA : (82469 / 1000000 : ℝ) < (4 : ℝ) ^ (-(9 : ℝ) / 5) :=
    hL 4 _ 9 (by norm_num) (by norm_num) (by norm_num)
  have hB : (2 : ℝ) ^ (-(14 : ℝ) / 5) < 143588 / 1000000 :=
    fifth_rpow_upper (k := 14) (by norm_num) (by norm_num) (by norm_num)
  have hC : (3 : ℝ) ^ (-(14 : ℝ) / 5) < 46139 / 1000000 :=
    fifth_rpow_upper (k := 14) (by norm_num) (by norm_num) (by norm_num)
  have hD : (1386 / 1000 : ℝ) < Real.log 4 := by rw [log_four_eq]; linarith only [Real.log_two_gt_d9]
  have hL₂ : (693 / 1000 : ℝ) < Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hU₂ : Real.log 2 < 694 / 1000 := by linarith only [Real.log_two_lt_d9]
  have hI : 1584 / 10000 < -zetaCurvaturePrimitive (9 / 5) 4 := by
    unfold zetaCurvaturePrimitive
    rw [neg_neg,← neg_div]
    have hE := mul_le_mul hA.le (pow_le_pow_left₀ (by norm_num) hD.le 2)
      (by positivity : 0 ≤ (1386 / 1000 : ℝ) ^ 2) (Real.rpow_nonneg (by norm_num) _)
    linarith only [hE]
  have hLower (b l u c e : ℝ) (hb : 0 < b) (hl : 0 ≤ l) (hlo : l ≤ Real.log b) (hhi : Real.log b ≤ u)
      (hcu : b ^ (-(14 : ℝ) / 5) ≤ c) (hc : 0 ≤ c) (ht₀ : 0 ≤ 2 - (9 / 5) * l) (he : c * u * (2 - (9 / 5) * l) < e) :
      -e < zetaCurvature (9 / 5) b := by
    have hLog : 0 ≤ Real.log b := hl.trans hlo
    have hP := mul_le_mul hcu hhi hLog hc
    have hQ : -(b ^ (-(14 : ℝ) / 5) * Real.log b) * ((9 / 5) * Real.log b - 2) ≤
        c * u * (2 - (9 / 5) * l) := by
      by_cases ht : 0 ≤ 2 - (9 / 5) * Real.log b
      · have hE := mul_le_mul hP (show 2 - (9 / 5) * Real.log b ≤ 2 - (9 / 5) * l by linarith only [hlo])
          ht (mul_nonneg hc (hLog.trans hhi))
        nlinarith only [hE]
      · have hNonneg := mul_nonneg (mul_nonneg hc (hLog.trans hhi)) ht₀
        have hNonpos := mul_nonpos_of_nonneg_of_nonpos
          (mul_nonneg (Real.rpow_nonneg hb.le (-(14 : ℝ) / 5)) hLog)
          (le_of_not_ge ht)
        nlinarith only [hNonneg,hNonpos]
    unfold zetaCurvature
    rw [show (9 / 5 : ℝ) + 1 = 14 / 5 by norm_num,← neg_div]
    linarith only [hQ,he]
  have hL2 := hLower 2 (693 / 1000) (694 / 1000) (143588 / 1000000) (751 / 10000)
    (by norm_num) (by norm_num) hL₂.le hU₂.le hB.le (by norm_num) (by norm_num) (by norm_num)
  have hL3 := hLower 3 (1098 / 1000) (1099 / 1000) (46139 / 1000000) (122 / 100000)
    (by norm_num) (by norm_num) log_three_bounds.1.le log_three_bounds.2.le hC.le (by norm_num) (by norm_num) (by norm_num)
  have hL4 : 0 < zetaCurvature (9 / 5) 4 := by
    unfold zetaCurvature
    exact mul_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (by linarith only [hD])) (by linarith only [hD])
  have hEnd : 2 / 25 < zetaCurvatureReference (9 / 5) := by
    unfold zetaCurvatureReference
    linarith only [hI,hL2,hL3,hL4]
  exact hEnd.trans_le (zetaCurvatureReference_antitone ⟨hp,hP⟩
    (show (9 / 5 : ℝ) ∈ Icc 1 (9 / 5) by constructor <;> norm_num) hP)

end ACS12.GammaMeasure

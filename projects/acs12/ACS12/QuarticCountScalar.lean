import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Separate concavity and the four corners of the quartic count margin. -/
namespace ACS12.HighCurrent

open Set

noncomputable section

def quarticCountConstant : ℝ := Real.sqrt (7 / 4) * (7 / 10 : ℝ) ^ (5 / 4 : ℝ)

private theorem quarticCountConstant_fourth :
    quarticCountConstant ^ 4 = (7 / 4 : ℝ) ^ 2 * (7 / 10 : ℝ) ^ 5 := by
  have hSqrt : Real.sqrt (7 / 4 : ℝ) ^ 4 = (7 / 4 : ℝ) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, Real.sq_sqrt (by norm_num)]
  unfold quarticCountConstant
  rw [mul_pow, hSqrt, ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 7 / 10)]
  norm_num

private theorem quarticCountConstant_nonneg : 0 ≤ quarticCountConstant := by
  unfold quarticCountConstant
  positivity

theorem quarticCountConstant_lower : (847 / 1000 : ℝ) < quarticCountConstant := by
  apply (pow_lt_pow_iff_left₀ (by norm_num) quarticCountConstant_nonneg
    (by decide : (4 : ℕ) ≠ 0)).mp
  norm_num [quarticCountConstant_fourth]

theorem quarticCountConstant_upper : quarticCountConstant < 8471 / 10000 := by
  apply (pow_lt_pow_iff_left₀ quarticCountConstant_nonneg (by norm_num)
    (by decide : (4 : ℕ) ≠ 0)).mp
  norm_num [quarticCountConstant_fourth]

private theorem quarter_fourth {b : ℝ} (hb : 0 ≤ b) : (b ^ (1 / 4 : ℝ)) ^ 4 = b := by
  rw [← Real.rpow_mul_natCast hb, show (1 / 4 : ℝ) * (4 : ℕ) = 1 by norm_num, Real.rpow_one]

private theorem lt_quarter {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 4 < b) :
    a < b ^ (1 / 4 : ℝ) := by
  apply (pow_lt_pow_iff_left₀ ha (Real.rpow_nonneg hb _) (by decide : (4 : ℕ) ≠ 0)).mp
  rwa [quarter_fourth hb]

theorem quarticCount_twoThirds_quarter_lower : (903 / 1000 : ℝ) < (2 / 3 : ℝ) ^ (1 / 4 : ℝ) := by
  exact lt_quarter (by norm_num) (by norm_num) (by norm_num)

theorem quarticCount_twoThirds_quarter_upper : (2 / 3 : ℝ) ^ (1 / 4 : ℝ) < 904 / 1000 := by
  have hb : (0 : ℝ) ≤ 2 / 3 := by norm_num
  apply (pow_lt_pow_iff_left₀ (Real.rpow_nonneg hb _) (by norm_num)
    (by decide : (4 : ℕ) ≠ 0)).mp
  norm_num [quarter_fourth hb]

private def countLimit : ℝ := 691 / 2000

private def countMargin (r z : ℝ) : ℝ :=
  quarticCountConstant * (1 - (2 : ℝ) ^ r * z ^ 2) ^ (5 / 4 : ℝ) -
    (3 / 4) * (2 / 3 : ℝ) ^ (r / 4) * Real.sqrt (1 - z) - (1 / 16 - 5 * z ^ 2 / 64)

private theorem countPower_two {r : ℝ} (hr : r ∈ Icc 0 1) :
    (1 : ℝ) ≤ (2 : ℝ) ^ r ∧ (2 : ℝ) ^ r ≤ 2 := by
  constructor
  · simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le one_le_two hr.1
  · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le one_le_two hr.2

private theorem count_product_bound {B z : ℝ}
    (hB : B ≤ 2) (hz : z ∈ Icc 0 countLimit) : B * z ^ 2 ≤ 2 * countLimit ^ 2 := by
  have hz2 := pow_le_pow_left₀ hz.1 hz.2 2
  calc
    B * z ^ 2 ≤ 2 * z ^ 2 := mul_le_mul_of_nonneg_right hB (sq_nonneg _)
    _ ≤ 2 * countLimit ^ 2 := mul_le_mul_of_nonneg_left hz2 zero_le_two

private theorem quarter_shift {b : ℝ} (hb : 0 < b) :
    b ^ (1 / 4 : ℝ) = b ^ (-3 / 4 : ℝ) * b := by
  rw [← Real.rpow_add_one hb.ne', show (-3 / 4 : ℝ) + 1 = 1 / 4 by norm_num]

private theorem countMargin_concave_r {z : ℝ} (hz : z ∈ Icc 0 countLimit) :
    ConcaveOn ℝ (Icc 0 1) (fun r => countMargin r z) := by
  let a (r : ℝ) := (2 : ℝ) ^ r * z ^ 2
  let e (r : ℝ) := (3 / 4) * (2 / 3 : ℝ) ^ (r / 4) * Real.sqrt (1 - z)
  let L := Real.log 2
  let M := Real.log (2 / 3) / 4
  let D (r : ℝ) := -quarticCountConstant * (5 / 4) * L * ((1 - a r) ^ (1 / 4 : ℝ) * a r) - M * e r
  let DD (r : ℝ) := quarticCountConstant * (5 / 4) * L ^ 2 *
    (1 - a r) ^ (-3 / 4 : ℝ) * a r * ((5 / 4) * a r - 1) - M ^ 2 * e r
  have ha_nonneg (r : ℝ) : 0 ≤ a r := by
    unfold a
    positivity
  have ha_bound (r : ℝ) (hr : r ∈ Icc 0 1) : a r ≤ 2 * countLimit ^ 2 :=
    count_product_bound (countPower_two hr).2 hz
  have hab (r : ℝ) (hr : r ∈ Icc 0 1) : 0 < 1 - a r := by
    have h := ha_bound r hr
    norm_num [countLimit] at h
    linarith
  have ha (r : ℝ) : HasDerivAt a (L * a r) r := by
    unfold a L
    convert (((hasDerivAt_id r).const_rpow (by norm_num : (0 : ℝ) < 2)).mul_const (z ^ 2)) using 1
    simp only [id_eq, mul_one]
    ring
  have he (r : ℝ) : HasDerivAt e (M * e r) r := by
    unfold e M
    have h := ((hasDerivAt_id r).div_const 4).const_rpow (by norm_num : (0 : ℝ) < 2 / 3)
    convert ((h.const_mul (3 / 4)).mul_const (Real.sqrt (1 - z))) using 1
    simp only [id_eq]
    ring
  have hD (r : ℝ) (hr : r ∈ Icc 0 1) : HasDerivAt (fun r => countMargin r z) (D r) r := by
    have hb := ((ha r).const_sub 1).rpow_const (p := 5 / 4) (Or.inl (hab r hr).ne')
    unfold D countMargin
    convert (((hb.const_mul quarticCountConstant).sub (he r)).sub_const
      (1 / 16 - 5 * z ^ 2 / 64)) using 1
    rw [show (5 / 4 : ℝ) - 1 = 1 / 4 by norm_num]
    ring
  have hDD (r : ℝ) (hr : r ∈ Icc 0 1) : HasDerivAt D (DD r) r := by
    have hb := ((ha r).const_sub 1).rpow_const (p := 1 / 4) (Or.inl (hab r hr).ne')
    unfold D DD
    convert (((hb.mul (ha r)).const_mul (-quarticCountConstant * (5 / 4) * L)).sub
      ((he r).const_mul M)) using 1
    rw [show (1 / 4 : ℝ) - 1 = -3 / 4 by norm_num, quarter_shift (hab r hr)]
    ring
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 1) (f' := D) (f'' := DD)
  · exact fun r hr => (hD r hr).continuousAt.continuousWithinAt
  · exact fun r hr => (hD r (interior_subset hr)).hasDerivWithinAt
  · exact fun r hr => (hDD r (interior_subset hr)).hasDerivWithinAt
  · intro r hr
    have hr' := interior_subset hr
    have h := ha_bound r hr'
    norm_num [countLimit] at h
    have hsign : (5 / 4) * a r - 1 ≤ 0 := by linarith
    have he_nonneg : 0 ≤ e r := by unfold e; positivity
    have hbase := Real.rpow_nonneg (hab r hr').le (-3 / 4)
    have hcoef : 0 ≤ quarticCountConstant * (5 / 4) * L ^ 2 *
        (1 - a r) ^ (-3 / 4 : ℝ) * a r :=
      mul_nonneg (mul_nonneg
        (mul_nonneg (mul_nonneg quarticCountConstant_nonneg (by norm_num)) (sq_nonneg L))
        hbase) (ha_nonneg r)
    exact sub_nonpos.mpr
      ((mul_nonpos_of_nonneg_of_nonpos hcoef hsign).trans
        (mul_nonneg (sq_nonneg M) he_nonneg))

private theorem count_sqrt_curvature_bound {z : ℝ} (hz : z ∈ Icc 0 countLimit) :
    (1 - z) ^ (-3 / 2 : ℝ) ≤ 2 := by
  have hb : 0 < 1 - z := by
    have hh := hz.2
    norm_num [countLimit] at hh
    linarith
  have hhalf : (1 / 2 : ℝ) < (1 - z) ^ (3 / 2 : ℝ) := by
    apply (pow_lt_pow_iff_left₀ (by norm_num) (Real.rpow_nonneg hb.le _) two_ne_zero).mp
    rw [← Real.rpow_mul_natCast hb.le, show (3 / 2 : ℝ) * (2 : ℕ) = (3 : ℕ) by norm_num,
      Real.rpow_natCast]
    have hmono := pow_le_pow_left₀
      (show 0 ≤ 1 - countLimit by norm_num [countLimit])
      (sub_le_sub_left hz.2 1) 3
    exact (show (1 / 2 : ℝ) ^ 2 < (1 - countLimit) ^ 3 by norm_num [countLimit]).trans_le hmono
  rw [show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by norm_num, Real.rpow_neg hb.le]
  rw [inv_eq_one_div, div_le_iff₀ (Real.rpow_pos_of_pos hb _)]
  linarith only [hhalf]

private theorem countMargin_concave_z {r : ℝ} (hr : r ∈ Icc 0 1) :
    ConcaveOn ℝ (Icc 0 countLimit) (countMargin r) := by
  let B := (2 : ℝ) ^ r
  let A := (3 / 4) * (2 / 3 : ℝ) ^ (r / 4)
  let a (z : ℝ) := 1 - B * z ^ 2
  let b (z : ℝ) := 1 - z
  let D (z : ℝ) := -2 * quarticCountConstant * (5 / 4) * B * (a z ^ (1 / 4 : ℝ) * z) +
    (A / 2) * b z ^ (-1 / 2 : ℝ) + (5 / 32) * z
  let DD (z : ℝ) := -(2 * quarticCountConstant * (5 / 4) * B * a z ^ (-3 / 4 : ℝ) *
    (1 - (3 / 2) * B * z ^ 2)) + (A / 4) * b z ^ (-3 / 2 : ℝ) + 5 / 32
  obtain ⟨hB1, hB2⟩ := countPower_two hr
  have hB1' : 1 ≤ B := hB1
  have hB0 : 0 ≤ B := zero_le_one.trans hB1'
  have hA0 : 0 ≤ A := by unfold A; positivity
  have hA1 : A ≤ 3 / 4 := by
    have h := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 2 / 3)
      (by norm_num) (show (0 : ℝ) ≤ r / 4 by exact div_nonneg hr.1 (by norm_num))
    rw [Real.rpow_zero] at h
    unfold A
    simpa using mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 3 / 4)
  have ha_bound (z : ℝ) (hz : z ∈ Icc 0 countLimit) : B * z ^ 2 ≤ 2 * countLimit ^ 2 :=
    count_product_bound hB2 hz
  have ha_pos (z : ℝ) (hz : z ∈ Icc 0 countLimit) : 0 < a z := by
    have h := ha_bound z hz
    norm_num [countLimit] at h
    unfold a
    linarith
  have hb_pos (z : ℝ) (hz : z ∈ Icc 0 countLimit) : 0 < b z := by
    have h := hz.2
    norm_num [countLimit] at h
    unfold b
    linarith
  have ha (z : ℝ) : HasDerivAt a (-2 * B * z) z := by
    unfold a
    convert ((hasDerivAt_pow 2 z).const_mul B).const_sub 1 using 1
    norm_num
    ring
  have hb (z : ℝ) : HasDerivAt b (-1) z := (hasDerivAt_id z).const_sub 1
  have hE (z : ℝ) : HasDerivAt (fun z : ℝ => -(1 / 16 - 5 * z ^ 2 / 64)) ((5 / 32) * z) z := by
    convert (((hasDerivAt_pow 2 z).const_mul 5).div_const 64).sub_const (1 / 16) using 1
    · funext y
      ring
    · norm_num
      ring
  have hD (z : ℝ) (hz : z ∈ Icc 0 countLimit) : HasDerivAt (countMargin r) (D z) z := by
    have ha' := (ha z).rpow_const (p := 5 / 4) (Or.inl (ha_pos z hz).ne')
    have hb' := (hb z).rpow_const (p := 1 / 2) (Or.inl (hb_pos z hz).ne')
    unfold D countMargin
    convert (((ha'.const_mul quarticCountConstant).sub (hb'.const_mul A)).add (hE z)) using 1
    · funext y
      unfold a b A B
      simp only [Pi.add_apply, Pi.sub_apply, Real.sqrt_eq_rpow]
      ring
    · rw [show (5 / 4 : ℝ) - 1 = 1 / 4 by norm_num,
        show (1 / 2 : ℝ) - 1 = -1 / 2 by norm_num]
      ring
  have hDD (z : ℝ) (hz : z ∈ Icc 0 countLimit) : HasDerivAt D (DD z) z := by
    have ha' := (ha z).rpow_const (p := 1 / 4) (Or.inl (ha_pos z hz).ne')
    have hb' := (hb z).rpow_const (p := -1 / 2) (Or.inl (hb_pos z hz).ne')
    unfold D DD
    convert ((((ha'.mul (hasDerivAt_id z)).const_mul (-2 * quarticCountConstant * (5 / 4) * B)).add
      (hb'.const_mul (A / 2))).add ((hasDerivAt_id z).const_mul (5 / 32))) using 1
    simp only [id_eq]
    rw [show (1 / 4 : ℝ) - 1 = -3 / 4 by norm_num,
      show (-1 / 2 : ℝ) - 1 = -3 / 2 by norm_num, quarter_shift (ha_pos z hz)]
    dsimp only [a]
    ring
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 countLimit) (f' := D) (f'' := DD)
  · exact fun z hz => (hD z hz).continuousAt.continuousWithinAt
  · exact fun z hz => (hD z (interior_subset hz)).hasDerivWithinAt
  · exact fun z hz => (hDD z (interior_subset hz)).hasDerivWithinAt
  · intro z hz
    have hz' := interior_subset hz
    have ha_le : a z ≤ 1 := sub_le_self _ (mul_nonneg hB0 (sq_nonneg z))
    have ha_pow : 1 ≤ a z ^ (-3 / 4 : ℝ) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos (ha_pos z hz') ha_le (by norm_num)
    have hG : (5 / 8 : ℝ) ≤ 1 - (3 / 2) * B * z ^ 2 := by
      have h := ha_bound z hz'
      norm_num [countLimit] at h
      linarith
    have hFirst : (2 : ℝ) * (847 / 1000) * (5 / 4) * 1 * 1 * (5 / 8) ≤
        2 * quarticCountConstant * (5 / 4) * B * a z ^ (-3 / 4 : ℝ) *
          (1 - (3 / 2) * B * z ^ 2) := by
      have hc := quarticCountConstant_nonneg
      have hcLower := quarticCountConstant_lower.le
      have ha0 := zero_le_one.trans ha_pow
      have hG0 := (by norm_num : (0 : ℝ) ≤ 5 / 8).trans hG
      gcongr
    have hSecond : (A / 4) * b z ^ (-3 / 2 : ℝ) ≤ (3 / 4) / 4 * 2 := by
      have hb_pow : b z ^ (-3 / 2 : ℝ) ≤ 2 := count_sqrt_curvature_bound hz'
      have hb_pow0 : 0 ≤ b z ^ (-3 / 2 : ℝ) := Real.rpow_nonneg (hb_pos z hz').le _
      gcongr
    dsimp only [DD]
    linarith only [hFirst, hSecond]

private theorem count_corner_lower {B t tUpper rootLower : ℝ}
    (hb : 0 ≤ 1 - B * countLimit ^ 2) (ht : 0 ≤ t) (htU : t ≤ tUpper)
    (hroot : rootLower ≤ (1 - B * countLimit ^ 2) ^ (1 / 4 : ℝ))
    (hroot0 : 0 ≤ rootLower) :
    (847 / 1000 : ℝ) * ((1 - B * countLimit ^ 2) * rootLower) - (3 / 4) * tUpper * (8091 / 10000) -
        (1 / 16 - 5 * countLimit ^ 2 / 64) ≤
      quarticCountConstant * (1 - B * countLimit ^ 2) ^ (5 / 4 : ℝ) -
        (3 / 4) * t * Real.sqrt (1 - countLimit) - (1 / 16 - 5 * countLimit ^ 2 / 64) := by
  have hsqrt : Real.sqrt (1 - countLimit) ≤ 8091 / 10000 := by
    have hb' : 0 ≤ 1 - countLimit := by norm_num [countLimit]
    apply (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) (by norm_num) two_ne_zero).mp
    rw [Real.sq_sqrt hb']
    norm_num [countLimit]
  have heq : (1 - B * countLimit ^ 2) ^ (5 / 4 : ℝ) =
      (1 - B * countLimit ^ 2) * (1 - B * countLimit ^ 2) ^ (1 / 4 : ℝ) := by
    rw [show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num,
      Real.rpow_add' hb (by norm_num), Real.rpow_one]
  rw [heq]
  have hRoot := mul_le_mul_of_nonneg_left hroot hb
  have hLower := mul_le_mul quarticCountConstant_lower.le hRoot
    (mul_nonneg hb hroot0) quarticCountConstant_nonneg
  have hUpper := mul_le_mul
    (mul_le_mul_of_nonneg_left htU (by norm_num : (0 : ℝ) ≤ 3 / 4)) hsqrt
    (Real.sqrt_nonneg _) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) (ht.trans htU))
  linarith only [hLower, hUpper]

private theorem count_corners :
    (1 / 2500 : ℝ) < countMargin 0 0 ∧ (1 / 2500 : ℝ) < countMargin 1 0 ∧
    (1 / 2500 : ℝ) < countMargin 0 countLimit ∧ (1 / 2500 : ℝ) < countMargin 1 countLimit := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [countMargin]
    linarith only [quarticCountConstant_lower]
  · norm_num [countMargin]
    linarith only [quarticCountConstant_lower, quarticCount_twoThirds_quarter_upper]
  · have h := count_corner_lower (B := 1) (t := 1) (tUpper := 1) (rootLower := 968 / 1000)
      (by norm_num [countLimit]) (by norm_num) le_rfl
      (lt_quarter (by norm_num) (by norm_num [countLimit]) (by norm_num [countLimit])).le (by norm_num)
    simp only [one_mul, mul_one] at h
    simp only [countMargin, Real.rpow_zero, zero_div, one_mul, mul_one]
    exact (by norm_num [countLimit] : (1 / 2500 : ℝ) <
      (847 / 1000) * ((1 - countLimit ^ 2) * (968 / 1000)) - (3 / 4) * (8091 / 10000) -
        (1 / 16 - 5 * countLimit ^ 2 / 64)).trans_le h
  · have h := count_corner_lower (B := 2) (t := (2 / 3 : ℝ) ^ (1 / 4 : ℝ))
      (tUpper := 904 / 1000) (rootLower := 934 / 1000)
      (by norm_num [countLimit]) (by positivity) quarticCount_twoThirds_quarter_upper.le
      (lt_quarter (by norm_num) (by norm_num [countLimit]) (by norm_num [countLimit])).le (by norm_num)
    simp only [countMargin, Real.rpow_one]
    exact (by norm_num [countLimit] : (1 / 2500 : ℝ) <
      (847 / 1000) * ((1 - 2 * countLimit ^ 2) * (934 / 1000)) -
        (3 / 4) * (904 / 1000) * (8091 / 10000) - (1 / 16 - 5 * countLimit ^ 2 / 64)).trans_le h

/-- The count comparison is positive on the full rectangle required by the quartic proof. -/
theorem quarticCount_scalar_pos {r z : ℝ} (hr : r ∈ Icc 0 1) (hz : z ∈ Icc 0 (691 / 2000)) :
    0 < quarticCountConstant * (1 - (2 : ℝ) ^ r * z ^ 2) ^ (5 / 4 : ℝ) -
      (3 / 4) * (2 / 3 : ℝ) ^ (r / 4) * Real.sqrt (1 - z) - (1 / 16 - 5 * z ^ 2 / 64) := by
  have hz' : z ∈ Icc 0 countLimit := hz
  have h0 : (0 : ℝ) ∈ Icc 0 countLimit := ⟨le_rfl, by norm_num [countLimit]⟩
  have hd : countLimit ∈ Icc 0 countLimit := ⟨by norm_num [countLimit], le_rfl⟩
  have hr0 : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have hr1 : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨h00, h10, h0d, h1d⟩ := count_corners
  have h0z := (lt_min h00 h0d).trans_le
    ((countMargin_concave_z hr0).min_le_of_mem_Icc h0 hd hz')
  have h1z := (lt_min h10 h1d).trans_le
    ((countMargin_concave_z hr1).min_le_of_mem_Icc h0 hd hz')
  have hrz := (lt_min h0z h1z).trans_le
    ((countMargin_concave_r hz').min_le_of_mem_Icc hr0 hr1 hr)
  exact (by norm_num : (0 : ℝ) < 1 / 2500).trans hrz

end

end ACS12.HighCurrent

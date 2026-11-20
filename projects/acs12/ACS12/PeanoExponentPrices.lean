import ACS12.PureAdjacentArc
import Mathlib.Analysis.Complex.Exponential

/-! Exact frequency bounds for the adverse exponent curvature of the Peano moments. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN Set
open scoped BigOperators

theorem mul_exp_neg_le_inv_e (x : ℝ) : x * Real.exp (-x) ≤ Real.exp (-1) := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (x - 1)) (Real.exp_pos (-x)).le
  rw [← Real.exp_add, show x - 1 + -x = -1 by ring,
    show x - 1 + 1 = x by ring] at h
  exact h

private theorem sq_mul_exp_neg_le (x : ℝ) (hx : 0 ≤ x) :
    x ^ 2 * Real.exp (-x) ≤ 4 * Real.exp (-2) := by
  have h := pow_le_pow_left₀ (mul_nonneg (by positivity : 0 ≤ x / 2) (Real.exp_pos _).le)
    (mul_exp_neg_le_inv_e (x / 2)) 2
  rw [mul_pow, pow_two (Real.exp (-(x / 2))), ← Real.exp_add,
    show -(x / 2) + -(x / 2) = -x by ring,
    pow_two (Real.exp (-1)), ← Real.exp_add, show (-1 : ℝ) + -1 = -2 by norm_num] at h
  nlinarith only [h]

theorem lower_cut_value_le {p y : ℝ} (hp : 1 ≤ p) (hy : 0 ≤ y) :
    Real.exp (-(p + 1) * y) * y * (2 - p * y) ≤ 3 / 10 := by
  rcases le_total (2 - p * y) 0 with h | h
  · exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) h).trans (by norm_num)
  · have hy₂ : y ≤ 2 := by
      have h' := mul_le_mul_of_nonneg_right hp hy
      linarith only [h, h']
    have hA : y * (2 - p * y) ≤ 2 * y - y ^ 2 := by
      have h' := mul_le_mul_of_nonneg_right hp (sq_nonneg y)
      nlinarith only [h']
    have hExp : Real.exp (-(p + 1) * y) ≤ Real.exp (-2 * y) := Real.exp_le_exp.mpr (by
      nlinarith only [mul_le_mul_of_nonneg_right hp hy])
    have hB := mul_le_mul hExp hA (mul_nonneg hy h) (Real.exp_pos _).le
    have hE : (2 * y - y ^ 2) ≤ (3 / 10) * Real.exp (2 * y) := by
      have hP := Real.sum_le_exp_of_nonneg (x := 2 * y) (by positivity) 4
      norm_num [Finset.sum_range_succ] at hP
      have hN : 0 ≤ (3 / 10) - (7 / 5) * y + (8 / 5) * y ^ 2 + (2 / 5) * y ^ 3 := by
        rcases le_total y (1 / 4) with h' | h'
        · have hQ := mul_nonneg (sub_nonneg.mpr h') (show 0 ≤ 1 - (8 / 5) * y by linarith)
          nlinarith only [hQ, pow_nonneg hy 3]
        · have hQ := mul_le_mul_of_nonneg_left h' (by positivity : 0 ≤ y ^ 2)
          have hR := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 4) h' 3
          nlinarith only [hQ, hR, sq_nonneg (y - 7 / 16)]
      linarith only [hP, hN]
    have hC := mul_le_mul_of_nonneg_left hE (Real.exp_pos (-2 * y)).le
    have he : Real.exp (-2 * y) * Real.exp (2 * y) = 1 := by
      rw [← Real.exp_add, show -2 * y + 2 * y = 0 by ring, Real.exp_zero]
    calc
      _ = Real.exp (-(p + 1) * y) * (y * (2 - p * y)) := by ring
      _ ≤ Real.exp (-2 * y) * (2 * y - y ^ 2) := hB
      _ ≤ _ := hC.trans_eq (by linear_combination (3 / 10 : ℝ) * he)

private theorem exp_neg_one_lt : Real.exp (-1) < 10 / 27 := by
  have h := Real.sum_le_exp_of_nonneg (x := 1) zero_le_one 6
  have hE : (27 / 10 : ℝ) < Real.exp 1 := by norm_num [Finset.sum_range_succ] at h; linarith
  rw [Real.exp_neg, ← one_div]
  exact (div_lt_div_of_pos_left zero_lt_one (by norm_num) hE).trans_eq (by norm_num)

private theorem exp_neg_twentyEight_ninths_lt : Real.exp (-(28 / 9)) < 1 / 22 := by
  have h := Real.sum_le_exp_of_nonneg (x := 28 / 9) (by norm_num) 9
  have hE : (22 : ℝ) < Real.exp (28 / 9) := by norm_num [Finset.sum_range_succ] at h; linarith
  rw [Real.exp_neg, ← one_div]
  exact div_lt_div_of_pos_left zero_lt_one (by norm_num) hE

theorem upper_cut_value_lt {p y : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) (hy : 0 ≤ y) :
    Real.exp (-(p + 1) * y) * y * (p * y - 2) < 1 / 50 := by
  rcases le_total (p * y) 2 with h | h
  · exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr h)).trans_lt (by norm_num)
  · let v := p * y
    let q := p⁻¹
    let q₀ : ℝ := 5 / 9
    let k : ℝ := 14 / 9
    let w := v - 2
    have hp₀ := zero_lt_one.trans_le hp
    have hq : q₀ ≤ q := by
      change (5 / 9 : ℝ) ≤ p⁻¹
      exact (show (5 / 9 : ℝ) = (9 / 5 : ℝ)⁻¹ by norm_num).le.trans (inv_anti₀ hp₀ hP)
    have hv : 2 ≤ v := h
    have hw : 0 ≤ w := sub_nonneg.mpr hv
    have hk : 0 < k := by norm_num [k]
    have hBase : q ≤ q₀ * Real.exp ((q - q₀) * v) := by
      have hE := mul_le_mul_of_nonneg_left (Real.add_one_le_exp ((q - q₀) * v))
        (by norm_num [q₀] : 0 ≤ q₀)
      have hM := mul_le_mul_of_nonneg_left hv (sub_nonneg.mpr hq)
      norm_num [q₀] at hE hM ⊢
      have hQ : 0 ≤ q - 5 / 9 := sub_nonneg.mpr hq
      nlinarith only [hE, hM, hQ]
    have hTilt := mul_le_mul_of_nonneg_right hBase (Real.exp_pos (-(1 + q) * v)).le
    rw [mul_assoc, ← Real.exp_add, show (q - q₀) * v + -(1 + q) * v = -k * v by
      dsimp only [q₀, k]; ring] at hTilt
    have hyEq : y = q * v := by
      dsimp only [q, v]
      rw [← mul_assoc, inv_mul_cancel₀ hp₀.ne', one_mul]
    have hExp : -(p + 1) * y = -(1 + q) * v := by
      dsimp only [q, v]
      field_simp [hp₀.ne']
    have hMajor : Real.exp (-(p + 1) * y) * y * (p * y - 2) ≤
        q₀ * Real.exp (-k * v) * (v * (v - 2)) := by
      rw [hExp, ← show v = p * y from rfl, hyEq]
      calc
        _ = (q * Real.exp (-(1 + q) * v)) * (v * (v - 2)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hTilt (mul_nonneg (by linarith) hw)
    have hVW : v = w + 2 := by dsimp only [w]; ring
    have hE : Real.exp (-k * v) = Real.exp (-2 * k) * Real.exp (-k * w) := by
      rw [← Real.exp_add, hVW]
      congr 1
      ring
    have hU := mul_exp_neg_le_inv_e (k * w)
    have hV := sq_mul_exp_neg_le (k * w) (mul_nonneg hk.le hw)
    have h₁ : w * Real.exp (-k * w) ≤ Real.exp (-1) / k := by
      apply (le_div_iff₀ hk).mpr
      rw [show -(k * w) = -k * w by ring] at hU
      convert hU using 1 <;> ring
    have h₂ : w ^ 2 * Real.exp (-k * w) ≤ 4 * Real.exp (-2) / k ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hk)).mpr
      rw [show -(k * w) = -k * w by ring] at hV
      convert hV using 1 <;> ring
    have hD : Real.exp (-k * w) * (v * (v - 2)) ≤
        2 * Real.exp (-1) / k + 4 * Real.exp (-2) / k ^ 2 := by
      calc
        _ = 2 * (w * Real.exp (-k * w)) + w ^ 2 * Real.exp (-k * w) := by rw [hVW]; ring
        _ ≤ 2 * (Real.exp (-1) / k) + 4 * Real.exp (-2) / k ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_left h₁ zero_le_two) h₂
        _ = _ := by ring
    have hSquare := pow_le_pow_left₀ (Real.exp_pos (-1)).le exp_neg_one_lt.le 2
    rw [pow_two (Real.exp (-1)), ← Real.exp_add, show (-1 : ℝ) + -1 = -2 by norm_num] at hSquare
    have hD' : 2 * Real.exp (-1) / k + 4 * Real.exp (-2) / k ^ 2 ≤ 3 / 4 := by
      norm_num [k] at hSquare ⊢
      linarith only [hSquare, exp_neg_one_lt]
    have hE' : Real.exp (-2 * k) ≤ 1 / 22 := by
      simpa only [k, show -(2 : ℝ) * (14 / 9) = -(28 / 9) by norm_num] using
        exp_neg_twentyEight_ninths_lt.le
    refine hMajor.trans_lt ?_
    rw [hE]
    calc
      _ = (q₀ * Real.exp (-2 * k)) * (Real.exp (-k * w) * (v * (v - 2))) := by ring
      _ ≤ (q₀ * (1 / 22)) * (3 / 4) := mul_le_mul
        (mul_le_mul_of_nonneg_left hE' (by norm_num [q₀])) (hD.trans hD')
        (mul_nonneg (Real.exp_pos _).le (mul_nonneg (by linarith) hw)) (by norm_num [q₀])
      _ < _ := by norm_num [q₀]

end ACS12.GammaMeasure

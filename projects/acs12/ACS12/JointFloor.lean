import ACS12.LawPeanoHead
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! The exact full-ray lower test at the half-gap in P945 G13. -/

namespace ACS12.GammaMeasure

open scoped BigOperators

private def jointFloorPolynomial (t : ℝ) : ℝ :=
  120 + 120 * t - 20 * t ^ 2 - 80 * t ^ 3 + 22 * t ^ 4 + 2 * t ^ 5 + t ^ 6

private theorem jointFloorPolynomial_pos {t : ℝ} (ht : 0 ≤ t) :
    0 < jointFloorPolynomial t := by
  by_cases h₁ : t ≤ 1
  · have h₂ : t ^ 2 ≤ t := by simpa only [pow_two, one_mul] using mul_le_mul_of_nonneg_right h₁ ht
    have h₃ : t ^ 3 ≤ t := by
      rw [pow_succ]
      exact (mul_le_mul_of_nonneg_right h₂ ht).trans (by simpa only [pow_two] using h₂)
    unfold jointFloorPolynomial
    nlinarith only [h₂, h₃, ht, pow_nonneg ht 4, pow_nonneg ht 5, pow_nonneg ht 6]
  by_cases h₂ : t ≤ 2
  · let y := t - 1
    have hy : 0 ≤ y := sub_nonneg.mpr (le_of_not_ge h₁)
    have hy₁ : y ≤ 1 := by dsimp only [y]; linarith
    have hy₂ : y ^ 2 ≤ 1 := by
      rw [sq]
      exact (mul_le_of_le_one_right hy hy₁).trans hy₁
    have hEq : jointFloorPolynomial t =
        165 - 56 * y - 93 * y ^ 2 + 48 * y ^ 3 + 47 * y ^ 4 + 8 * y ^ 5 + y ^ 6 := by
      unfold jointFloorPolynomial
      dsimp only [y]
      ring
    rw [hEq]
    nlinarith only [hy₁, hy₂, pow_nonneg hy 3, pow_nonneg hy 4, pow_nonneg hy 5, pow_nonneg hy 6]
  · let y := t - 2
    have hy : 0 ≤ y := sub_nonneg.mpr (le_of_not_ge h₂)
    have hEq : jointFloorPolynomial t =
        120 + 136 * y + 428 * y ^ 2 + 336 * y ^ 3 + 102 * y ^ 4 + 14 * y ^ 5 + y ^ 6 := by
      unfold jointFloorPolynomial
      dsimp only [y]
      ring
    rw [hEq]
    positivity

theorem jointFloor_brace_pos {t : ℝ} (ht : 0 < t) :
    0 < Real.sinh t / t - Real.exp (-t) - t + 1 / 2 := by
  have hS : 1 + t ^ 2 / 6 + t ^ 4 / 120 ≤ Real.sinh t / t := by
    have hSum := Real.hasSum_sinh t
    have hBound := hSum.summable.sum_le_tsum (Finset.range 3) (fun i _ => by positivity)
    rw [hSum.tsum_eq] at hBound
    norm_num [Finset.sum_range_succ, Nat.factorial] at hBound
    apply (le_div_iff₀ ht).mpr
    nlinarith only [hBound]
  let D := 1 + t + t ^ 2 / 2
  have hD : 0 < D := by dsimp only [D]; positivity
  have he : Real.exp (-t) ≤ 1 / D := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ hD (Real.quadratic_le_exp_of_nonneg ht.le)
  have hP : 1 / D < 3 / 2 - t + t ^ 2 / 6 + t ^ 4 / 120 := by
    apply (div_lt_iff₀ hD).mpr
    have h := jointFloorPolynomial_pos ht.le
    unfold jointFloorPolynomial at h
    dsimp only [D]
    nlinarith only [h]
  linarith only [hS, he, hP]

theorem third_spacing_brace_pos {x : ℝ} (hx : 0 < x) :
    0 < (Real.exp x - 1 - x) / (Real.exp (x / 3) - 1) + 2 - x := by
  let f (t : ℝ) := Real.exp t - (t - 2) * Real.exp (t / 3) - 3
  have hF (t : ℝ) : HasDerivAt f (Real.exp t - (t + 1) * Real.exp (t / 3) / 3) t := by
    have hE := ((hasDerivAt_id t).div_const 3).exp
    have h := ((Real.hasDerivAt_exp t).sub (((hasDerivAt_id t).sub_const 2).mul hE)).sub_const 3
    convert h using 1
    simp only [id_eq, one_mul]
    ring
  have hPos : 0 < f x := by
    apply BoseShape.positive_of_derivative (by norm_num [f]) hF _ hx
    intro t ht
    have h := Real.add_one_le_exp (2 * t / 3)
    have hT : (t + 1) / 3 < Real.exp (2 * t / 3) := by linarith
    have hMul := mul_lt_mul_of_pos_right hT (Real.exp_pos (t / 3))
    rw [← Real.exp_add, show 2 * t / 3 + t / 3 = t by ring] at hMul
    linarith only [hMul]
  have hd := CenteredCircle.AllN.expTail_den_pos (show 0 < x / 3 by positivity)
  have h : x - 2 < (Real.exp x - 1 - x) / (Real.exp (x / 3) - 1) := by
    apply (lt_div_iff₀ hd).mpr
    dsimp only [f] at hPos
    linarith only [hPos]
  linarith only [h]

end ACS12.GammaMeasure


import ACS12.JointBoseBounds
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! The two whole-ray exponential guards for the joint return G18 and G21. -/
namespace ACS12.GammaMeasure

open CenteredCircle.AllN Polynomial Set
open BoseShape (expQuad expQuad_deriv)

private theorem derivativeChain_pos (N : ℕ) (F : ℕ → ℝ → ℝ)
    (h0 : ∀ j < N, F j 0 = 0)
    (hD : ∀ j < N, ∀ x, HasDerivAt (F j) (F (j + 1) x) x)
    (hN : ∀ x > 0, 0 < F N x) :
    ∀ x > 0, 0 < F 0 x := by
  induction N generalizing F with
  | zero => exact hN
  | succ N ih =>
    have hNext : ∀ x > 0, 0 < F 1 x :=
      ih (fun j => F (j + 1))
        (fun j hj => h0 (j + 1) (Nat.succ_lt_succ hj))
        (fun j hj => hD (j + 1) (Nat.succ_lt_succ hj)) hN
    exact fun x hx => BoseShape.positive_of_derivative (h0 0 (Nat.succ_pos N))
      (hD 0 (Nat.succ_pos N)) hNext hx

theorem expGuard_remainder {N : ℕ} {F : ℕ → ℝ → ℝ} {P : ℝ[X]}
    (h0 : ∀ j < N, F j 0 = (derivative^[j] P).eval 0)
    (hD : ∀ j x, HasDerivAt (F j) (F (j + 1) x) x)
    (hN : ∀ x > 0, (derivative^[N] P).eval x < F N x) {x : ℝ} (hx : 0 < x) :
    P.eval x < F 0 x := by
  let G (n : ℕ) (t : ℝ) := F n t - (derivative^[n] P).eval t
  have hG0 (j : ℕ) (hj : j < N) : G j 0 = 0 := sub_eq_zero.mpr (h0 j hj)
  have hGD (j : ℕ) (hj : j < N) (t : ℝ) : HasDerivAt (G j) (G (j + 1) t) t := by
    simpa only [G, Function.iterate_succ_apply'] using (hD j t).sub ((derivative^[j] P).hasDerivAt t)
  have hGN (t : ℝ) (ht : 0 < t) : 0 < G N t := sub_pos.mpr (hN t ht)
  simpa only [G, Function.iterate_zero_apply, sub_pos] using derivativeChain_pos N G hG0 hGD hGN x hx

private noncomputable def adjointGuardD (n : ℕ) (x : ℝ) : ℝ :=
  expQuad 2 0 (2 ^ n * 2) (2 ^ n * (n - 7)) x +
    expQuad 1 (-1) (12 - 2 * n) (14 + 12 * n - n * (n - 1)) x

private noncomputable def adjointGuardP : ℝ[X] :=
  ∑ j ∈ Finset.range 8, C
    (match j with
      | 0 => 7
      | 1 => 14
      | 2 => 8
      | 3 => 2
      | 4 => 1 / 12
      | 5 => -(1 / 12)
      | 6 => -(1 / 90)
      | _ => 1 / 90 : ℝ) * X ^ j

private theorem adjointGuard_polynomial_pos {x : ℝ} (hx : 0 < x) :
    0 < x ^ 2 + 2 * x ^ 3 + x ^ 4 / 12 - x ^ 5 / 12 - x ^ 6 / 90 + x ^ 7 / 90 := by
  by_cases h₁ : x ≤ 1
  · have h₅ := mul_le_mul_of_nonneg_right
      (show x ^ 3 ≤ 1 by simpa only [one_pow] using pow_le_pow_left₀ hx.le h₁ 3) (sq_nonneg x)
    have h₆ := mul_le_mul_of_nonneg_right
      (show x ^ 4 ≤ 1 by simpa only [one_pow] using pow_le_pow_left₀ hx.le h₁ 4) (sq_nonneg x)
    nlinarith only [h₅, h₆, sq_pos_of_pos hx, pow_nonneg hx.le 3, pow_nonneg hx.le 4, pow_nonneg hx.le 7]
  · have h1 : 1 ≤ x := (lt_of_not_ge h₁).le
    have h76 := mul_le_mul_of_nonneg_right h1 (pow_nonneg hx.le 6)
    by_cases h₃ : x ≤ 3
    · have h53 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx.le h₃ 2) (pow_nonneg hx.le 3)
      nlinarith only [h76, h53, sq_pos_of_pos hx, pow_nonneg hx.le 3, pow_nonneg hx.le 4]
    · have h3 : 3 ≤ x := (lt_of_not_ge h₃).le
      have h := mul_nonneg (mul_nonneg (pow_nonneg hx.le 4) (sub_nonneg.mpr h1))
        (show 0 ≤ x ^ 2 / 90 - 1 / 12 by nlinarith only [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) h3 2])
      nlinarith only [h, sq_pos_of_pos hx, pow_nonneg hx.le 3]

private theorem adjointGuard_pos {x : ℝ} (hx : 0 < x) :
    0 < (2 * x - 7) * Real.exp (2 * x) + (14 + 12 * x - x ^ 2) * Real.exp x -
      7 * (1 + x) ^ 2 := by
  have hD (n : ℕ) (t : ℝ) : HasDerivAt (adjointGuardD n) (adjointGuardD (n + 1) t) t := by
    unfold adjointGuardD
    convert (expQuad_deriv 2 0 (2 ^ n * 2) (2 ^ n * (n - 7)) t).add
      (expQuad_deriv 1 (-1) (12 - 2 * n) (14 + 12 * n - n * (n - 1)) t) using 1
    simp only [expQuad, Nat.cast_add, Nat.cast_one, pow_succ]
    ring
  have h0 (n : ℕ) (hn : n < 8) : adjointGuardD n 0 = (derivative^[n] adjointGuardP).eval 0 := by
    interval_cases n <;>
      norm_num [adjointGuardD, expQuad, adjointGuardP, Finset.sum_range_succ, iterate_derivative_sum,
        iterate_derivative_X_pow_eq_C_mul, Nat.descFactorial_succ, Nat.descFactorial_zero]
  have hN (t : ℝ) (ht : 0 < t) : (derivative^[8] adjointGuardP).eval t < adjointGuardD 8 t := by
    have hP : (derivative^[8] adjointGuardP).eval t = 0 := by
      norm_num [adjointGuardP, Finset.sum_range_succ, iterate_derivative_sum,
        iterate_derivative_X_pow_eq_C_mul, Nat.descFactorial_succ, Nat.descFactorial_zero]
    rw [hP]
    norm_num [adjointGuardD, expQuad, two_mul, Real.exp_add]
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp t)
      (show 0 ≤ 512 * t + 256 by positivity)
    have hPos : 0 < (512 * t + 256) * Real.exp t + (54 - 4 * t - t ^ 2) := by
      nlinarith only [h, ht, sq_nonneg t]
    linear_combination Real.exp t * hPos
  have hR := expGuard_remainder h0 hD hN hx
  norm_num [adjointGuardD, expQuad, adjointGuardP, Finset.sum_range_succ] at hR
  nlinarith only [hR, adjointGuard_polynomial_pos hx]

theorem adjointA_lt_seventh {x : ℝ} (hx : 0 < x) :
    7 * polyA x * BoseShape.E x < 1 + x + polyA x * Real.exp x * BoseShape.C x := by
  have h := adjointGuard_pos hx
  apply sub_pos.mp
  have hEq : (1 + x + polyA x * Real.exp x * BoseShape.C x -
      7 * polyA x * BoseShape.E x) * (Real.exp x - 1) ^ 2 =
      (2 * x - 7) * Real.exp (2 * x) + (14 + 12 * x - x ^ 2) * Real.exp x - 7 * (1 + x) ^ 2 := by
    rw [two_mul, Real.exp_add]
    unfold polyA BoseShape.E BoseShape.C
    rw [Real.exp_neg]
    field_simp [(expTail_den_pos hx).ne', Real.exp_ne_zero x]
    ring
  exact pos_of_mul_pos_left (hEq.symm ▸ h) (by positivity)

private noncomputable def retainedGuardD (n : ℕ) (x : ℝ) : ℝ :=
  expQuad (7 / 4) 0 0 ((7 / 4) ^ n) x +
    expQuad (3 / 4) 0 0 (-((3 / 4) ^ n)) x + expQuad 1 0 0 (-5) x

private noncomputable def retainedGuardP : ℝ[X] :=
  ∑ j ∈ Finset.range 7, C
    (match j with
      | 0 => -5
      | 1 => -4
      | 2 => -(5 / 4)
      | 3 => -(1 / 96)
      | 4 => 65 / 384
      | 5 => 2861 / 30720
      | _ => 12055 / 368640 : ℝ) * X ^ j

private theorem retainedGuard_polynomial_pos {x : ℝ} (hx : 0 < x) :
    0 < 1 - (5 / 4) * x - x ^ 2 / 96 + (65 / 384) * x ^ 3 + (2861 / 30720) * x ^ 4 +
      (12055 / 368640) * x ^ 5 := by
  let f (t : ℝ) := 1 - (5 / 4) * t - t ^ 2 / 96 + (65 / 384) * t ^ 3 + (2861 / 30720) * t ^ 4 +
    (12055 / 368640) * t ^ 5
  change 0 < f x
  by_cases hx₁ : x ≤ 1
  · let df (t : ℝ) := -(5 / 4) - t / 48 + (195 / 384) * t ^ 2 + (11444 / 30720) * t ^ 3 +
      (60275 / 368640) * t ^ 4
    have hd (t : ℝ) : HasDerivAt f (df t) t := by
      have h := hasDerivAt_id t
      convert (((((h.const_mul (5/4)).const_sub 1).sub ((h.pow 2).div_const 96)).add
        ((h.pow 3).const_mul (65/384))).add ((h.pow 4).const_mul (2861/30720))).add
        ((h.pow 5).const_mul (12055/368640)) using 1
      norm_num [df, id_eq]; ring
    have hA : AntitoneOn f (Icc 0 1) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      · exact fun t _ => (hd t).continuousAt.continuousWithinAt
      · exact fun t _ => (hd t).differentiableAt.differentiableWithinAt
      · intro t ht
        have ht' : t ∈ Icc (0 : ℝ) 1 := interior_subset ht
        rw [(hd t).deriv]
        have h2 := pow_le_pow_left₀ ht'.1 ht'.2 2
        have h3 := pow_le_pow_left₀ ht'.1 ht'.2 3
        have h4 := pow_le_pow_left₀ ht'.1 ht'.2 4
        dsimp only [df]
        nlinarith only [ht'.1, h2, h3, h4]
    exact (by norm_num [f] : 0 < f 1).trans_le (hA ⟨hx.le, hx₁⟩ ⟨zero_le_one, le_rfl⟩ hx₁)
  · let y := x - 1
    have hy : 0 ≤ y := sub_nonneg.mpr (lt_of_not_ge hx₁).le
    have hE : x = 1 + y := by dsimp only [y]; ring
    have h : 34 / 1000 - (227 / 1000) * y + (138 / 100) * y ^ 2 ≤ f x := by
      rw [hE]
      dsimp only [f]
      nlinarith only [hy, sq_nonneg y, pow_nonneg hy 3, pow_nonneg hy 4, pow_nonneg hy 5]
    have h₀ : 0 < (34 / 1000 : ℝ) - (227 / 1000) * y + (138 / 100) * y ^ 2 := by
      nlinarith only [sq_nonneg (y - (227 / 2760 : ℝ))]
    exact h₀.trans_le h

private theorem retainedGuard_pos {x : ℝ} (hx : 0 < x) :
    0 < Real.exp ((7 / 4) * x) - Real.exp ((3 / 4) * x) - 5 * Real.exp x + 5 + 5 * x := by
  have hD (n : ℕ) (t : ℝ) : HasDerivAt (retainedGuardD n) (retainedGuardD (n + 1) t) t := by
    unfold retainedGuardD
    convert ((expQuad_deriv (7 / 4) 0 0 ((7 / 4) ^ n) t).add
      (expQuad_deriv (3 / 4) 0 0 (-((3 / 4) ^ n)) t)).add (expQuad_deriv 1 0 0 (-5) t) using 1
    simp only [expQuad, pow_succ]
    ring
  have h0 (n : ℕ) (hn : n < 7) : retainedGuardD n 0 = (derivative^[n] retainedGuardP).eval 0 := by
    interval_cases n <;>
      norm_num [retainedGuardD, expQuad, retainedGuardP, Finset.sum_range_succ, iterate_derivative_sum,
        iterate_derivative_X_pow_eq_C_mul, Nat.descFactorial_succ, Nat.descFactorial_zero]
  have hN (t : ℝ) (ht : 0 < t) : (derivative^[7] retainedGuardP).eval t < retainedGuardD 7 t := by
    have hP : (derivative^[7] retainedGuardP).eval t = 0 := by
      norm_num [retainedGuardP, Finset.sum_range_succ, iterate_derivative_sum,
        iterate_derivative_X_pow_eq_C_mul, Nat.descFactorial_succ, Nat.descFactorial_zero]
    rw [hP]
    have h₁ : Real.exp ((3 / 4) * t) ≤ Real.exp ((7 / 4) * t) :=
      Real.exp_le_exp.mpr (by linarith only [ht])
    have h₂ : Real.exp t ≤ Real.exp ((7 / 4) * t) := Real.exp_le_exp.mpr (by linarith only [ht])
    have h₃ := mul_le_mul_of_nonneg_left h₁ (by norm_num : 0 ≤ (3 / 4 : ℝ) ^ 7)
    norm_num [retainedGuardD, expQuad]
    nlinarith only [h₃, h₂, Real.exp_pos ((7 / 4) * t)]
  have hR := expGuard_remainder h0 hD hN hx
  norm_num [retainedGuardD, expQuad, retainedGuardP, Finset.sum_range_succ] at hR
  nlinarith only [hR, mul_pos hx (retainedGuard_polynomial_pos hx)]

theorem retainedA_exp_lt_fifth {x : ℝ} (hx : 0 < x) :
    polyA x * Real.exp (-(3 / 4) * x) < (1 - Real.exp (-x)) / 5 := by
  have h := retainedGuard_pos hx
  have hE₁ : Real.exp ((7 / 4) * x) * Real.exp (-x) = Real.exp ((3 / 4) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hE₂ : Real.exp ((7 / 4) * x) * Real.exp (-(3 / 4) * x) = Real.exp x := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hE₃ : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  apply sub_pos.mp
  have hEq : ((1 - Real.exp (-x)) / 5 - polyA x * Real.exp (-(3 / 4) * x)) *
      (5 * Real.exp ((7 / 4) * x)) =
      Real.exp ((7 / 4) * x) - Real.exp ((3 / 4) * x) - 5 * Real.exp x + 5 + 5 * x := by
    unfold polyA
    linear_combination -hE₁ + (5 * (1 + x) * Real.exp (-x) - 5) * hE₂ + 5 * (1 + x) * hE₃
  exact pos_of_mul_pos_left (hEq.symm ▸ h) (by positivity)

end ACS12.GammaMeasure

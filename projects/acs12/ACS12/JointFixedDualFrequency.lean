import ACS12.OuterReturnShape
import Mathlib.Analysis.Normed.Algebra.Exponential

/-! The whole-ray frequency bound for the fixed-geometry dual return. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN

private noncomputable def dualCoeff (n : ℕ) : ℝ :=
  16 ^ (n + 2) - 2 * 8 ^ (n + 2) -
    64 * (n + 2 : ℝ) * (n + 1 : ℝ) * 9 ^ n + 4 * (n + 2 : ℝ) * (9 ^ (n + 1) - 1)

private theorem dualCoeff_pos (n : ℕ) : 0 < dualCoeff n := by
  have hDom (k : ℕ) (hk : 2 ≤ k) : (128 : ℝ) * (k + 2 : ℝ) < 63 * (16 / 9) ^ (k + 2) := by
    induction k, hk using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
      have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
      have h := mul_lt_mul_of_pos_right ih (show (0 : ℝ) < 16 / 9 by norm_num)
      simp only [Nat.cast_succ,pow_succ] at h ⊢
      linarith only [h,hk']
  have hStep (k : ℕ) (hk : 2 ≤ k) : 9 * dualCoeff k < dualCoeff (k + 1) := by
    have h := mul_lt_mul_of_pos_right (hDom k hk) (show (0 : ℝ) < 9 ^ (k + 1) by positivity)
    have hPow : (63 : ℝ) * (16 / 9) ^ (k + 2) * 9 ^ (k + 1) = 7 * 16 ^ (k + 2) := by
      rw [div_pow,show k + 2 = k + 1 + 1 by omega,pow_succ (9 : ℝ) (k + 1)]
      have h9 : (0 : ℝ) < 9 ^ (k + 1) := by positivity
      field_simp [h9.ne']
      ring
    rw [hPow] at h
    have hDiff : dualCoeff (k + 1) - 9 * dualCoeff k =
        7 * 16 ^ (k + 2) + 2 * 8 ^ (k + 2) - 128 * (k + 2 : ℝ) * 9 ^ (k + 1) +
          4 * 9 ^ (k + 2) + 32 * (k + 2 : ℝ) - 4 := by
      unfold dualCoeff
      push_cast
      simp only [pow_succ]
      ring
    have h₈ : (0 : ℝ) ≤ 8 ^ (k + 2) := by positivity
    have h₉ : (0 : ℝ) ≤ 9 ^ (k + 2) := by positivity
    have hk₀ : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    linarith only [h,hDiff,h₈,h₉,hk₀]
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n <;> norm_num [dualCoeff]
  · induction n, hn using Nat.le_induction with
    | base => norm_num [dualCoeff]
    | succ n hn ih => exact (mul_pos (by norm_num : (0 : ℝ) < 9) ih).trans (hStep n hn)

private theorem dualFrequency_exp_pos {x : ℝ} (hx : 0 < x) :
    0 < Real.exp (16 * x) - 2 * Real.exp (8 * x) + 1 -
      64 * x ^ 2 * Real.exp (9 * x) + 4 * x * Real.exp (9 * x) - 4 * x * Real.exp x := by
  have he (t : ℝ) : HasSum (fun n : ℕ => t ^ n / (n.factorial : ℝ)) (Real.exp t) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp t
  have h₂ (t : ℝ) : HasSum (fun n : ℕ => t ^ (n + 2) / ((n + 2).factorial : ℝ))
      (Real.exp t - (1 + t)) := by
    simpa [Finset.sum_range_succ] using (hasSum_nat_add_iff' 2).mpr (he t)
  have h₁ (t : ℝ) : HasSum (fun n : ℕ => t ^ (n + 1) / ((n + 1).factorial : ℝ))
      (Real.exp t - 1) := by
    simpa [Finset.sum_range_one] using (hasSum_nat_add_iff' 1).mpr (he t)
  have hS := (((h₂ (16 * x)).sub ((h₂ (8 * x)).mul_left 2)).sub
    ((he (9 * x)).mul_left (64 * x ^ 2))).add
      (((h₁ (9 * x)).sub (h₁ x)).mul_left (4 * x))
  have hSum : HasSum (fun n : ℕ => dualCoeff n * x ^ (n + 2) / ((n + 2).factorial : ℝ))
      (Real.exp (16 * x) - 2 * Real.exp (8 * x) + 1 -
        64 * x ^ 2 * Real.exp (9 * x) + 4 * x * Real.exp (9 * x) - 4 * x * Real.exp x) := by
    convert hS using 1
    · funext n
      unfold dualCoeff
      have hF : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
      have hN : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
      have h2 : (n : ℝ) + 1 + 1 ≠ 0 := by positivity
      simp only [show n + 2 = n + 1 + 1 by omega,Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ,
        mul_pow,pow_succ]
      field_simp [hF.ne',h1,h2]
      ring
    · ring
  rw [← hSum.tsum_eq]
  exact hSum.summable.tsum_pos (fun n => by positivity [dualCoeff_pos n]) 0
    (by positivity [dualCoeff_pos 0])

theorem fixedDual_frequency_lt_one {s : ℝ} (hs : 0 < s) :
    Real.exp (-(7 / 8) * s) * expHeadFactor s * (expHeadFactor s - 1 / 2) < 1 := by
  let x := s / 8
  have hx : 0 < x := by unfold x; positivity
  have h := dualFrequency_exp_pos hx
  have h8 : 8 * x = s := by unfold x; ring
  have h16 : 16 * x = s + s := by unfold x; ring
  have h9 : 9 * x = x + s := by unfold x; ring
  rw [h16,h8,h9,Real.exp_add,Real.exp_add] at h
  have hPoly : 0 < (Real.exp s - 1) ^ 2 -
      s ^ 2 * Real.exp x * Real.exp s + s / 2 * Real.exp x * (Real.exp s - 1) := by
    unfold x at h ⊢
    nlinarith only [h]
  have hD := expTail_den_pos hs
  have hH : expHeadFactor s = s * Real.exp s / (Real.exp s - 1) := by
    rw [expHeadFactor_eq_add_expTail hs]
    unfold expTailFactor
    field_simp [hD.ne']
    ring
  have hE : Real.exp (-(7 / 8) * s) * Real.exp s = Real.exp x := by
    rw [← Real.exp_add]
    congr 1
    unfold x
    ring
  apply (mul_lt_mul_iff_right₀ (sq_pos_of_pos hD)).mp
  rw [hH,mul_comm (Real.exp (-(7 / 8) * s))]
  field_simp [hD.ne']
  have hE' : Real.exp s * Real.exp (-(s * 7 / 8)) = Real.exp x := by
    rw [mul_comm,show -(s * 7 / 8) = -(7 / 8) * s by ring]
    exact hE
  calc
    _ = 2 * (s ^ 2 * Real.exp x * Real.exp s - s / 2 * Real.exp x * (Real.exp s - 1)) := by
      rw [show Real.exp s * s * Real.exp (-(s * 7 / 8)) =
        s * (Real.exp s * Real.exp (-(s * 7 / 8))) by ring,hE']
      ring
    _ < _ := by linarith only [hPoly]

end ACS12.GammaMeasure

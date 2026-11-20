import CenteredCircle.LaplaceSampling
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.GCongr

/-! Polynomial Laplace moments and summability from cubic decay. -/

namespace CenteredCircle.AllN

open MeasureTheory Filter Set
open scoped BigOperators

theorem integral_power_exponential (k : ℕ) (t : ℝ) (ht : 0 < t) :
    (∫ u : ℝ in Ioi 0, u ^ k * Real.exp (-u * t)) =
      (k.factorial : ℝ) / t ^ (k + 1) := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have key := Real.integral_rpow_mul_exp_neg_mul_Ioi hk ht
  calc
    (∫ u : ℝ in Ioi 0, u ^ k * Real.exp (-u * t)) =
        ∫ u : ℝ in Ioi 0, u ^ (((k : ℝ) + 1) - 1) * Real.exp (-(t * u)) := by
      simp only [add_sub_cancel_right, Real.rpow_natCast]
      congr 1
      funext u
      congr 1
      congr 1
      ring
    _ = (k.factorial : ℝ) / t ^ (k + 1) := by
      simp_rw [key, Real.Gamma_nat_eq_factorial, div_eq_mul_inv,
        one_mul, mul_comm, Real.inv_rpow ht.le, ← Real.rpow_natCast]
      norm_cast

theorem integrable_power_exponential (k : ℕ) (t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun u : ℝ => u ^ k * Real.exp (-u * t)) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_power_exponential k t ht]
  positivity

theorem summable_of_power_decay (K : ℝ → ℝ) (C t s : ℝ) (p : ℕ) (hp : 1 < p)
    (hC : 0 ≤ C) (ht : 0 < t) (hs : 0 < s)
    (hK0 : ∀ x, 0 < x → 0 ≤ K x)
    (hK : ∀ x, 0 < x → K x ≤ C / x ^ p) :
    Summable (fun j : ℕ => K (t + j * s)) := by
  let d := min t s
  have hd : 0 < d := lt_min ht hs
  have hdt : d ≤ t := min_le_left _ _
  have hds : d ≤ s := min_le_right _ _
  have hps : Summable (fun j : ℕ => 1 / (j : ℝ) ^ p) :=
    Real.summable_one_div_nat_pow.mpr hp
  have hp' : Summable (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ p) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hps
  have hmajor := hp'.mul_left (C / d ^ p)
  apply Summable.of_nonneg_of_le
    (fun j => hK0 _ (by have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j; nlinarith)) _ hmajor
  intro j
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hx : 0 < t + j * s := by nlinarith
  have hbase : d * ((j : ℝ) + 1) ≤ t + j * s := by nlinarith
  have hpow : (d * ((j : ℝ) + 1)) ^ p ≤ (t + j * s) ^ p := by
    gcongr
  calc
    K (t + j * s) ≤ C / (t + j * s) ^ p := hK _ hx
    _ ≤ C / (d * ((j : ℝ) + 1)) ^ p :=
      div_le_div_of_nonneg_left hC (by positivity) hpow
    _ = C / d ^ p * (1 / ((j : ℝ) + 1) ^ p) := by
      simp only [mul_pow, div_eq_mul_inv, mul_inv_rev]
      ring

theorem summable_of_cubic_decay (K : ℝ → ℝ) (C t s : ℝ)
    (hC : 0 ≤ C) (ht : 0 < t) (hs : 0 < s)
    (hK0 : ∀ x, 0 < x → 0 ≤ K x)
    (hK : ∀ x, 0 < x → K x ≤ C / x ^ 3) :
    Summable (fun j : ℕ => K (t + j * s)) :=
  summable_of_power_decay K C t s 3 (by norm_num) hC ht hs hK0 hK

end CenteredCircle.AllN

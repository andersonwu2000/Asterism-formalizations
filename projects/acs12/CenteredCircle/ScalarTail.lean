import CenteredCircle.LineConvex

/-! A telescoping cubic tail closes the exact eight-term certificate. -/

namespace CenteredCircle.AllN

open Filter
open scoped BigOperators Topology

theorem cubic_step_bound {x : ℝ} (hx : 0 < x) :
    1 / (x + 1) ^ 3 ≤ 1 / (2 * x ^ 2) - 1 / (2 * (x + 1) ^ 2) := by
  have hx1 : 0 < x + 1 := by linarith
  have he : (1 / (2 * x ^ 2) - 1 / (2 * (x + 1) ^ 2)) - 1 / (x + 1) ^ 3 =
      (3 * x + 1) / (2 * x ^ 2 * (x + 1) ^ 3) := by
    field_simp
    <;> ring
  have hp : 0 ≤ (3 * x + 1) / (2 * x ^ 2 * (x + 1) ^ 3) := by positivity
  linarith

theorem cubic_tail_prefix_bound (N : ℕ) :
    (∑ j ∈ Finset.range N, 1 / ((j : ℝ) + 9) ^ 3) ≤
      1 / 128 - 1 / (2 * ((N : ℝ) + 8) ^ 2) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hstep := cubic_step_bound (x := (N : ℝ) + 8) (by positivity)
    rw [show (N : ℝ) + 8 + 1 = (N : ℝ) + 9 by ring] at hstep
    rw [show ((N + 1 : ℕ) : ℝ) + 8 = (N : ℝ) + 9 by push_cast; ring]
    linarith

theorem cubic_tail_summable : Summable (fun j : ℕ => 1 / ((j : ℝ) + 9) ^ 3) := by
  have h := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (3 : ℕ))
  have hs := (summable_nat_add_iff 9).mpr h
  simpa only [Nat.cast_add, Nat.cast_ofNat] using hs

theorem cubic_tail_bound : (∑' j : ℕ, 1 / ((j : ℝ) + 9) ^ 3) ≤ 1 / 128 := by
  apply le_of_tendsto cubic_tail_summable.hasSum.tendsto_sum_nat
  apply Eventually.of_forall
  intro N
  have h := cubic_tail_prefix_bound N
  have hp : 0 ≤ 1 / (2 * ((N : ℝ) + 8) ^ 2) := by positivity
  linarith

theorem rationalPair_tail_bound {b : ℝ} (hb : 0 < b) :
    (∑' j : ℕ, rationalPair b (j + 8)) ≤ (1 + b⁻¹ ^ 2) / 128 := by
  have hs := (summable_nat_add_iff 8).mpr (rationalPair_summable hb)
  have hcmp : ∀ j : ℕ, rationalPair b (j + 8) ≤ (1 + b⁻¹ ^ 2) * (1 / ((j : ℝ) + 9) ^ 3) := by
    intro j
    have h := comparison_pair_cubic_bound (t := (j : ℝ) + 9) hb (by positivity)
    convert h using 1 <;> dsimp [rationalPair] <;> push_cast <;> congr 1 <;> ring
  have h := hs.tsum_le_tsum hcmp (cubic_tail_summable.mul_left (1 + b⁻¹ ^ 2))
  rw [tsum_mul_left] at h
  have hbnd := mul_le_mul_of_nonneg_left cubic_tail_bound
    (by positivity : 0 ≤ 1 + b⁻¹ ^ 2)
  linarith

theorem lineScalar_certificate : lineScalar (7 / 10) ≤ eightTermCertificate := by
  have hb : (0 : ℝ) < 7 / 10 := by norm_num
  have htail := rationalPair_tail_bound hb
  have he := (rationalPair_summable hb).sum_add_tsum_nat_add 8
  rw [lineScalar_eq_rational hb, ← he]
  dsimp [eightTermCertificate]
  change (∑ j ∈ Finset.range 8, rationalPair (7 / 10) j) + _ - _ + _ ≤
    (∑ j ∈ Finset.range 8, rationalPair (7 / 10) j) + _ - _ + _
  linarith

theorem circleScalar_endpoint {L b : ℝ} (hL : 0 < L) (hb : (7 / 10 : ℝ) ≤ b)
    (hb1 : b ≤ 1) (hscalar : 0 ≤ circleScalar L b) : b = 1 := by
  by_cases he : b = 1
  · exact he
  have hbp : 0 < b := by linarith
  have hlt : b < 1 := lt_of_le_of_ne hb1 he
  have hcmp := circleScalar_lt_lineScalar hL hbp hlt
  apply scalar_endpoint_of_comparison lineScalar b (circleScalar L b)
    (lineScalar_convex.subset (fun x hx => by have := hx.1; change 0 < x; linarith)
      (convex_Icc _ _)) lineScalar_one lineScalar_certificate hb hb1 hscalar
  linarith

end CenteredCircle.AllN

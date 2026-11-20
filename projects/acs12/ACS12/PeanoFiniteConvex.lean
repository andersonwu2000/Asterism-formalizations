import ACS12.PeanoExponentShape

/-! Semiconvexity of finite Peano sums from a complete adverse-curvature price. -/

namespace ACS12.GammaMeasure

open MeasureTheory Set Filter
open scoped BigOperators

noncomputable def peanoPower (p x : ℝ) : ℝ := p * (p + 1) * x ^ (-(p + 2))

private noncomputable def peanoPowerSlope (p x : ℝ) : ℝ :=
  (2 * p + 1 - p * (p + 1) * Real.log x) * x ^ (-(p + 2))

private theorem peanoPower_derivative (p : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun r => peanoPower r x) (peanoPowerSlope p x) p := by
  have h := hasDerivAt_id p
  have hExp := (((h.add_const 2).neg.const_mul (Real.log x))).exp
  simp only [id_eq, mul_one, neg_mul, mul_neg, mul_one] at hExp
  simp_rw [peanoPower, peanoPowerSlope, Real.rpow_def_of_pos hx]
  convert (h.mul (h.add_const 1)).mul hExp using 1
  simp only [Pi.mul_apply, Pi.neg_apply, Pi.sub_apply, id_eq]
  ring

private theorem peanoPower_slope_derivative (p : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun r => peanoPowerSlope r x)
      (-(x ^ (-(p + 2)) * peanoExponentQuadratic p (Real.log x))) p := by
  have h := hasDerivAt_id p
  have hExp := (((h.add_const 2).neg.const_mul (Real.log x))).exp
  simp only [id_eq, mul_one, neg_mul, mul_neg, mul_one] at hExp
  have hPoly := ((h.const_mul 2).add_const 1).sub ((h.mul (h.add_const 1)).mul_const (Real.log x))
  simp_rw [peanoPowerSlope, Real.rpow_def_of_pos hx, peanoExponentQuadratic]
  convert hPoly.mul hExp using 1
  simp only [Pi.mul_apply, Pi.neg_apply, Pi.sub_apply, id_eq]
  ring

noncomputable def finitePeanoMesh (a t : ℝ) (N : ℕ) (p : ℝ) : ℝ :=
  a * ∑ j ∈ Finset.range N, peanoPower p (a + t + j * a)

theorem finitePeanoMesh_convex {a t M : ℝ} (ha : 0 < a) (ht : 0 ≤ t) (N : ℕ)
    (hBad : ∀ p ∈ Icc (1 : ℝ) (9 / 5),
      a * ∑ j ∈ Finset.range N, peanoExponentBad p (a + t + j * a) ≤ M) :
    ConvexOn ℝ (Icc 1 (9 / 5)) (fun p => finitePeanoMesh a t N p + (M / 2) * p ^ 2) := by
  let x (j : ℕ) := a + t + j * a
  let f (p : ℝ) := finitePeanoMesh a t N p + (M / 2) * p ^ 2
  let f' (p : ℝ) := a * (∑ j ∈ Finset.range N, peanoPowerSlope p (x j)) + M * p
  let f'' (p : ℝ) := a * (∑ j ∈ Finset.range N,
    -(x j ^ (-(p + 2)) * peanoExponentQuadratic p (Real.log (x j)))) + M
  have hx (j : ℕ) : 0 < x j :=
    add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg ha ht) (mul_nonneg (Nat.cast_nonneg _) ha.le)
  have hD (p : ℝ) : HasDerivAt f (f' p) p := by
    have h := HasDerivAt.fun_sum (u := Finset.range N)
      (fun j _ => peanoPower_derivative p (hx j))
    convert (h.const_mul a).add (((hasDerivAt_id p).pow 2).const_mul (M / 2)) using 1
    norm_num [f', id_eq] <;> ring
  have hD₂ (p : ℝ) : HasDerivAt f' (f'' p) p := by
    have h := HasDerivAt.fun_sum (u := Finset.range N)
      (fun j _ => peanoPower_slope_derivative p (hx j))
    convert (h.const_mul a).add ((hasDerivAt_id p).const_mul M) using 1
    simp [f'', Finset.sum_neg_distrib, mul_neg, show ∀ r : ℝ, -(r + 2) = -2 + -r by intro; ring]
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
    (fun p _ => (hD p).continuousAt.continuousWithinAt)
    (fun p _ => (hD p).hasDerivWithinAt) (fun p _ => (hD₂ p).hasDerivWithinAt)
  intro p hp
  have hQ (j : ℕ) : -peanoExponentBad p (x j) ≤
      -(x j ^ (-(p + 2)) * peanoExponentQuadratic p (Real.log (x j))) := by
    apply neg_le_neg
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.rpow_nonneg (hx j).le _)
  have hSum := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.range N) (fun j _ => hQ j)) ha.le
  rw [Finset.sum_neg_distrib, mul_neg] at hSum
  have hB := hBad p (interior_subset hp)
  dsimp only [f'']
  linarith only [hSum, hB]

end ACS12.GammaMeasure

import ACS12.JointLogSlope
import ACS12.TrapezoidPositive

/-! Whole Z semiconcavity via the finite unit trapezoids and exact series limit. -/

namespace ACS12.GammaMeasure

open Set Filter MeasureTheory
open scoped BigOperators Topology

theorem zetaCurvature_partial_bounds {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) (N : ℕ) :
    let b : ℝ := 4 + ((N + 1 : ℕ) : ℝ)
    let S := ∑ j ∈ Finset.range (N + 5), zetaCurvature p (1 + j)
    S < 1 / 8 ∧ 299 / 4000 + zetaCurvaturePrimitive p b + zetaCurvature p b / 2 < S := by
  let f := zetaCurvature p
  let D := zetaCurvatureSlope p
  let E := zetaCurvatureSpatial p
  let F := zetaCurvaturePrimitive p
  let M := N + 1
  let b : ℝ := 4 + M
  have hM : 0 < M := Nat.succ_pos N
  have hb : (4 : ℝ) ≤ b := le_add_of_nonneg_right (Nat.cast_nonneg M)
  have hF {a c : ℝ} (ha : 0 < a) (hc : a ≤ c) : IntervalIntegrable f volume a c := by
    apply ContinuousOn.intervalIntegrable_of_Icc hc
    exact fun x hx => (zetaCurvature_hasDerivAt p (ha.trans_le hx.1)).continuousAt.continuousWithinAt
  have hE (k : ℕ) : IntervalIntegrable (fun x => max 0 (E x)) volume (4 + k) (4 + (k + 1 : ℕ)) := by
    have ha : (0 : ℝ) < 4 + k := by positivity
    have hk : (4 : ℝ) + k ≤ 4 + (k + 1 : ℕ) := by push_cast; linarith
    have hC : ContinuousOn E (Icc (4 + k : ℝ) (4 + (k + 1 : ℕ))) :=
      (zetaCurvatureSpatial_continuousOn p).mono (fun x hx => ha.trans_le hx.1)
    exact (continuous_max.comp_continuousOn (continuousOn_const.prodMk hC)).intervalIntegrable_of_Icc hk
  have hCell (k : ℕ) : trapezoidal_error f 1 (4 + k) (4 + (k + 1 : ℕ)) ≤
      (1 / 8) * ∫ x in (4 + k : ℝ)..(4 + (k + 1 : ℕ)), max 0 (E x) := by
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc]
    have ha : (0 : ℝ) < 4 + k := by positivity
    exact ACS12.trapezoidalError_unit_le
      (fun x hx => zetaCurvature_hasDerivAt p (ha.trans_le hx.1))
      (fun x hx => zetaCurvatureSlope_hasDerivAt p (ha.trans_le hx.1))
      ((zetaCurvatureSpatial_continuousOn p).mono (fun x hx => ha.trans_le hx.1))

  have hNegI (k : ℕ) : IntervalIntegrable (fun x => max 0 (-E x)) volume (4 + k) (4 + (k + 1 : ℕ)) := by
    have ha : (0 : ℝ) < 4 + k := by positivity
    have hk : (4 : ℝ) + k ≤ 4 + (k + 1 : ℕ) := by push_cast; linarith
    have hC : ContinuousOn E (Icc (4 + k : ℝ) (4 + (k + 1 : ℕ))) :=
      (zetaCurvatureSpatial_continuousOn p).mono (fun x hx => ha.trans_le hx.1)
    exact (continuous_max.comp_continuousOn (continuousOn_const.prodMk hC.neg)).intervalIntegrable_of_Icc hk
  have hCellNeg (k : ℕ) :
      -(1 / 8) * (∫ x in (4 + k : ℝ)..(4 + (k + 1 : ℕ)), max 0 (-E x)) ≤
        trapezoidal_error f 1 (4 + k) (4 + (k + 1 : ℕ)) := by
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc]
    have ha : (0 : ℝ) < 4 + k := by positivity
    exact ACS12.trapezoidalError_unit_ge
      (fun x hx => zetaCurvature_hasDerivAt p (ha.trans_le hx.1))
      (fun x hx => zetaCurvatureSlope_hasDerivAt p (ha.trans_le hx.1))
      ((zetaCurvatureSpatial_continuousOn p).mono (fun x hx => ha.trans_le hx.1))
  have hSN := Finset.sum_le_sum (s := Finset.range M) (fun k _ => hCellNeg k)
  rw [← Finset.mul_sum, intervalIntegral.sum_integral_adjacent_intervals (a := fun k => 4 + (k : ℝ))
    (fun k _ => hNegI k)] at hSN
  simp only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one] at hSN
  have hS := Finset.sum_le_sum (s := Finset.range M) (fun k _ => hCell k)
  rw [← Finset.mul_sum, intervalIntegral.sum_integral_adjacent_intervals (a := fun k => 4 + (k : ℝ))
    (fun k _ => hE k)] at hS
  simp only [Nat.cast_zero, add_zero] at hS
  have hTr := sum_trapezoidal_error_adjacent_intervals (f := f) (a := 4) (h := 1)
    hM (by simpa only [mul_one] using hF (by norm_num) hb)
  simp only [mul_one] at hTr
  simp only [Nat.cast_add, Nat.cast_one] at hS
  rw [hTr] at hS hSN
  have hV := zetaCurvature_positiveVariation_le hp hP hb
  have hI : (∫ x in (4 : ℝ)..b, f x) = F b - F 4 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => zetaCurvaturePrimitive_hasDerivAt p (by
        rw [uIcc_of_le hb] at hx
        exact (by norm_num : (0 : ℝ) < 4).trans_le hx.1)) (hF (by norm_num) hb)
  have h := hS.trans (mul_le_mul_of_nonneg_left hV (by norm_num))
  change trapezoidal_error f M 4 b ≤ _ at h
  rw [trapezoidal_error, hI] at h
  have hBM : (b - 4) / M = 1 := by
    dsimp only [b]
    rw [add_sub_cancel_left, div_self (Nat.cast_ne_zero.mpr hM.ne')]
  have hTrE : trapezoidal_integral f M 4 b =
      (f 4 + f b) / 2 + ∑ j ∈ Finset.range N, f (5 + j) := by
    unfold trapezoidal_integral
    rw [hBM, one_mul, show M - 1 = N by omega]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_div_assoc, hBM, mul_one]
    congr 1
    ring
  have hSum : (∑ j ∈ Finset.range (N + 5), f (1 + j)) =
      f 2 + f 3 + f 4 + (∑ j ∈ Finset.range N, f (5 + j)) + f b := by
    have hOne : f 1 = 0 := by simp [f, zetaCurvature]
    rw [show N + 5 = (4 + N) + 1 by omega, Finset.sum_range_succ, Finset.sum_range_add]
    norm_num [Finset.sum_range_succ, hOne, Nat.cast_add]
    have hB : 1 + (4 + (N : ℝ)) = b := by dsimp only [b, M]; push_cast; ring
    rw [hB]
    have hT : (∑ j ∈ Finset.range N, f (1 + (4 + (j : ℝ)))) =
        ∑ j ∈ Finset.range N, f (5 + j) := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      ring
    rw [hT]
  have hRem : F b + f b / 2 ≤ 0 := by
    have hb₀ : 0 < b := (by norm_num : (0 : ℝ) < 4).trans_le hb
    have hLog : 0 ≤ Real.log b := Real.log_nonneg ((by norm_num : (1 : ℝ) ≤ 4).trans hb)
    have hExp : b ^ (-(p + 1)) = b ^ (-p) / b := by
      rw [show -(p + 1) = -p - 1 by ring, Real.rpow_sub_one hb₀.ne']
    change zetaCurvaturePrimitive p b + zetaCurvature p b / 2 ≤ 0
    rw [zetaCurvaturePrimitive, zetaCurvature, hExp]
    have hP' : p ≤ 2 * b := by linarith only [hP, hb]
    have hB : b ^ (-p) * Real.log b * (p * Real.log b - 2) ≤
        2 * b * (b ^ (-p) * Real.log b ^ 2) := by
      have hQ := mul_le_mul_of_nonneg_right hP' (sq_nonneg (Real.log b))
      have hR := mul_le_mul_of_nonneg_left hQ (Real.rpow_nonneg hb₀.le (-p))
      nlinarith only [hR, mul_nonneg (Real.rpow_nonneg hb₀.le (-p)) hLog]
    have hC := (div_le_iff₀ (show 0 < 2 * b by positivity)).mpr (hB.trans_eq (mul_comm _ _))
    have hE : b ^ (-p) / b * Real.log b * (p * Real.log b - 2) / 2 =
        b ^ (-p) * Real.log b * (p * Real.log b - 2) / (2 * b) := by ring
    rw [hE]
    linarith only [hC]
  rw [hTrE] at h
  have hR := zetaCurvatureReference_lt hp hP
  change -F 4 + f 2 + f 3 + (1 / 2) * f 4 < 119 / 1000 at hR

  have hR' := zetaCurvatureReference_gt hp hP
  change 2 / 25 < -F 4 + f 2 + f 3 + (1 / 2) * f 4 at hR'
  have hVN := zetaCurvature_negativeVariation_le hp hP hb
  have hN := (mul_le_mul_of_nonpos_left hVN (by norm_num : (-(1 / 8) : ℝ) ≤ 0)).trans hSN
  change -(1 / 8) * (21 / 500) ≤ trapezoidal_error f M 4 b at hN
  rw [trapezoidal_error,hI,hTrE] at hN
  constructor
  · change (∑ j ∈ Finset.range (N + 5), f (1 + j)) < _
    rw [hSum]
    linarith only [h, hR, hRem]
  · change 299 / 4000 + F b + f b / 2 < (∑ j ∈ Finset.range (N + 5), f (1 + j))
    rw [hSum]
    linarith only [hN,hR']


private noncomputable def partialZ (N : ℕ) (p : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (N + 5), p * (1 + (j : ℝ)) ^ (-(p + 1))

private theorem partialZ_semiconcave (N : ℕ) :
    ConvexOn ℝ (Icc 1 (9 / 5)) (fun p => -partialZ N p + (1 / 16) * p ^ 2) := by
  let g (p : ℝ) := -partialZ N p + (1 / 16) * p ^ 2
  let d (p : ℝ) := -(∑ j ∈ Finset.range (N + 5),
    (1 + (j : ℝ)) ^ (-(p + 1)) * (1 - p * Real.log (1 + j))) + (1 / 8) * p
  let e (p : ℝ) := -(∑ j ∈ Finset.range (N + 5), zetaCurvature p (1 + j)) + 1 / 8
  have hx (j : ℕ) : 0 < 1 + (j : ℝ) := by positivity
  have hd (p : ℝ) : HasDerivAt g (d p) p := by
    have h := HasDerivAt.fun_sum (u := Finset.range (N + 5))
      (fun j _ => zetaTerm_exponent_hasDerivAt (hx j) p)
    convert h.neg.add (((hasDerivAt_id p).pow 2).const_mul (1 / 16)) using 1
    norm_num [d, id_eq] <;> ring
  have he (p : ℝ) : HasDerivAt d (e p) p := by
    have h := HasDerivAt.fun_sum (u := Finset.range (N + 5))
      (fun j _ => zetaTerm_exponent_second_hasDerivAt (hx j) p)
    convert h.neg.add ((hasDerivAt_id p).const_mul (1 / 8)) using 1
    simp [e]
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
    (fun p _ => (hd p).continuousAt.continuousWithinAt)
    (fun p _ => (hd p).hasDerivWithinAt) (fun p _ => (he p).hasDerivWithinAt)
  intro p hp
  have hp' : p ∈ Icc (1 : ℝ) (9 / 5) := interior_subset hp
  have h := (zetaCurvature_partial_bounds hp'.1 hp'.2 N).1
  dsimp only [e]
  linarith only [h]

theorem pureZ_semiconcave :
    ConvexOn ℝ (Icc 1 (9 / 5)) (fun p => -pureZ p + (1 / 16) * p ^ 2) := by
  have hLimit (p : ℝ) (hp : p ∈ Icc (1 : ℝ) (9 / 5)) :
      Tendsto (fun N : ℕ => -partialZ N p + (1 / 16) * p ^ 2) atTop
        (𝓝 (-pureZ p + (1 / 16) * p ^ 2)) := by
    have hS := (powerTail_summable (q := p + 1) (by linarith only [hp.1]) 1).hasSum.tendsto_sum_nat
    have h := ((hS.comp (tendsto_add_atTop_nat 5)).const_mul p).neg.add_const ((1 / 16) * p ^ 2)
    simpa only [partialZ, pureZ, powerTail, Finset.mul_sum, Function.comp_apply, Nat.cast_one] using h
  refine ⟨convex_Icc _ _, ?_⟩
  intro p hp q hq a b ha hb hab
  exact le_of_tendsto_of_tendsto (hLimit _ (convex_Icc _ _ hp hq ha hb hab))
    (((hLimit p hp).const_mul a).add ((hLimit q hq).const_mul b))
    (Eventually.of_forall (fun N => (partialZ_semiconcave N).2 hp hq ha hb hab))

end ACS12.GammaMeasure

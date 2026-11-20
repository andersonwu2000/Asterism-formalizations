import ACS12.PowerSine

/-! Complete Bose moments and the integer reference tails. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open scoped BigOperators

noncomputable def powerTail (q : ℝ) (m : ℕ) : ℝ :=
  ∑' j : ℕ, ((m : ℝ) + (j : ℝ)) ^ (-q)

theorem powerTail_summable {q : ℝ} (hq : 1 < q) (m : ℕ) :
    Summable (fun j : ℕ => ((m : ℝ) + (j : ℝ)) ^ (-q)) := by
  have h := (Real.summable_nat_rpow (p := -q)).mpr (by linarith)
  simpa only [Nat.cast_add, add_comm] using (summable_nat_add_iff m).mpr h

theorem powerTail_pos {q : ℝ} (hq : 1 < q) {m : ℕ} (hm : 0 < m) :
    0 < powerTail q m := by
  have hm₀ : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  exact (powerTail_summable hq m).tsum_pos
    (fun j => Real.rpow_nonneg (by positivity) _) 0 (Real.rpow_pos_of_pos (by positivity) _)

theorem powerTail_shift {q : ℝ} (hq : 1 < q) (m : ℕ) :
    powerTail q (m + 1) = powerTail q m - (m : ℝ) ^ (-q) := by
  have h := (powerTail_summable hq m).tsum_eq_zero_add
  simp only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one] at h
  have hE : (∑' j : ℕ, ((m : ℝ) + (j + (1 : ℝ))) ^ (-q)) = powerTail q (m + 1) := by
    unfold powerTail
    apply tsum_congr
    intro j
    rw [Nat.cast_add, Nat.cast_one]
    congr 1
    ring
  rw [hE] at h
  change powerTail q m = _ at h
  linarith

/-- The complete Bose moment, including its positive infinite tail. -/
theorem boseMoment_integral {r : ℝ} (hr : 0 < r) {m : ℕ} (hm : 0 < m) :
    (∫ s : ℝ in Ioi 0, s ^ r * (Real.exp (-s * m) / (1 - Real.exp (-s)))) =
      Real.Gamma (r + 1) * powerTail (r + 1) m := by
  let f (j : ℕ) (s : ℝ) := s ^ r * Real.exp (-s * ((m : ℝ) + (j : ℝ)))
  let μ := volume.restrict (Ioi (0 : ℝ))
  have hm₀ : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have ha : 0 < r + 1 := by positivity
  have hj (j : ℕ) : 0 < (m : ℝ) + (j : ℝ) := add_pos_of_pos_of_nonneg hm₀ (Nat.cast_nonneg _)
  have hEq (j : ℕ) :
      (∫ s : ℝ, f j s ∂μ) = Real.Gamma (r + 1) * ((m : ℝ) + (j : ℝ)) ^ (-(r + 1)) := by
    have h := GammaDeficit.gamma_exp_integral ha (hj j)
    rw [show r + 1 - 1 = r by ring] at h
    refine (setIntegral_congr_fun measurableSet_Ioi ?_).trans h
    intro s _
    dsimp [f]
    rw [neg_mul, neg_mul, mul_comm s]
  have hI (j : ℕ) : Integrable (f j) μ :=
    Integrable.of_integral_ne_zero (by rw [hEq]; positivity)
  have hNorm (j : ℕ) : (∫ s : ℝ, ‖f j s‖ ∂μ) = ∫ s : ℝ, f j s ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (mem_Ioi.mp hs).le _) (Real.exp_pos _).le)
  have hSum : Summable (fun j => ∫ s : ℝ, ‖f j s‖ ∂μ) := by
    simp_rw [hNorm, hEq]
    exact (powerTail_summable (by linarith : 1 < r + 1) m).mul_left _
  have h := integral_tsum_of_summable_integral_norm hI hSum
  simp_rw [hEq] at h
  rw [tsum_mul_left] at h
  refine (integral_congr_ae ?_).trans h.symm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs₀ : 0 < s := hs
  have hPoint := (exponential_samples_hasSum s (m : ℝ) 1 hs₀ zero_lt_one).mul_left (s ^ r)
  simpa only [f, mul_one] using hPoint.tsum_eq.symm

theorem boseMoment_integrable {r : ℝ} (hr : 0 < r) {m : ℕ} (hm : 0 < m) :
    IntegrableOn (fun s : ℝ => s ^ r * (Real.exp (-s * m) / (1 - Real.exp (-s)))) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [boseMoment_integral hr hm]
  exact (mul_pos (Real.Gamma_pos_of_pos (by positivity))
    (powerTail_pos (by linarith : 1 < r + 1) hm)).ne'

theorem expMoment_nat_integral (r : ℕ) {c : ℝ} (hc : 0 < c) :
    (∫ s : ℝ in Ioi 0, s ^ r * Real.exp (-s * c)) = (r.factorial : ℝ) / c ^ (r + 1) := by
  have h := GammaDeficit.gamma_exp_integral (a := (r : ℝ) + 1) (by positivity) hc
  rw [add_sub_cancel_right, Real.Gamma_nat_eq_factorial, Real.rpow_neg hc.le,
    ← Nat.cast_one, ← Nat.cast_add, Real.rpow_natCast, ← div_eq_mul_inv] at h
  simpa only [Real.rpow_natCast, neg_mul, mul_comm c] using h

theorem expMoment_nat_integrable (r : ℕ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun s : ℝ => s ^ r * Real.exp (-s * c)) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [expMoment_nat_integral r hc]
  positivity

theorem boseMoment_nat_integral {r m : ℕ} (hr : 0 < r) (hm : 0 < m) :
    (∫ s : ℝ in Ioi 0, s ^ r * (Real.exp (-s * m) / (1 - Real.exp (-s)))) =
      (r.factorial : ℝ) * powerTail ((r : ℝ) + 1) m := by
  simpa only [Real.rpow_natCast, Real.Gamma_nat_eq_factorial] using
    boseMoment_integral (Nat.cast_pos.mpr hr) hm

theorem boseMoment_nat_integrable {r m : ℕ} (hr : 0 < r) (hm : 0 < m) :
    IntegrableOn (fun s : ℝ => s ^ r * (Real.exp (-s * m) / (1 - Real.exp (-s)))) (Ioi 0) := by
  simpa only [Real.rpow_natCast] using boseMoment_integrable (Nat.cast_pos.mpr hr) hm

private theorem zeta3_tail_le :
    (∑' j : ℕ, (1 : ℝ) / ((16 : ℝ) + j + 1) ^ 3) ≤ 1 / (2 * 16 ^ 2) := by
  let a (j : ℕ) : ℝ := 1 / (2 * ((16 : ℝ) + j) ^ 2)
  have ha : Summable a := by
    have h := powerTail_summable (by norm_num : (1 : ℝ) < 2) 16
    apply (h.mul_left (1 / 2 : ℝ)).congr
    intro j
    dsimp [a]
    rw [Real.rpow_neg (by positivity), Real.rpow_two, one_div, one_div, mul_inv_rev]
    ring
  have ha' : Summable (fun j : ℕ => a (j + 1)) := (summable_nat_add_iff 1).mpr ha
  have hTelescope : (∑' j : ℕ, (a j - a (j + 1))) = a 0 := by
    rw [ha.tsum_sub ha']
    linarith [ha.tsum_eq_zero_add]
  rw [← show a 0 = 1 / (2 * (16 : ℝ) ^ 2) by norm_num [a], ← hTelescope]
  have hS := powerTail_summable (by norm_num : (1 : ℝ) < 3) 17
  have hE (j : ℕ) : ((17 : ℝ) + j) ^ (-(3 : ℝ)) = 1 / ((16 : ℝ) + j + 1) ^ 3 := by
    rw [Real.rpow_neg (by positivity), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, inv_eq_one_div]
    congr 1
    ring
  have hS' : Summable (fun j : ℕ => (1 : ℝ) / ((16 : ℝ) + j + 1) ^ 3) :=
    hS.congr fun j => hE j
  apply hS'.tsum_le_tsum _ (ha.sub ha')
  intro j
  let x := (16 : ℝ) + j
  have hx : 16 ≤ x := le_add_of_nonneg_right (Nat.cast_nonneg j)
  have hx₀ : 0 < x := by linarith
  have hx₁ : 0 < x + 1 := by linarith
  change 1 / (x + 1) ^ 3 ≤ a j - a (j + 1)
  have he : a (j + 1) = 1 / (2 * (x + 1) ^ 2) := by dsimp [a, x]; push_cast; congr 2; ring
  rw [he]
  change _ ≤ 1 / (2 * x ^ 2) - 1 / (2 * (x + 1) ^ 2)
  have hEq : 1 / (2 * x ^ 2) - 1 / (2 * (x + 1) ^ 2) - 1 / (x + 1) ^ 3 =
      (3 * x + 1) / (2 * x ^ 2 * (x + 1) ^ 3) := by
    field_simp [hx₀.ne', hx₁.ne']
    ring
  apply sub_nonneg.mp
  rw [hEq]
  positivity

theorem powerTail_three_lt : powerTail 3 1 < 6011 / 5000 := by
  have hS := powerTail_summable (by norm_num : (1 : ℝ) < 3) 1
  have hSplit := hS.sum_add_tsum_nat_add 16
  have hE (j : ℕ) : ((1 : ℝ) + j) ^ (-(3 : ℝ)) = 1 / ((1 : ℝ) + j) ^ 3 := by
    rw [Real.rpow_neg (by positivity), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, inv_eq_one_div]
  simp_rw [Nat.cast_one, hE] at hSplit
  have hTail : (∑' j : ℕ, (1 : ℝ) / (1 + (↑(j + 16) : ℝ)) ^ 3) ≤ 1 / (2 * 16 ^ 2) := by
    have hh : (∑' j : ℕ, (1 : ℝ) / (1 + (↑(j + 16) : ℝ)) ^ 3) =
        ∑' j : ℕ, (1 : ℝ) / ((16 : ℝ) + j + 1) ^ 3 := by
      apply tsum_congr
      intro j
      push_cast
      congr 1
      ring
    exact hh.le.trans zeta3_tail_le
  have hFin : (∑ j ∈ Finset.range 16, (1 : ℝ) / (1 + (j : ℝ)) ^ 3) + 1 / (2 * 16 ^ 2) < 6011 / 5000 := by
    norm_num [Finset.sum_range_succ]
  unfold powerTail
  simp_rw [Nat.cast_one, hE]
  linarith

theorem powerTail_four_gt : (5411 / 5000 : ℝ) < powerTail 4 1 := by
  have hS := powerTail_summable (by norm_num : (1 : ℝ) < 4) 1
  have h := hS.sum_le_tsum (Finset.range 16) (fun _ _ => Real.rpow_nonneg (by positivity) _)
  have hE (j : ℕ) : ((1 : ℝ) + j) ^ (-(4 : ℝ)) = 1 / ((1 : ℝ) + j) ^ 4 := by
    rw [Real.rpow_neg (by positivity), show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, inv_eq_one_div]
  have hFin : (5411 / 5000 : ℝ) < ∑ j ∈ Finset.range 16, 1 / ((1 : ℝ) + j) ^ 4 := by
    norm_num [Finset.sum_range_succ]
  unfold powerTail
  simp_rw [Nat.cast_one, hE] at h ⊢
  exact hFin.trans_le h

end ACS12.GammaMeasure

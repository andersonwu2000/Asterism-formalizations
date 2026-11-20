import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! Complete first-order canonical G residual, including every series coefficient. -/
namespace ACS12.Pressure

private noncomputable def sinhShiftCoeff (b : ℝ) (k j : ℕ) : ℝ :=
  if k ≤ j then b ^ (2 * (j - k) + 1) / ((2 * (j - k) + 1).factorial : ℝ) else 0

private noncomputable def coshShiftCoeff (k j : ℕ) : ℝ :=
  if k ≤ j then 1 / ((2 * (j - k)).factorial : ℝ) else 0

private theorem hasSum_shift {f : ℕ → ℝ} {z : ℝ} (h : HasSum f z) (k : ℕ) :
    HasSum (fun j => if k ≤ j then f (j - k) else 0) z := by
  let F (j : ℕ) := if k ≤ j then f (j - k) else 0
  have hF : (∑ j ∈ Finset.range k, F j) = 0 := Finset.sum_eq_zero (by
    intro j hj
    exact if_neg (not_le.mpr (Finset.mem_range.mp hj)))
  apply (hasSum_nat_add_iff' k).mp
  change HasSum (fun j => F (j + k)) (z - ∑ j ∈ Finset.range k, F j)
  rw [hF,sub_zero]
  have hE (j : ℕ) : F (j + k) = f j := by
    simp only [F,show k ≤ j + k by omega,if_true,Nat.add_sub_cancel]
  simpa only [hE] using h

private theorem sinhShift_hasSum (b v : ℝ) (k : ℕ) :
    HasSum (fun j => sinhShiftCoeff b k j * v ^ (2 * j + 1)) (v ^ (2 * k) * Real.sinh (b * v)) := by
  convert hasSum_shift ((Real.hasSum_sinh (b * v)).mul_left (v ^ (2 * k))) k using 1
  funext j
  unfold sinhShiftCoeff
  split_ifs with h
  · rw [mul_pow,show 2 * j + 1 = 2 * k + (2 * (j - k) + 1) by omega,pow_add]
    ring
  · simp

private theorem coshShift_hasSum (v : ℝ) (k : ℕ) :
    HasSum (fun j => coshShiftCoeff k j * v ^ (2 * j + 1)) (v ^ (2 * k + 1) * Real.cosh v) := by
  convert hasSum_shift ((Real.hasSum_cosh v).mul_left (v ^ (2 * k + 1))) k using 1
  funext j
  unfold coshShiftCoeff
  split_ifs with h
  · rw [show 2 * j + 1 = 2 * k + 1 + 2 * (j - k) by omega,pow_add]
    ring
  · simp

noncomputable def pressureGapResidual (v : ℝ) : ℝ :=
  (2 / (9 / 14)) * (1 + (887 / 3920) * v ^ 2) ^ 2 * Real.sinh ((9 / 14) * v) +
  (5 / 14) * v ^ 2 * (1 + v ^ 2 / 10) * (1 + (887 / 3920) * v ^ 2) * Real.sinh v -
  2 * v * (1 + 2 * (1 / 10) * v ^ 2 + (1 / 10) * (887 / 3920) * v ^ 4) * Real.cosh v

private noncomputable def gapCoeff (j : ℕ) : ℝ :=
  let b : ℝ := 1 / 10
  let q : ℝ := 887 / 3920
  let a : ℝ := 5 / 14
  let β : ℝ := 9 / 14
  (2 / β) * (sinhShiftCoeff β 0 j + 2 * q * sinhShiftCoeff β 1 j + q ^ 2 * sinhShiftCoeff β 2 j) +
  (a * sinhShiftCoeff 1 1 j - 2 * coshShiftCoeff 0 j) +
  (a * (b + q) * sinhShiftCoeff 1 2 j - 4 * b * coshShiftCoeff 1 j) +
  (a * b * q * sinhShiftCoeff 1 3 j - 2 * b * q * coshShiftCoeff 2 j)

private theorem gapResidual_hasSum (v : ℝ) :
    HasSum (fun j => gapCoeff j * v ^ (2 * j + 1)) (pressureGapResidual v) := by
  let b : ℝ := 1 / 10
  let q : ℝ := 887 / 3920
  let a : ℝ := 5 / 14
  let β : ℝ := 9 / 14
  have hA := (((sinhShift_hasSum β v 0).add ((sinhShift_hasSum β v 1).mul_left (2 * q))).add
    ((sinhShift_hasSum β v 2).mul_left (q ^ 2))).mul_left (2 / β)
  have hB := ((sinhShift_hasSum 1 v 1).mul_left a).sub ((coshShift_hasSum v 0).mul_left 2)
  have hC := ((sinhShift_hasSum 1 v 2).mul_left (a * (b + q))).sub ((coshShift_hasSum v 1).mul_left (4 * b))
  have hD := ((sinhShift_hasSum 1 v 3).mul_left (a * b * q)).sub ((coshShift_hasSum v 2).mul_left (2 * b * q))
  convert ((hA.add hB).add hC).add hD using 1
  · funext j
    dsimp only [gapCoeff,a,b,q,β]
    ring
  · norm_num [pressureGapResidual,a,b,q,β]
    ring

private theorem gapCoeff_tail_nonneg {j : ℕ} (hj : 5 ≤ j) : 0 ≤ gapCoeff j := by
  let b : ℝ := 1 / 10
  let q : ℝ := 887 / 3920
  let a : ℝ := 5 / 14
  let β : ℝ := 9 / 14
  have hS (k : ℕ) : 0 ≤ sinhShiftCoeff β k j := by
    unfold sinhShiftCoeff
    split_ifs
    · dsimp only [β]; positivity
    · exact le_rfl
  have hTerm (k : ℕ) (hk : k + 1 ≤ j) (A B : ℝ)
      (hAB : B ≤ A * (2 * (j - k) : ℕ)) :
      0 ≤ A * sinhShiftCoeff 1 (k + 1) j - B * coshShiftCoeff k j := by
    unfold sinhShiftCoeff coshShiftCoeff
    rw [if_pos hk,if_pos (by omega : k ≤ j),one_pow]
    have hN : 2 * (j - k) = 2 * (j - (k + 1)) + 1 + 1 := by omega
    have hF : ((2 * (j - k)).factorial : ℝ) =
        (2 * (j - k) : ℕ) * ((2 * (j - (k + 1)) + 1).factorial : ℝ) := by
      rw [hN,Nat.factorial_succ,Nat.cast_mul]
    have hDen : 0 < ((2 * (j - k)).factorial : ℝ) := by positivity
    apply nonneg_of_mul_nonneg_left _ hDen
    have hE : (A * (1 / ((2 * (j - (k + 1)) + 1).factorial : ℝ)) -
        B * (1 / ((2 * (j - k)).factorial : ℝ))) * ((2 * (j - k)).factorial : ℝ) =
          A * (2 * (j - k) : ℕ) - B := by
      rw [sub_mul]
      congr 1
      · rw [hF]
        field_simp [show ((2 * (j - (k + 1)) + 1).factorial : ℝ) ≠ 0 by positivity]
      · field_simp [hDen.ne']
    rw [hE]
    exact sub_nonneg.mpr hAB
  have hB : 0 ≤ a * sinhShiftCoeff 1 1 j - 2 * coshShiftCoeff 0 j := by
    apply hTerm 0 (by omega)
    have hJ : (10 : ℝ) ≤ ((2 * (j - 0) : ℕ) : ℝ) := by exact_mod_cast (show 10 ≤ 2 * (j - 0) by omega)
    dsimp only [a]
    linarith only [hJ]
  have hC : 0 ≤ a * (b + q) * sinhShiftCoeff 1 2 j - 4 * b * coshShiftCoeff 1 j := by
    apply hTerm 1 (by omega)
    have hJ : (8 : ℝ) ≤ ((2 * (j - 1) : ℕ) : ℝ) := by exact_mod_cast (show 8 ≤ 2 * (j - 1) by omega)
    dsimp only [a,b,q]
    linarith only [hJ]
  have hD : 0 ≤ a * b * q * sinhShiftCoeff 1 3 j - 2 * b * q * coshShiftCoeff 2 j := by
    apply hTerm 2 (by omega)
    have hJ : (6 : ℝ) ≤ ((2 * (j - 2) : ℕ) : ℝ) := by exact_mod_cast (show 6 ≤ 2 * (j - 2) by omega)
    dsimp only [a,b,q]
    linarith only [hJ]
  have hA : 0 ≤ (2 / β) * (sinhShiftCoeff β 0 j + 2 * q * sinhShiftCoeff β 1 j + q ^ 2 * sinhShiftCoeff β 2 j) := by
    exact mul_nonneg (by unfold β; positivity)
      (add_nonneg (add_nonneg (hS 0) (mul_nonneg (by unfold q; positivity) (hS 1))) (mul_nonneg (sq_nonneg q) (hS 2)))
  exact add_nonneg (add_nonneg (add_nonneg hA hB) hC) hD

theorem pressureGapResidual_pos {v : ℝ} (hv : 0 < v) (hV : v ^ 2 ≤ 2) : 0 < pressureGapResidual v := by
  have h := (hasSum_nat_add_iff' 5).mpr (gapResidual_hasSum v)
  have hTail : 0 ≤ pressureGapResidual v - ∑ j ∈ Finset.range 5, gapCoeff j * v ^ (2 * j + 1) := by
    rw [← h.tsum_eq]
    exact tsum_nonneg fun j => mul_nonneg (gapCoeff_tail_nonneg (by omega)) (by positivity)
  have h0 : gapCoeff 0 = 0 := by norm_num [gapCoeff,sinhShiftCoeff,coshShiftCoeff,Nat.factorial]
  have h1 : gapCoeff 1 = 0 := by norm_num [gapCoeff,sinhShiftCoeff,coshShiftCoeff,Nat.factorial]
  have h2 : (3 / 240 : ℝ) < gapCoeff 2 := by norm_num [gapCoeff,sinhShiftCoeff,coshShiftCoeff,Nat.factorial]
  have h3 : (-17 / 5040 : ℝ) < gapCoeff 3 := by norm_num [gapCoeff,sinhShiftCoeff,coshShiftCoeff,Nat.factorial]
  have h4 : 0 ≤ gapCoeff 4 := by norm_num [gapCoeff,sinhShiftCoeff,coshShiftCoeff,Nat.factorial]
  norm_num [Finset.sum_range_succ,h0,h1] at hTail
  have hP : 0 < v ^ 5 := by positivity
  have h5 := mul_lt_mul_of_pos_right h2 hP
  have h7 := mul_lt_mul_of_pos_right h3 (show 0 < v ^ 7 by positivity)
  have h9 := mul_nonneg h4 (show 0 ≤ v ^ 9 by positivity)
  have hE := mul_le_mul_of_nonneg_left hV hP.le
  nlinarith only [hTail,h5,h7,h9,hE,hP]

end ACS12.Pressure


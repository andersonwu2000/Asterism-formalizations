import ACS12.PressureCanonicalGapG

/-! The complete cosh tail and the original canonical D upper. -/
namespace ACS12.Pressure

noncomputable def canonicalGapD (v : ℝ) : ℝ :=
  Real.cosh ((5 / 9) * v) - Real.cosh ((4 / 9) * v) ^ (5 / 14 : ℝ)

noncomputable def canonicalGapUpper (v : ℝ) : ℝ :=
  (5 / 42) * v ^ 2 * (1 + (37877 / 1000188 - 1 / 90) * v ^ 2) / (1 - v ^ 2 / 90)

private noncomputable def differenceCoeff (k : ℕ) : ℝ :=
  ((25 / 81 : ℝ) ^ k - (100 / 3969 : ℝ) ^ k) / ((2 * k).factorial : ℝ)

private theorem differenceCoeff_nonneg (k : ℕ) : 0 ≤ differenceCoeff k :=
  div_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) (by norm_num) k)) (by positivity)

private theorem differenceCoeff_ratio {k : ℕ} (hk : 2 ≤ k) :
    differenceCoeff (k + 1) ≤ (1 / 90) * differenceCoeff k := by
  rcases hk.eq_or_lt with h | h
  · rw [← h]
    norm_num [differenceCoeff,Nat.factorial]
  let C : ℝ := 25 / 81
  let D : ℝ := 100 / 3969
  have hC : 0 < C := by norm_num [C]
  have hD : 0 ≤ D := by norm_num [D]
  have hCD : D ≤ C * (1 / 10) := by norm_num [C,D]
  have hK : (1 / 10 : ℝ) ^ k ≤ 1 / 10 := by
    simpa only [pow_one] using pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 10) (by norm_num)
      (show 1 ≤ k by omega)
  have hPow : D ^ k ≤ C ^ k * (1 / 10) := by
    have h' := pow_le_pow_left₀ hD hCD k
    rw [mul_pow] at h'
    exact h'.trans (mul_le_mul_of_nonneg_left hK (by positivity))
  let f : ℝ := ((2 * k).factorial : ℝ)
  let b : ℝ := ((2 * k + 2 : ℕ) : ℝ) * ((2 * k + 1 : ℕ) : ℝ)
  have hf : 0 < f := by unfold f; positivity
  have hb : 56 ≤ b := by
    have ha : (8 : ℝ) ≤ ((2 * k + 2 : ℕ) : ℝ) := by exact_mod_cast (show 8 ≤ 2 * k + 2 by omega)
    have hB : (7 : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) := by exact_mod_cast (show 7 ≤ 2 * k + 1 by omega)
    have h := mul_le_mul ha hB (by norm_num : (0 : ℝ) ≤ 7) (by positivity)
    norm_num only [show (8 : ℝ) * 7 = 56 by norm_num] at h
    exact h
  have hFact : ((2 * (k + 1)).factorial : ℝ) = b * f := by
    unfold b f
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega,Nat.factorial_succ,Nat.factorial_succ]
    push_cast
    ring
  change (C ^ (k + 1) - D ^ (k + 1)) / ((2 * (k + 1)).factorial : ℝ) ≤
    (1 / 90) * ((C ^ k - D ^ k) / f)
  rw [hFact]
  have hb₀ : 0 < b := by linarith only [hb]
  have hCk : 0 ≤ C ^ k := by positivity
  have hX : C * C ^ k ≤ (b / 90) * ((9 / 10) * C ^ k) := by
    have h : C ≤ b / 90 * (9 / 10) := by unfold C; linarith only [hb]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right h hCk
  have hY := mul_le_mul_of_nonneg_left (show (9 / 10) * C ^ k ≤ C ^ k - D ^ k by linarith only [hPow])
    (show 0 ≤ b / 90 by positivity)
  have hZ : C ^ (k + 1) - D ^ (k + 1) ≤ (b / 90) * (C ^ k - D ^ k) := by
    rw [pow_succ' C]
    exact (sub_le_self _ (pow_nonneg hD _)).trans (hX.trans hY)
  have h' := (div_le_iff₀ hb₀).mpr (by nlinarith only [hZ] :
    C ^ (k + 1) - D ^ (k + 1) ≤ (1 / 90) * (C ^ k - D ^ k) * b)
  have h'' := div_le_div_of_nonneg_right h' hf.le
  simpa only [div_div,mul_div_assoc] using h''

private theorem difference_hasSum (v : ℝ) :
    HasSum (fun k => differenceCoeff k * v ^ (2 * k))
      (Real.cosh ((5 / 9) * v) - Real.cosh ((10 / 63) * v)) := by
  convert (Real.hasSum_cosh ((5 / 9) * v)).sub (Real.hasSum_cosh ((10 / 63) * v)) using 1
  funext k
  simp only [differenceCoeff,mul_pow,pow_mul]
  norm_num
  ring

private theorem difference_upper {v : ℝ} (hV : v ^ 2 ≤ 2) :
    Real.cosh ((5 / 9) * v) - Real.cosh ((10 / 63) * v) ≤
      (125 / 882) * v ^ 2 * (1 + (1325 / 47628) * v ^ 2 / (1 - v ^ 2 / 90)) := by
  let w := v ^ 2
  let q : ℝ := 1 / 90
  have hw : 0 ≤ w := sq_nonneg _
  have hq : 0 ≤ q := by norm_num [q]
  have hW : w * q < 1 := by dsimp only [w,q]; linarith only [hV]
  have hD₀ : differenceCoeff 0 = 0 := by norm_num [differenceCoeff]
  have hD₁ : differenceCoeff 1 = 125 / 882 := by norm_num [differenceCoeff,Nat.factorial]
  have hD₂ : differenceCoeff 2 = (125 / 882) * (1325 / 47628) := by norm_num [differenceCoeff,Nat.factorial]
  have hI (n : ℕ) : differenceCoeff (n + 2) ≤ differenceCoeff 2 * q ^ n := by
    induction n with
    | zero => simp only [Nat.zero_add,pow_zero,mul_one,le_rfl]
    | succ n ih =>
      have h := differenceCoeff_ratio (show 2 ≤ n + 2 by omega)
      rw [show n.succ + 2 = (n + 2) + 1 by omega,pow_succ]
      exact h.trans (by simpa only [mul_assoc,mul_comm,mul_left_comm] using mul_le_mul_of_nonneg_left ih hq)
  have h := (hasSum_nat_add_iff' 2).mpr (difference_hasSum v)
  have hG := (hasSum_geometric_of_lt_one (show 0 ≤ w * q by positivity) hW).mul_left
    (differenceCoeff 2 * w ^ 2)
  have hT : ∀ n : ℕ, differenceCoeff (n + 2) * v ^ (2 * (n + 2)) ≤
      differenceCoeff 2 * w ^ 2 * (w * q) ^ n := by
    intro n
    rw [pow_mul,← show w = v ^ 2 from rfl,pow_add,mul_pow]
    have h' := mul_le_mul_of_nonneg_right (hI n) (show 0 ≤ w ^ n * w ^ 2 by positivity)
    convert h' using 1
    ring
  have hPrice := h.summable.tsum_le_tsum hT hG.summable
  rw [h.tsum_eq,hG.tsum_eq] at hPrice
  norm_num [Finset.sum_range_succ,hD₀,hD₁] at hPrice
  rw [hD₂] at hPrice
  dsimp only [w,q] at hPrice
  have hEq : (125 / 882 : ℝ) * v ^ 2 + (125 / 882 * (1325 / 47628) * (v ^ 2) ^ 2) *
      (1 - v ^ 2 * (1 / 90))⁻¹ =
      (125 / 882) * v ^ 2 * (1 + (1325 / 47628) * v ^ 2 / (1 - v ^ 2 / 90)) := by
    rw [show v ^ 2 * (1 / 90 : ℝ) = v ^ 2 / 90 by ring]
    ring
  rw [← hEq]
  linarith only [hPrice]

theorem canonicalGapD_le_upper {v : ℝ} (hv : 0 ≤ v) (hV : v ^ 2 ≤ 2) :
    canonicalGapD v ≤ canonicalGapUpper v := by
  have hScale : ((4 / 9) * v) ^ 2 ≤ 2 := by nlinarith only [hV]
  have hG := canonicalGapG_weak (show 0 ≤ (4 / 9) * v by positivity) hScale
  have hD := difference_upper hV
  have hE : canonicalGapD v =
      Real.cosh ((5 / 9) * v) - Real.cosh ((10 / 63) * v) - canonicalGapG ((4 / 9) * v) := by
    unfold canonicalGapD canonicalGapG
    rw [show (5 / 14 : ℝ) * ((4 / 9) * v) = (10 / 63) * v by ring]
    ring
  rw [hE]
  apply (sub_le_sub hD hG).trans
  have h₁ : 0 < 1 - v ^ 2 / 90 := by linarith only [hV]
  have h₂ : 0 < 1 + (11 / 441) * v ^ 2 := by positivity
  have hEq : (45 / 392 : ℝ) * ((4 / 9) * v) ^ 2 / (1 + (99 / 784) * ((4 / 9) * v) ^ 2) =
      (10 / 441) * v ^ 2 / (1 + (11 / 441) * v ^ 2) := by ring
  rw [hEq]
  have hG' : (1 - v ^ 2 / 90) ≤ 1 + (11 / 441) * v ^ 2 := by nlinarith only [sq_nonneg v]
  have hI := div_le_div_of_nonneg_left (show 0 ≤ (10 / 441 : ℝ) * (11 / 441) * v ^ 4 by positivity) h₁ hG'
  unfold canonicalGapUpper
  have hA : (125 / 882 : ℝ) * v ^ 2 * (1 + (1325 / 47628) * v ^ 2 / (1 - v ^ 2 / 90)) -
      (10 / 441) * v ^ 2 / (1 + (11 / 441) * v ^ 2) =
        (5 / 42) * v ^ 2 + (125 / 882) * (1325 / 47628) * v ^ 4 / (1 - v ^ 2 / 90) +
          (10 / 441) * (11 / 441) * v ^ 4 / (1 + (11 / 441) * v ^ 2) := by
    field_simp [h₁.ne',h₂.ne']
    ring
  rw [hA]
  have hB : (5 / 42 : ℝ) * v ^ 2 * (1 + (37877 / 1000188 - 1 / 90) * v ^ 2) / (1 - v ^ 2 / 90) =
      (5 / 42) * v ^ 2 + (125 / 882) * (1325 / 47628) * v ^ 4 / (1 - v ^ 2 / 90) +
        (10 / 441) * (11 / 441) * v ^ 4 / (1 - v ^ 2 / 90) := by
    have h : (90 : ℝ) - v ^ 2 ≠ 0 := ne_of_gt (by linarith only [hV])
    field_simp [h₁.ne',h]
    ring
  rw [hB]
  exact add_le_add_right hI _

end ACS12.Pressure


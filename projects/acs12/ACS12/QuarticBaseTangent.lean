import ACS12.QuarticRootComparison
import Mathlib.Analysis.Convex.Deriv

/-! The quartic base under the one-quarter mass cap. -/
namespace ACS12.NativeCells

open Finset hiding Icc
open Set

noncomputable section

def quarticPolyLog (y : ℝ) : ℝ :=
  Real.log (1 - y ^ 2) + Real.log (1 + 11 * y ^ 2)

private def quarticPolyFirst (y : ℝ) : ℝ :=
  quarticPolyLog y - 2 * y ^ 2 / (1 - y ^ 2) + 22 * y ^ 2 / (1 + 11 * y ^ 2)

private def quarticPolySecond (y : ℝ) : ℝ :=
  22 * y * (3 + 11 * y ^ 2) / (1 + 11 * y ^ 2) ^ 2 -
    2 * y * (3 - y ^ 2) / (1 - y ^ 2) ^ 2

private theorem cap_square_bound {y : ℝ} (hy : y ∈ Icc 0 (1 / 4)) :
    y ^ 2 ≤ (1 / 4 : ℝ) ^ 2 :=
  pow_le_pow_left₀ hy.1 hy.2 2

private theorem cap_factors_pos {y : ℝ} (hy : y ∈ Icc 0 (1 / 4)) :
    0 < 1 - y ^ 2 ∧ 0 < 1 + 11 * y ^ 2 := by
  exact ⟨by nlinarith only [cap_square_bound hy], by positivity⟩

theorem quarticPolyLog_deriv {y : ℝ} (hy : y ∈ Icc 0 (1 / 4)) :
    HasDerivAt quarticPolyLog
      (-2 * y / (1 - y ^ 2) + 22 * y / (1 + 11 * y ^ 2)) y := by
  obtain ⟨h₁, h₂⟩ := cap_factors_pos hy
  have hsq := hasDerivAt_pow 2 y
  unfold quarticPolyLog
  convert (hsq.const_sub 1 |>.log h₁.ne').add
    ((hsq.const_mul 11).const_add 1 |>.log h₂.ne') using 1
  norm_num
  ring

private theorem quarticPoly_deriv {y : ℝ} (hy : y ∈ Icc 0 (1 / 4)) :
    HasDerivAt (fun y => y * quarticPolyLog y) (quarticPolyFirst y) y := by
  unfold quarticPolyFirst
  convert (hasDerivAt_id y).mul (quarticPolyLog_deriv hy) using 1
  simp only [id_eq, one_mul, div_eq_mul_inv]
  ring

private theorem quarticPolyFirst_deriv {y : ℝ} (hy : y ∈ Icc 0 (1 / 4)) :
    HasDerivAt quarticPolyFirst (quarticPolySecond y) y := by
  obtain ⟨h₁, h₂⟩ := cap_factors_pos hy
  have hsq := hasDerivAt_pow 2 y
  have hm := (hsq.const_mul 2).div (hsq.const_sub 1) h₁.ne'
  have hp := (hsq.const_mul 22).div ((hsq.const_mul 11).const_add 1) h₂.ne'
  unfold quarticPolyFirst quarticPolySecond
  convert (((quarticPolyLog_deriv hy).sub hm).add hp) using 1
  norm_num
  field_simp [h₁.ne', h₂.ne']
  ring

private theorem quartic_quintic_pos {y : ℝ} (hy : 0 ≤ y) :
    0 < 3630 * y ^ 5 + 3751 * y ^ 4 - 550 * y ^ 3 + 682 * y ^ 2 - 300 * y + 31 := by
  have h :
       3630 * y ^ 5 + 3751 * y ^ 4 - 550 * y ^ 3 + 682 * y ^ 2 - 300 * y + 31 =
         14923 / 29282 + 600 * (y - 2 / 11 + 7 / 2420) ^ 2 +
           (y - 2 / 11) ^ 2 * (3630 * y ^ 3 + 5071 * y ^ 2 + 1174 * y + 3754 / 11) := by
    ring
  rw [h]
  positivity

private theorem quarticPolySecond_le {y : ℝ} (hy : y ∈ Icc 0 (1 / 4)) :
    quarticPolySecond y ≤ 31 / 5 := by
  obtain ⟨h₁, h₂⟩ := cap_factors_pos hy
  have hminus : 6 * y ≤ 2 * y * (3 - y ^ 2) / (1 - y ^ 2) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos h₁)).mpr
    have h := mul_nonneg (show 0 ≤ 2 * y ^ 3 by have := hy.1; positivity)
      (show 0 ≤ 5 - 3 * y ^ 2 by nlinarith only [cap_square_bound hy])
    nlinarith only [h]
  have hplus : 22 * y * (3 + 11 * y ^ 2) / (1 + 11 * y ^ 2) ^ 2 < 31 / 5 + 6 * y := by
    apply (div_lt_iff₀ (sq_pos_of_pos h₂)).mpr
    nlinarith only [quartic_quintic_pos hy.1]
  unfold quarticPolySecond
  linarith only [hminus, hplus]

private def quarticPolyAdjusted (x y : ℝ) : ℝ :=
  y * quarticPolyLog y - (31 / 10) * (y - x) ^ 2

private theorem quarticPolyAdjusted_concave (x : ℝ) :
    ConcaveOn ℝ (Icc 0 (1 / 4)) (quarticPolyAdjusted x) := by
  let D (y : ℝ) := quarticPolyFirst y - (31 / 5) * (y - x)
  let DD (y : ℝ) := quarticPolySecond y - 31 / 5
  have hd (y : ℝ) (hy : y ∈ Icc 0 (1 / 4)) :
      HasDerivAt (quarticPolyAdjusted x) (D y) y := by
    unfold quarticPolyAdjusted D
    convert (quarticPoly_deriv hy).sub
      ((((hasDerivAt_id y).sub_const x).pow 2).const_mul (31 / 10)) using 1
    norm_num
    ring
  have hdd (y : ℝ) (hy : y ∈ Icc 0 (1 / 4)) : HasDerivAt D (DD y) y := by
    unfold D DD
    simpa using (quarticPolyFirst_deriv hy).sub
      (((hasDerivAt_id y).sub_const x).const_mul (31 / 5))
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _) (f' := D) (f'' := DD)
  · exact fun y hy => (hd y hy).continuousAt.continuousWithinAt
  · exact fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt
  · exact fun y hy => (hdd y (interior_subset hy)).hasDerivWithinAt
  · exact fun y hy => sub_nonpos.mpr (quarticPolySecond_le (interior_subset hy))

theorem quartic_log_row_inverse {y : ℝ} (hy : 0 < y) (hy4 : y ≤ 1 / 4) :
    Real.log (analyticRow 4 y⁻¹) =
      quarticPolyLog y - Real.log 45 - 4 * Real.log y := by
  obtain ⟨h₁, h₂⟩ := cap_factors_pos ⟨hy.le, hy4⟩
  have hY : 1 < y⁻¹ := (one_lt_inv₀ hy).mpr (by linarith)
  have hPower : (y⁻¹ ^ 4 + 10 * y⁻¹ ^ 2 - 11) / 45 =
      (1 - y ^ 2) * (1 + 11 * y ^ 2) / (45 * y ^ 4) := by
    field_simp [hy.ne']
    ring
  rw [analyticRow_four_eq hY, hPower,
    Real.log_div (mul_pos h₁ h₂).ne' (by positivity : 45 * y ^ 4 ≠ 0),
    Real.log_mul h₁.ne' h₂.ne', Real.log_mul (by norm_num : (45 : ℝ) ≠ 0) (pow_ne_zero 4 hy.ne'),
    Real.log_pow]
  unfold quarticPolyLog
  ring

/-- The quartic base pays the entropy less reverse entropy and the quadratic
variance debit, by the mass tangent on the full one-quarter cap. -/
theorem quarticBase_lower {n : ℕ} (hn : 5 ≤ n) {w : Fin n → ℝ}
    (hw : ∀ i, 0 < w i) (hcap : ∀ i, w i ≤ 1 / 4) (hW : ∑ i, w i = 1) :
    ((∑ i, let u := (n : ℝ) * w i
      3 * (u * Real.log u - u + 1) - (u - 1 - Real.log u) -
        (31 / 10) * (u - 1) ^ 2 / (n : ℝ)) / (n : ℝ)) ≤ quarticBase w := by
  let x : ℝ := (n : ℝ)⁻¹
  have hN : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hN5 : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hx : 0 < x := inv_pos.mpr hN
  have hx4 : x ≤ 1 / 4 := by
    unfold x
    rw [inv_eq_one_div, div_le_iff₀ hN]
    linarith
  have hX : ∑ _ : Fin n, x = 1 := by
    simp only [x, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_inv_cancel₀ hN.ne']
  have hMean : (∑ i, x * w i) = x := by rw [← mul_sum, hW, mul_one]
  have hJ := (quarticPolyAdjusted_concave x).le_map_sum
    (t := (univ : Finset (Fin n))) (w := fun _ => x) (p := w)
    (fun _ _ => hx.le) hX (fun i _ => ⟨(hw i).le, hcap i⟩)
  simp only [smul_eq_mul, hMean] at hJ
  rw [← mul_sum, show quarticPolyAdjusted x x = x * quarticPolyLog x by
    simp [quarticPolyAdjusted]] at hJ
  have hCorr := (mul_le_mul_iff_of_pos_left hx).mp hJ
  have hRegLog : Real.log (analyticRow 4 (n : ℝ)) =
      quarticPolyLog x - Real.log 45 + 4 * Real.log (n : ℝ) := by
    have h := quartic_log_row_inverse hx hx4
    simp only [x, inv_inv, Real.log_inv] at h ⊢
    linarith only [h]
  let f (i : Fin n) : ℝ :=
    let u := (n : ℝ) * w i
    3 * (u * Real.log u - u + 1) - (u - 1 - Real.log u) -
      (31 / 10) * (u - 1) ^ 2 / (n : ℝ)
  let d (i : Fin n) : ℝ := w i * (Real.log (w i) + Real.log (analyticRow 4 (w i)⁻¹))
  have hf (i : Fin n) :
      f i / (n : ℝ) + d i =
        x * Real.log (w i) + (3 * w i * Real.log (n : ℝ) + x * Real.log (n : ℝ)) -
          w i * Real.log 45 - 4 * (w i - x) + quarticPolyAdjusted x (w i) := by
    simp only [f, d, x, quarticPolyAdjusted, quartic_log_row_inverse (hw i) (hcap i),
      Real.log_mul hN.ne' (hw i).ne']
    field_simp [hN.ne']
    ring
  have hSum : (∑ i, f i) / (n : ℝ) + ∑ i, d i =
      (∑ i, Real.log (w i)) / (n : ℝ) + 4 * Real.log (n : ℝ) - Real.log 45 +
        ∑ i, quarticPolyAdjusted x (w i) := by
    have hLogX : (∑ _ : Fin n, x * Real.log (n : ℝ)) = Real.log (n : ℝ) := by
      rw [← sum_mul, hX, one_mul]
    have hCentered : (∑ i, (w i - x)) = 0 := by
      rw [sum_sub_distrib, hW, hX, sub_self]
    rw [sum_div, ← sum_add_distrib, sum_congr rfl (fun i _ => hf i)]
    simp only [sum_add_distrib, sum_sub_distrib, hLogX]
    simp only [← mul_sum, ← sum_mul, hW, hCentered, one_mul, mul_zero, sub_zero]
    dsimp only [x]
    rw [div_eq_inv_mul]
    ring
  change (∑ i, f i) / (n : ℝ) ≤ quarticBase w
  unfold quarticBase
  rw [hRegLog]
  change (∑ i, f i) / (n : ℝ) ≤
    quarticPolyLog x - Real.log 45 + 4 * Real.log (n : ℝ) +
      (∑ i, Real.log (w i)) / (n : ℝ) - ∑ i, d i
  linarith only [hCorr, hSum]

end

end ACS12.NativeCells

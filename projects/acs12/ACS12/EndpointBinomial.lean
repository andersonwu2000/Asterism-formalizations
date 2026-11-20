import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-! A rational polynomial enclosure of a negative real power. -/
namespace ACS12

open Set Finset

def risingCoefficient {K : Type*} [Field K] (a : K) : ℕ → K
  | 0 => 1
  | n + 1 => risingCoefficient a n * ((a + n) / (n + 1))

theorem risingCoefficient_nonneg {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    0 ≤ risingCoefficient a n := by
  induction n with
  | zero => exact zero_le_one
  | succ n ih =>
    rw [risingCoefficient]
    positivity

private theorem risingCoefficient_eq_multichoose (a : ℝ) (n : ℕ) :
    risingCoefficient a n = Ring.multichoose a n := by
  have h (k : ℕ) :
      (k.factorial : ℝ) * Ring.multichoose a k = (ascPochhammer ℕ k).smeval a := by
    rw [← nsmul_eq_mul]
    exact Ring.factorial_nsmul_multichoose_eq_ascPochhammer a k
  induction n with
  | zero => simp [risingCoefficient,Ring.multichoose_zero_right]
  | succ n ih =>
    rw [risingCoefficient,ih]
    have hP := h (n + 1)
    rw [ascPochhammer_succ_right,Polynomial.smeval_mul,Polynomial.smeval_add,
      Polynomial.smeval_X,Polynomial.smeval_natCast,← h n,Nat.factorial_succ,Nat.cast_mul] at hP
    have hn : (n.factorial : ℝ) ≠ 0 := by positivity
    have hn' : (↑n : ℝ) + 1 ≠ 0 := by positivity
    push_cast at hP
    simp only [pow_one,pow_zero,nsmul_eq_mul,mul_one] at hP
    rw [← mul_div_assoc]
    apply (div_eq_iff hn').mpr
    apply mul_left_cancel₀ hn
    linear_combination -hP

private theorem binomial_negative_hasSum {a w : ℝ} (hw : 0 ≤ w) (hw₁ : w < 1) :
    HasSum (fun n : ℕ => risingCoefficient a n * w ^ n) ((1 - w) ^ (-a)) := by
  have hB : w ∈ Metric.eball (0 : ℝ) 1 := by
    rw [← ENNReal.ofReal_one,Metric.eball_ofReal,Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg hw]
    exact hw₁
  have h := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero a).hasSum_sub hB
  simpa only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,Finset.prod_const,Finset.card_univ,
    Fintype.card_fin,FormalMultilinearSeries.coeff_ofScalars,smul_eq_mul,mul_comm,
    ← Ring.multichoose_eq,risingCoefficient_eq_multichoose,Real.rpow_neg (sub_nonneg.mpr hw₁.le),
    one_div,sub_zero] using h

theorem binomial_four_enclosure {a w wMax r : ℝ} (ha : 0 < a) (hw : 0 ≤ w) (hW : w ≤ wMax)
    (hr : 0 ≤ r) (hr₁ : r < 1) (hwR : wMax ≤ r)
    (hRatio : wMax * ((a + 5) / 6) ≤ r) :
    let P := ∑ j ∈ range 5, risingCoefficient a j * w ^ j
    P ≤ (1 - w) ^ (-a) ∧ (1 - w) ^ (-a) ≤
      P + risingCoefficient a 5 * w ^ 5 / (1 - r) := by
  let f (j : ℕ) := risingCoefficient a j * w ^ j
  let g (n : ℕ) := f 5 * r ^ n
  have hW₀ : 0 ≤ wMax := hw.trans hW
  have hf (n : ℕ) : 0 ≤ f n := mul_nonneg (risingCoefficient_nonneg ha.le n) (by positivity)
  have hF := binomial_negative_hasSum (a := a) hw (hW.trans_lt (hwR.trans_lt hr₁))
  have hG := (summable_geometric_of_lt_one hr hr₁).mul_left (f 5)
  have hStep (n : ℕ) : f (n + 5 + 1) ≤ f (n + 5) * r := by
    have h : w * ((a + (n : ℝ) + 5) / ((n : ℝ) + 6)) ≤ r := by
      have hR := (div_le_iff₀ (by norm_num : (0 : ℝ) < 6)).mp
        (show wMax * (a + 5) / 6 ≤ r by rwa [mul_div_assoc])
      have hA := mul_le_mul_of_nonneg_right hW (show 0 ≤ a + (n : ℝ) + 5 by positivity)
      have hB := mul_le_mul_of_nonneg_right hwR (Nat.cast_nonneg (α := ℝ) n)
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 6)).mpr
      nlinarith only [hR,hA,hB]
    have h' := mul_le_mul_of_nonneg_left h (hf (n + 5))
    unfold f at h' ⊢
    rw [risingCoefficient,pow_succ]
    push_cast
    convert h' using 1 <;> ring
  have hTerm (n : ℕ) : f (n + 5) ≤ g n := by
    induction n with
    | zero => simp [g]
    | succ n ih =>
      rw [show n + 1 + 5 = n + 5 + 1 by omega]
      exact (hStep n).trans (by simpa only [g,pow_succ,mul_assoc] using mul_le_mul_of_nonneg_right ih hr)
  change (∑ j ∈ range 5, f j) ≤ _ ∧ _ ≤ (∑ j ∈ range 5, f j) + f 5 / (1 - r)
  have hSplit := hF.summable.sum_add_tsum_nat_add 5
  rw [hF.tsum_eq] at hSplit
  have hTail := (hF.summable.comp_injective (fun _ _ e => Nat.add_right_cancel e)).tsum_le_tsum hTerm hG
  unfold g at hTail
  rw [tsum_mul_left,tsum_geometric_of_lt_one hr hr₁,← div_eq_mul_inv] at hTail
  have hTail₀ : 0 ≤ ∑' n : ℕ, f (n + 5) := tsum_nonneg (fun n => hf (n + 5))
  exact ⟨by linarith only [hSplit,hTail₀],by linarith only [hSplit,hTail]⟩

theorem scaled_binomial_four_enclosure {a x M wMax r L H : ℝ}
    (ha : 0 < a) (hx : 0 < x) (hM : 0 < M) (hxM : x ≤ M)
    (hW : 1 - x / M ≤ wMax) (hr : 0 ≤ r) (hr₁ : r < 1)
    (hwR : wMax ≤ r) (hRatio : wMax * ((a + 5) / 6) ≤ r)
    (hL : L ≤ M ^ (-a)) (hH : M ^ (-a) ≤ H) :
    let w := 1 - x / M
    let P := ∑ j ∈ range 5, risingCoefficient a j * w ^ j
    L * P ≤ x ^ (-a) ∧ x ^ (-a) ≤ H * (P + risingCoefficient a 5 * w ^ 5 / (1 - r)) := by
  let w := 1 - x / M
  let P := ∑ j ∈ range 5, risingCoefficient a j * w ^ j
  have hw : 0 ≤ w := sub_nonneg.mpr ((div_le_one hM).mpr hxM)
  have hP : 0 ≤ P := sum_nonneg fun j _ => mul_nonneg (risingCoefficient_nonneg ha.le j) (by positivity)
  have hR : 0 ≤ risingCoefficient a 5 * w ^ 5 / (1 - r) :=
    div_nonneg (mul_nonneg (risingCoefficient_nonneg ha.le 5) (by positivity)) (sub_nonneg.mpr hr₁.le)
  have hMpow := Real.rpow_nonneg hM.le (-a)
  obtain ⟨hLower,hUpper⟩ := binomial_four_enclosure ha hw hW hr hr₁ hwR hRatio
  change P ≤ (1 - w) ^ (-a) at hLower
  change (1 - w) ^ (-a) ≤ P + risingCoefficient a 5 * w ^ 5 / (1 - r) at hUpper
  have hScale : x ^ (-a) = M ^ (-a) * (1 - w) ^ (-a) := by
    have hEq : 1 - w = x / M := by unfold w; ring
    have hX : x = M * (1 - w) := by rw [hEq,mul_div_cancel₀ _ hM.ne']
    conv_lhs => rw [hX,Real.mul_rpow hM.le (hEq ▸ div_nonneg hx.le hM.le)]
  rw [hScale]
  exact ⟨(mul_le_mul_of_nonneg_right hL hP).trans (mul_le_mul_of_nonneg_left hLower hMpow),
    (mul_le_mul_of_nonneg_left hUpper hMpow).trans
      (mul_le_mul_of_nonneg_right hH (add_nonneg hP hR))⟩

end ACS12

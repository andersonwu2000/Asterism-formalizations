import ACS12.QuarticRootComparison

namespace ACS12.NativeCells

noncomputable def quarticEntropy {n : ℕ} (w : Fin n → ℝ) : ℝ :=
  (∑ i, let u := (n:ℝ)*w i; u*Real.log u-u+1)/(n:ℝ)
noncomputable def quarticReverseEntropy {n : ℕ} (w : Fin n → ℝ) : ℝ :=
  -(∑ i,Real.log ((n:ℝ)*w i))/(n:ℝ)
noncomputable def quarticWidthVariance {n : ℕ} (w : Fin n → ℝ) : ℝ :=
  (∑ i,(w i-1/(n:ℝ))^2)/(n:ℝ)
noncomputable def quarticDebitA {n : ℕ} (w : Fin n → ℝ) : ℝ :=
  7*quarticReverseEntropy w+(23/2)*quarticWidthVariance w
noncomputable def quarticDebitB {n : ℕ} (w : Fin n → ℝ) : ℝ :=
  quarticReverseEntropy w+2*quarticWidthVariance w

theorem quarticReverseEntropy_eq {n : ℕ} {w : Fin n → ℝ} (hW : ∑ i,w i=1) :
    quarticReverseEntropy w = (∑ i : Fin n, ((n:ℝ)*w i-1-Real.log ((n:ℝ)*w i)))/(n:ℝ) := by
  unfold quarticReverseEntropy
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum,hW,mul_one,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,sub_self,zero_sub]

theorem quarticDebit_nonneg {n : ℕ} (hn : 1 ≤ n) {w : Fin n → ℝ}
    (hw : ∀ i,0<w i) (hW : ∑ i,w i=1) :
    0 ≤ quarticDebitA w ∧ 0 ≤ quarticDebitB w ∧ quarticDebitB w ≤ 4*quarticDebitA w/23 := by
  have hN : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  have hR : 0 ≤ quarticReverseEntropy w := by
    rw [quarticReverseEntropy_eq hW]
    apply div_nonneg (Finset.sum_nonneg _) hN.le
    intro i _
    linarith [Real.log_le_sub_one_of_pos (mul_pos hN (hw i))]
  have hV : 0 ≤ quarticWidthVariance w := by unfold quarticWidthVariance; positivity
  unfold quarticDebitA quarticDebitB
  constructor
  · positivity
  constructor
  · positivity
  · nlinarith

end ACS12.NativeCells

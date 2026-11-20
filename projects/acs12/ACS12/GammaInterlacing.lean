import ACS12.GammaOrder

/-! Positive partial fractions for the finite original Gamma Euler products. -/
namespace ACS12.GammaMeasure

noncomputable def interlacingProduct (a b : ℕ → ℝ) (N : ℕ) (z : ℝ) : ℝ :=
  ∏ i ∈ Finset.range N, (1 + z / a i) / (1 + z / b i)

noncomputable def interlacingWeight (a b : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | N + 1, i =>
    let c := b N / a N - 1
    if i < N then interlacingWeight a b N i * (1 - c * b i / (b N - b i))
    else if i = N then c * (1 + ∑ j ∈ Finset.range N, interlacingWeight a b N j * (b N / (b N - b j)))
    else 0

private theorem interlacing_factor {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {z : ℝ} (hz : z + b ≠ 0) :
    (1 + z / a) / (1 + z / b) = 1 + (b / a - 1) * (z / (z + b)) := by
  have hNorm {t : ℝ} (ht : 0 < t) : 1 + z / t = (z + t) / t := by
    field_simp [ht.ne']
    ring
  rw [hNorm ha,hNorm hb]
  field_simp [ha.ne',hb.ne',hz]
  ring

private theorem interlacing_product_term {a b z : ℝ} (hab : a < b) (h₁ : z + a ≠ 0) (h₂ : z + b ≠ 0) (c : ℝ) :
    z / (z + a) * (1 + c * (z / (z + b))) =
      (1 - c * a / (b - a)) * (z / (z + a)) + (c * (b / (b - a))) * (z / (z + b)) := by
  field_simp [h₁,h₂,(sub_pos.mpr hab).ne']
  ring

private theorem interlacing_coefficient_pos {a b t : ℝ} (ha : 0 < a) (hab : a < b) (ht : t < a) :
    0 < 1 - (b / a - 1) * t / (b - t) := by
  have hb := ha.trans hab
  have hbt := sub_pos.mpr (ht.trans hab)
  have hEq : 1 - (b / a - 1) * t / (b - t) = b * (a - t) / (a * (b - t)) := by
    field_simp [ha.ne',hbt.ne']
    ring
  rw [hEq]
  exact div_pos (mul_pos hb (sub_pos.mpr ht)) (mul_pos ha hbt)

theorem interlacingWeight_pos {a b : ℕ → ℝ}
    (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i) (hba : ∀ i j, i < j → b i < a j) :
    ∀ N i, i < N → 0 < interlacingWeight a b N i := by
  intro N
  induction N with
  | zero => omega
  | succ N ih =>
    intro i hi
    rw [interlacingWeight]
    split_ifs with hiN hiEq
    · exact mul_pos (ih i hiN) (interlacing_coefficient_pos (ha N) (hab N) (hba i N hiN))
    · subst i
      refine mul_pos (sub_pos.mpr ((one_lt_div (ha N)).mpr (hab N))) (add_pos_of_pos_of_nonneg one_pos ?_)
      apply Finset.sum_nonneg
      intro j hj
      have hjN := Finset.mem_range.mp hj
      exact mul_nonneg (ih j hjN).le (div_nonneg ((ha N).trans (hab N)).le
        (sub_nonneg.mpr (((hba j N hjN).trans (hab N)).le)))
    · omega

theorem interlacingWeight_step_le {a b : ℕ → ℝ}
    (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i) (hba : ∀ i j, i < j → b i < a j)
    {N i : ℕ} (hi : i < N) :
    interlacingWeight a b (N + 1) i ≤ interlacingWeight a b N i := by
  rw [interlacingWeight]
  rw [if_pos hi]
  have hC : 0 ≤ (b N / a N - 1) * b i / (b N - b i) :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr ((le_div_iff₀ (ha N)).mpr (by linarith only [hab N])))
      ((ha i).trans (hab i)).le) (sub_nonneg.mpr (((hba i N hi).trans (hab N)).le))
  exact mul_le_of_le_one_right (interlacingWeight_pos ha hab hba N i hi).le (by linarith only [hC])

theorem interlacingProduct_eq_off_poles {a b : ℕ → ℝ}
    (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i) (hba : ∀ i j, i < j → b i < a j)
    {z : ℝ} (N : ℕ) (hz : ∀ i < N, z + b i ≠ 0) :
    interlacingProduct a b N z = 1 + ∑ i ∈ Finset.range N, interlacingWeight a b N i * (z / (z + b i)) := by
  induction N with
  | zero => simp [interlacingProduct]
  | succ N ih =>
    let c := b N / a N - 1
    let B := z / (z + b N)
    let f (i : ℕ) := z / (z + b i)
    let w := interlacingWeight a b N
    let v (i : ℕ) := w i * (1 - c * b i / (b N - b i))
    let e (i : ℕ) := w i * (b N / (b N - b i))
    have hOld : (∑ i ∈ Finset.range N, interlacingWeight a b (N + 1) i * f i) =
        ∑ i ∈ Finset.range N, v i * f i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [interlacingWeight,Finset.mem_range.mp hi,if_true,v,w,c]
    have hNew : interlacingWeight a b (N + 1) N = c * (1 + ∑ i ∈ Finset.range N, e i) := by
      simp [interlacingWeight,c,e,w]
    have hB (i : ℕ) (hi : i ∈ Finset.range N) :
        w i * f i * (1 + c * B) = v i * f i + (c * B) * e i := by
      have hiN := Finset.mem_range.mp hi
      have h₀ := interlacing_product_term ((hba i N hiN).trans (hab N))
        (hz i (by omega)) (hz N (Nat.lt_succ_self _)) c
      change f i * (1 + c * B) =
        (1 - c * b i / (b N - b i)) * f i + (c * (b N / (b N - b i))) * B at h₀
      dsimp only [v,e]
      linear_combination w i * h₀
    have hSum : (∑ i ∈ Finset.range N, w i * f i) * (1 + c * B) =
        (∑ i ∈ Finset.range N, v i * f i) + (c * B) * ∑ i ∈ Finset.range N, e i := by
      rw [Finset.sum_mul,Finset.mul_sum,← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl hB
    have hProd : interlacingProduct a b (N + 1) z =
        interlacingProduct a b N z * (1 + c * B) := by
      unfold interlacingProduct
      rw [Finset.prod_range_succ,interlacing_factor (ha N) ((ha N).trans (hab N)) (hz N (Nat.lt_succ_self _))]
    rw [hProd,ih (fun i hi => hz i (by omega)),Finset.sum_range_succ]
    change (1 + ∑ i ∈ Finset.range N, w i * f i) * (1 + c * B) =
      1 + ((∑ i ∈ Finset.range N, interlacingWeight a b (N + 1) i * f i) +
        interlacingWeight a b (N + 1) N * B)
    rw [hOld,hNew,add_mul,hSum]
    ring

theorem interlacingProduct_eq {a b : ℕ → ℝ}
    (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i) (hba : ∀ i j, i < j → b i < a j)
    {z : ℝ} (hz : 0 ≤ z) (N : ℕ) :
    interlacingProduct a b N z = 1 + ∑ i ∈ Finset.range N, interlacingWeight a b N i * (z / (z + b i)) :=
  interlacingProduct_eq_off_poles ha hab hba N (fun i _ => (add_pos_of_nonneg_of_pos hz ((ha i).trans (hab i))).ne')

end ACS12.GammaMeasure

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! The original adjacent-mass telescoping bound along a complete cyclic path. -/
namespace ACS12.Pressure

noncomputable def pathMassDistance (m : ℕ → ℝ) (k : ℕ) : ℝ :=
  m 0 + m k + 2 * ∑ j ∈ Finset.range (k - 1), m (j + 1)

theorem pathMassDistance_endpoints_le {m : ℕ → ℝ} (hm : ∀ j, 0 ≤ m j) (k : ℕ) :
    m 0 + m k ≤ pathMassDistance m k :=
  le_add_of_nonneg_right (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun j _ => hm _)))

theorem pathMassDistance_adjacent_lower {m : ℕ → ℝ} {p : ℝ} (hp : 0 < p) {k : ℕ} (hk : 0 < k)
    (hAdjacent : ∀ j < k, m j < (p + 1) * m (j + 1)) :
    ((p + 2) / p) * (m 0 - m k) < pathMassDistance m k := by
  obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have h := Finset.sum_lt_sum_of_nonempty (s := Finset.range (l + 1)) ⟨0,Finset.mem_range.mpr (Nat.succ_pos _)⟩
    (fun j hj => hAdjacent j (Finset.mem_range.mp hj))
  rw [← Finset.mul_sum,Finset.sum_range_succ' m,Finset.sum_range_succ (fun j => m (j + 1))] at h
  let S := ∑ j ∈ Finset.range l, m (j + 1)
  change S + m 0 < (p + 1) * (S + m (l + 1)) at h
  unfold pathMassDistance
  simp only [Nat.succ_sub_one]
  change ((p + 2) / p) * (m 0 - m (l + 1)) < m 0 + m (l + 1) + 2 * S
  apply (mul_lt_mul_iff_left₀ hp).mp
  have hE : ((p + 2) / p) * (m 0 - m (l + 1)) * p = (p + 2) * (m 0 - m (l + 1)) := by
    field_simp [hp.ne']
  rw [hE]
  nlinarith only [h]

theorem pathMassDistance_adjacent_abs {m : ℕ → ℝ} {p : ℝ} (hp : 0 < p) {k : ℕ} (hk : 0 < k)
    (hAdjacent : ∀ j < k, m j < (p + 1) * m (j + 1) ∧ m (j + 1) < (p + 1) * m j) :
    ((p + 2) / p) * |m 0 - m k| < pathMassDistance m k := by
  have hL := pathMassDistance_adjacent_lower hp hk (fun j hj => (hAdjacent j hj).1)
  have hR : ((p + 2) / p) * (m k - m 0) < pathMassDistance m k := by
    obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    have h := Finset.sum_lt_sum_of_nonempty (s := Finset.range (l + 1))
      ⟨0,Finset.mem_range.mpr (Nat.succ_pos _)⟩ (fun j hj => (hAdjacent j (Finset.mem_range.mp hj)).2)
    rw [← Finset.mul_sum,Finset.sum_range_succ' m,Finset.sum_range_succ (fun j => m (j + 1))] at h
    let S := ∑ j ∈ Finset.range l, m (j + 1)
    change S + m (l + 1) < (p + 1) * (S + m 0) at h
    unfold pathMassDistance
    simp only [Nat.succ_sub_one]
    change ((p + 2) / p) * (m (l + 1) - m 0) < m 0 + m (l + 1) + 2 * S
    apply (mul_lt_mul_iff_left₀ hp).mp
    have hE : ((p + 2) / p) * (m (l + 1) - m 0) * p = (p + 2) * (m (l + 1) - m 0) := by
      field_simp [hp.ne']
    rw [hE]
    nlinarith only [h]
  rw [abs_eq_max_neg,mul_max_of_nonneg _ _ (by positivity),neg_sub]
  exact max_lt hL hR

theorem pathMassDistance_le_label {m : ℕ → ℝ} (hm : ∀ j, m j ≤ 1) {k : ℕ} (hk : 0 < k) :
    pathMassDistance m k ≤ 2 * (k : ℝ) := by
  obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have hS := Finset.sum_le_sum (s := Finset.range l) (fun j _ => hm (j + 1))
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one] at hS
  unfold pathMassDistance
  simp only [Nat.succ_sub_one,Nat.cast_succ]
  linarith only [hS,hm 0,hm (l + 1)]

end ACS12.Pressure


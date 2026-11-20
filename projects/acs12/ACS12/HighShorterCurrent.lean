import ACS12.Angular
import ACS12.HighCurrentFlow

/-! The complete shorter-route pair current, including its zero antipodal contribution. -/
namespace ACS12.HighCurrent

open Finset

noncomputable def shorterCurrent {n : ℕ} (p D : ℝ) (a m : Fin n → ℝ) (i j : Fin n) : ℝ :=
  if i = j then 0 else if halfArc a i j < Real.pi / 2 then
    m i * m j * angularKernel p (halfArc a i j) / D ^ (p + 1) else 0

theorem halfArc_flip {n : ℕ} (a : Fin n → ℝ) {i j : Fin n} (hij : i ≠ j) :
    halfArc a j i = Real.pi - halfArc a i j := by
  rcases lt_or_gt_of_ne hij with h | h
  · simp only [halfArc,if_neg (not_lt.mpr h.le),if_pos h]
    ring
  · simp only [halfArc,if_pos h,if_neg (not_lt.mpr h.le)]
    ring

theorem angularKernel_flip (p t : ℝ) : angularKernel p (Real.pi - t) = -angularKernel p t := by
  simp only [angularKernel,Real.cos_pi_sub,Real.sin_pi_sub,neg_div]

theorem shorterCurrent_diagonal {n : ℕ} (p D : ℝ) (a m : Fin n → ℝ) (i : Fin n) :
    shorterCurrent p D a m i i = 0 := by simp only [shorterCurrent,if_true]

theorem shorterCurrent_difference {n : ℕ} (p D : ℝ) (a m : Fin n → ℝ) {i j : Fin n} (hij : i ≠ j) :
    shorterCurrent p D a m i j - shorterCurrent p D a m j i =
      (m i / D ^ (p + 1)) * (m j * angularKernel p (halfArc a i j)) := by
  simp only [shorterCurrent,if_neg hij,if_neg hij.symm,halfArc_flip a hij,angularKernel_flip]
  rcases lt_trichotomy (halfArc a i j) (Real.pi / 2) with h | h | h
  · rw [if_pos h,if_neg (by linarith only [h])]
    ring
  · rw [h]
    norm_num [angularKernel,Real.cos_pi_div_two]
  · rw [if_neg h.not_gt,if_pos (by linarith only [h])]
    ring

theorem shorterCurrent_nonneg {n : ℕ} (p : ℝ) {D : ℝ} (hD : 0 < D)
    (a m : Fin n → ℝ) (ha : StrictMono a) (ha₀ : ∀ i, 0 ≤ a i)
    (haπ : ∀ i, a i < 2 * Real.pi) (hm : ∀ i, 0 ≤ m i) (i j : Fin n) :
    0 ≤ shorterCurrent p D a m i j := by
  unfold shorterCurrent
  split_ifs with hij ht
  · exact le_rfl
  · have hArc := halfArc_mem ha ha₀ haπ (Ne.symm hij)
    have hSin := Real.sin_pos_of_pos_of_lt_pi hArc.1 hArc.2
    have hCos := Real.cos_pos_of_mem_Ioo
      (show halfArc a i j ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) by
        constructor <;> linarith only [hArc.1,ht,Real.pi_pos])
    exact div_nonneg
      (mul_nonneg (mul_nonneg (hm i) (hm j))
        (div_nonneg hCos.le (Real.rpow_pos_of_pos hSin _).le))
      (Real.rpow_pos_of_pos hD _).le
  · exact le_rfl

theorem shorterCurrent_divergence {n : ℕ} (p D : ℝ) (a m : Fin n → ℝ) (i : Fin n) :
    nodeDivergence (shorterCurrent p D a m) i =
      (m i / D ^ (p + 1)) *
        (∑ j ∈ univ.erase i, m j * angularKernel p (halfArc a i j)) := by
  have hErase : (∑ j, (shorterCurrent p D a m i j - shorterCurrent p D a m j i)) =
      ∑ j ∈ univ.erase i, (shorterCurrent p D a m i j - shorterCurrent p D a m j i) := by
    rw [sum_erase_eq_sub (mem_univ i),sub_self,sub_zero]
  unfold nodeDivergence
  rw [← sum_sub_distrib,hErase,Finset.mul_sum]
  apply sum_congr rfl
  intro j hj
  exact shorterCurrent_difference p D a m (mem_erase.mp hj).1.symm

end ACS12.HighCurrent

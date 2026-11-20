import ACS12.HighPhysicalCurrent

/-! Both original incident half-circles retain the same physical radial law and nonnegative current mark. -/
namespace ACS12.HighCurrent

theorem shorterCurrent_mul_reverse_zero {n : ℕ} (p D : ℝ) (a m : Fin n → ℝ) (i j : Fin n) :
    shorterCurrent p D a m i j * shorterCurrent p D a m j i = 0 := by
  by_cases hij : i = j
  · subst j
    rw [shorterCurrent_diagonal,zero_mul]
  · unfold shorterCurrent
    simp only [if_neg hij,if_neg (Ne.symm hij),halfArc_flip a hij]
    by_cases hShort : halfArc a i j < Real.pi / 2
    · rw [if_pos hShort,if_neg (by linarith only [hShort]),mul_zero]
    · rw [if_neg hShort,zero_mul]

theorem shorterCurrent_pair_abs {n : ℕ} (p : ℝ) {D : ℝ} (hD : 0 < D)
    (a m : Fin n → ℝ) (ha : StrictMono a) (ha₀ : ∀ i, 0 ≤ a i)
    (haπ : ∀ i, a i < 2 * Real.pi) (hm : ∀ i, 0 ≤ m i)
    {i j : Fin n} (hij : i ≠ j) :
    shorterCurrent p D a m i j + shorterCurrent p D a m j i =
      |(m i / D ^ (p + 1)) * (m j * angularKernel p (halfArc a i j))| := by
  have hFirst := shorterCurrent_nonneg p hD a m ha ha₀ haπ hm i j
  have hSecond := shorterCurrent_nonneg p hD a m ha ha₀ haπ hm j i
  have hProd := shorterCurrent_mul_reverse_zero p D a m i j
  have hAbs : shorterCurrent p D a m i j + shorterCurrent p D a m j i =
      |shorterCurrent p D a m i j - shorterCurrent p D a m j i| := by
    rcases mul_eq_zero.mp hProd with h | h
    · rw [h,zero_add,zero_sub,abs_neg,abs_of_nonneg hSecond]
    · rw [h,add_zero,sub_zero,abs_of_nonneg hFirst]
  rw [shorterCurrent_difference p D a m hij] at hAbs
  exact hAbs

end ACS12.HighCurrent

namespace ACS12.Configuration

open Finset HighCurrent

variable {n : ℕ} {α : ℝ} (F : ACS12.Configuration n α)

noncomputable def currentZeta (i j : Fin n) : ℝ :=
  |Real.cos (halfArc F.currentAngles i j)| /
    ((2 * F.radius) * Real.sin (halfArc F.currentAngles i j))

theorem currentZeta_nonneg {i j : Fin n} (hij : i ≠ j) : 0 ≤ F.currentZeta i j := by
  have hArc := halfArc_mem F.currentAngles_strictMono F.currentAngles_nonneg F.currentAngles_lt_two_pi hij.symm
  unfold currentZeta
  exact div_nonneg (abs_nonneg _) (mul_pos (mul_pos (by norm_num) F.radius_pos)
    (Real.sin_pos_of_pos_of_lt_pi hArc.1 hArc.2)).le

theorem current_pair_identity {i j : Fin n} (hij : i ≠ j) :
    F.currentEdges i j + F.currentEdges j i =
      (F.currentMasses i * F.currentMasses j /
        ‖F.position (F.currentOrder j) - F.position (F.currentOrder i)‖ ^ α) * F.currentZeta i j := by
  have hD : 0 < 2 * F.radius := mul_pos (by norm_num) F.radius_pos
  have hArc := halfArc_mem F.currentAngles_strictMono F.currentAngles_nonneg F.currentAngles_lt_two_pi hij.symm
  have hSin := Real.sin_pos_of_pos_of_lt_pi hArc.1 hArc.2
  have hi : 0 < F.currentMasses i := F.mass_pos (F.currentOrder i)
  have hj : 0 < F.currentMasses j := F.mass_pos (F.currentOrder j)
  have hChord := F.chord_eq_halfArc F.currentAngles F.currentOrder
    (fun k => F.phase_eq (F.currentOrder k)) hArc
  have hBase : 0 < (2 * F.radius) * Real.sin (halfArc F.currentAngles i j) := mul_pos hD hSin
  have hPower :
      (2 * F.radius) ^ (α + 1) * Real.sin (halfArc F.currentAngles i j) ^ (α + 1) =
        ((2 * F.radius) * Real.sin (halfArc F.currentAngles i j)) ^ α *
          ((2 * F.radius) * Real.sin (halfArc F.currentAngles i j)) := by
    rw [← Real.mul_rpow hD.le hSin.le,Real.rpow_add hBase,Real.rpow_one]
  unfold currentEdges
  rw [shorterCurrent_pair_abs α hD F.currentAngles F.currentMasses
    F.currentAngles_strictMono F.currentAngles_nonneg F.currentAngles_lt_two_pi
    (fun k => (F.mass_pos (F.currentOrder k)).le) hij,
    abs_mul,abs_div,abs_mul,abs_of_pos hi,abs_of_pos (Real.rpow_pos_of_pos hD _),abs_of_pos hj]
  have hK : |angularKernel α (halfArc F.currentAngles i j)| =
      |Real.cos (halfArc F.currentAngles i j)| /
        Real.sin (halfArc F.currentAngles i j) ^ (α + 1) := by
    unfold angularKernel
    rw [abs_div,abs_of_pos (Real.rpow_pos_of_pos hSin _)]
  rw [hK,hChord]
  unfold currentZeta
  calc
    _ = (F.currentMasses i * F.currentMasses j * |Real.cos (halfArc F.currentAngles i j)|) /
        ((2 * F.radius) ^ (α + 1) * Real.sin (halfArc F.currentAngles i j) ^ (α + 1)) := by
      field_simp [(Real.rpow_pos_of_pos hD (α + 1)).ne',(Real.rpow_pos_of_pos hSin (α + 1)).ne']
      <;> ring
    _ = _ := by
      rw [hPower]
      field_simp [hBase.ne',(Real.rpow_pos_of_pos hBase α).ne']
      <;> ring

theorem currentZeta_chord_identity {i j : Fin n} (hij : i ≠ j) :
    1 / (2 * F.radius) ^ 2 + F.currentZeta i j ^ 2 =
      1 / ‖F.position (F.currentOrder j) - F.position (F.currentOrder i)‖ ^ 2 := by
  have hD : 0 < 2 * F.radius := mul_pos (by norm_num) F.radius_pos
  have hArc := halfArc_mem F.currentAngles_strictMono F.currentAngles_nonneg F.currentAngles_lt_two_pi hij.symm
  have hSin := Real.sin_pos_of_pos_of_lt_pi hArc.1 hArc.2
  rw [F.chord_eq_halfArc F.currentAngles F.currentOrder (fun k => F.phase_eq (F.currentOrder k)) hArc]
  unfold currentZeta
  rw [div_pow,sq_abs]
  field_simp [hD.ne',F.radius_pos.ne',hSin.ne']
  linear_combination Real.sin_sq_add_cos_sq (halfArc F.currentAngles i j)

theorem current_incident_radial_bound (o : Fin n) :
    (∑ j ∈ univ.erase o,
      (F.currentMasses o * F.currentMasses j /
        ‖F.position (F.currentOrder j) - F.position (F.currentOrder o)‖ ^ α) * F.currentZeta o j) ≤
      2 * F.commonCurrent := by
  have h := F.current_total_incident_le o
  have hSum : (∑ j, F.currentEdges o j) + (∑ j, F.currentEdges j o) =
      ∑ j ∈ univ.erase o, (F.currentEdges o j + F.currentEdges j o) := by
    rw [sum_erase_eq_sub (mem_univ o),sum_add_distrib,F.currentEdges_diagonal,add_zero,sub_zero]
  rw [hSum] at h
  exact (sum_congr rfl (fun j hj => F.current_pair_identity (mem_erase.mp hj).1.symm)).symm ▸ h

end ACS12.Configuration

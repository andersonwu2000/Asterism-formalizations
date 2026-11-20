import ACS12.Physical
import ACS12.PressureMoments
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Original radial rows and centered squared-chord moment in diameter units. -/
namespace ACS12.Configuration

open Finset
open scoped BigOperators

variable {n : ℕ} {p : ℝ} (F : Configuration n p)

noncomputable def diameterChordSq (i j : Fin n) : ℝ :=
  (‖F.position j - F.position i‖ / (2 * F.radius)) ^ 2

theorem diameterChordSq_symm (i j : Fin n) : F.diameterChordSq i j = F.diameterChordSq j i := by
  unfold diameterChordSq
  rw [norm_sub_rev]

theorem diameterChordSq_pos {i j : Fin n} (h : j ≠ i) :
    0 < F.diameterChordSq i j :=
  sq_pos_of_pos (div_pos (F.chord_pos h) (mul_pos zero_lt_two F.radius_pos))

theorem diameterChordSq_le_one (i j : Fin n) : F.diameterChordSq i j ≤ 1 := by
  have hD := mul_pos zero_lt_two F.radius_pos
  have h := norm_sub_le (F.position j - F.center) (F.position i - F.center)
  rw [sub_sub_sub_cancel_right,F.on_circle,F.on_circle] at h
  have hN := div_nonneg (norm_nonneg (F.position j - F.position i)) hD.le
  have hB := (div_le_one hD).mpr (show ‖F.position j - F.position i‖ ≤ 2 * F.radius by linarith only [h])
  exact (pow_le_pow_left₀ hN hB 2).trans_eq (one_pow _)

theorem centered_chord_square (i : Fin n) :
    ∑ j ∈ univ.erase i, F.mass j * ‖F.position j - F.position i‖ ^ 2 =
      2 * F.radius ^ 2 * Pressure.massTotal F.mass := by
  have hVector : (∑ j, F.mass j • (F.position j - F.position i)) =
      -(Pressure.massTotal F.mass) • (F.position i - F.center) := by
    calc
      _ = ∑ j, F.mass j • ((F.position j - F.center) - (F.position i - F.center)) := by
        apply sum_congr rfl
        intro j _
        rw [sub_sub_sub_cancel_right]
      _ = ∑ j, (F.mass j • (F.position j - F.center) - F.mass j • (F.position i - F.center)) := by
        apply sum_congr rfl
        intro j _
        exact smul_sub _ _ _
      _ = _ := by
        have hS : (Pressure.massTotal F.mass) • (F.position i - F.center) =
            ∑ j, F.mass j • (F.position i - F.center) := Finset.sum_smul
        rw [sum_sub_distrib,F.centered,zero_sub,← hS]
        exact (neg_smul _ _).symm
  have h := congrArg (fun z : ℂ => (z * star (F.position i - F.center)).re) hVector
  have hTerm (j : Fin n) : F.mass j * ((F.position j - F.position i) *
      star (F.position i - F.center)).re = -(F.mass j * ‖F.position j - F.position i‖ ^ 2) / 2 := by
    rw [F.radial_chord]
    ring
  simp only [Complex.star_def] at hTerm
  simp only [sum_mul,Complex.re_sum,smul_mul_assoc,Complex.smul_re,smul_eq_mul,
    Complex.star_def,Complex.mul_conj,Complex.ofReal_re,Complex.normSq_eq_norm_sq,F.on_circle] at h
  simp_rw [hTerm] at h
  rw [← sum_div,sum_neg_distrib] at h
  rw [← sum_erase_add _ _ (mem_univ i),sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0),
    mul_zero,add_zero] at h
  linarith only [h]

theorem diameterChordSq_centered_sum (o i : Fin n) :
    ∑ j ∈ univ.erase i, (F.mass j / F.mass o) * F.diameterChordSq i j =
      (Pressure.massTotal F.mass / F.mass o) / 2 := by
  have hR := F.radius_pos
  have hO := F.mass_pos o
  unfold diameterChordSq
  have he (j : Fin n) : F.mass j / F.mass o *
      (‖F.position j - F.position i‖ / (2 * F.radius)) ^ 2 =
      (F.mass j * ‖F.position j - F.position i‖ ^ 2) / (F.mass o * (2 * F.radius) ^ 2) := by ring
  simp_rw [he,← sum_div]
  rw [F.centered_chord_square]
  field_simp [hO.ne',hR.ne']

theorem diameterChordSq_radial_sum (o i : Fin n) :
    ∑ j ∈ univ.erase i, (F.mass j / F.mass o) * F.diameterChordSq i j ^ (-(p / 2)) =
      (2 * F.radius) ^ p / F.mass o * (2 * F.coefficient * F.radius ^ 2) := by
  have hD := mul_pos zero_lt_two F.radius_pos
  have hO := F.mass_pos o
  have he (j : Fin n) (hj : j ∈ univ.erase i) :
      (F.mass j / F.mass o) * F.diameterChordSq i j ^ (-(p / 2)) =
      ((2 * F.radius) ^ p / F.mass o) * (F.mass j / ‖F.position j - F.position i‖ ^ p) := by
    have hd := F.chord_pos (mem_erase.mp hj).1
    have hQ := div_pos hd hD
    unfold diameterChordSq
    rw [← Real.rpow_natCast,← Real.rpow_mul hQ.le,
      show ((2 : ℕ) : ℝ) * (-(p / 2)) = -p by push_cast; ring,Real.rpow_neg hQ.le,Real.div_rpow hd.le hD.le]
    field_simp [hO.ne',(Real.rpow_pos_of_pos hD p).ne',(Real.rpow_pos_of_pos hd p).ne']
  rw [sum_congr rfl he,← mul_sum,F.radial_row]

end ACS12.Configuration

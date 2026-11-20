import CenteredCircle.PhysicalProjection
import CenteredCircle.PhysicalAngles
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Original centered cocircular equations with the physical force exponent. -/

namespace ACS12

open scoped BigOperators
open CenteredCircle.AllN (unitRay equal_radius_chord_projection)

noncomputable def forceTerm (α m : ℝ) (d : ℂ) : ℂ :=
  (m / ‖d‖ ^ (α + 2) : ℝ) • d

@[simp] theorem forceTerm_zero (α m : ℝ) : forceTerm α m 0 = 0 := by
  simp [forceTerm]

structure Configuration (n : ℕ) (α : ℝ) where
  mass : Fin n → ℝ
  position : Fin n → ℂ
  center : ℂ
  radius : ℝ
  coefficient : ℝ
  mass_pos : ∀ i, 0 < mass i
  radius_pos : 0 < radius
  distinct : Function.Injective position
  on_circle : ∀ i, ‖position i - center‖ = radius
  centered : (∑ i, mass i • (position i - center)) = 0
  central : ∀ i,
    (∑ j ∈ Finset.univ.erase i, forceTerm α (mass j) (position j - position i)) =
      (-coefficient) • (position i - center)

def IsEqualMassRegular {n : ℕ} {α : ℝ} (F : Configuration n α) : Prop :=
  (∃ m : ℝ, 0 < m ∧ ∀ i, F.mass i = m) ∧
  ∃ θ : ℝ, ∃ σ : Equiv.Perm (Fin n), ∀ k : Fin n,
    F.position (σ k) = F.center + (F.radius : ℂ) *
      unitRay (θ + 2 * Real.pi * (k : ℝ) / (n : ℝ))

namespace Configuration

variable {n : ℕ} {α : ℝ} (F : Configuration n α)

theorem chord_pos {i j : Fin n} (hji : j ≠ i) :
    0 < ‖F.position j - F.position i‖ :=
  norm_pos_iff.mpr (sub_ne_zero.mpr (F.distinct.ne hji))

theorem radial_chord (i j : Fin n) :
    ((F.position j - F.position i) * star (F.position i - F.center)).re =
      -‖F.position j - F.position i‖ ^ 2 / 2 := by
  simpa only [sub_sub_sub_cancel_right] using
    equal_radius_chord_projection (F.on_circle i) (F.on_circle j)

theorem radial_row (i : Fin n) :
    (∑ j ∈ Finset.univ.erase i, F.mass j / ‖F.position j - F.position i‖ ^ α) =
      2 * F.coefficient * F.radius ^ 2 := by
  have h := congrArg (fun z : ℂ => (z * star (F.position i - F.center)).re) (F.central i)
  simp only [forceTerm, smul_mul_assoc, Complex.smul_re, smul_eq_mul, Finset.sum_mul,
    Complex.re_sum, Complex.star_def, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq, F.on_circle] at h
  have hterm (j : Fin n) (hj : j ∈ Finset.univ.erase i) :
      (F.mass j / ‖F.position j - F.position i‖ ^ (α + 2)) *
        ((F.position j - F.position i) * star (F.position i - F.center)).re =
      -(F.mass j / ‖F.position j - F.position i‖ ^ α) / 2 := by
    have hd := F.chord_pos (Finset.mem_erase.mp hj).1
    rw [F.radial_chord, Real.rpow_add hd, Real.rpow_two]
    field_simp [ne_of_gt hd, ne_of_gt (Real.rpow_pos_of_pos hd α)]
  simp only [Complex.star_def] at hterm
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, Finset.sum_neg_distrib] at h
  nlinarith

theorem tangential_row (i : Fin n) :
    (∑ j ∈ Finset.univ.erase i,
      (F.mass j / ‖F.position j - F.position i‖ ^ (α + 2)) *
        ((F.position j - F.position i) * star (F.position i - F.center)).im) = 0 := by
  have h := congrArg (fun z : ℂ => (z * star (F.position i - F.center)).im) (F.central i)
  simpa only [forceTerm, smul_mul_assoc, Complex.smul_im, smul_eq_mul, Finset.sum_mul,
    Complex.im_sum, Complex.star_def, Complex.mul_conj, Complex.ofReal_im, mul_zero] using h

theorem coefficient_pos (hn : 2 ≤ n) : 0 < F.coefficient := by
  let i : Fin n := ⟨0, by omega⟩
  have hs : 0 < (∑ j ∈ Finset.univ.erase i, F.mass j /
      ‖F.position j - F.position i‖ ^ α) := by
    apply Finset.sum_pos
    · intro j hj
      exact div_pos (F.mass_pos j)
        (Real.rpow_pos_of_pos (F.chord_pos (Finset.mem_erase.mp hj).1) α)
    · exact ⟨⟨1, by omega⟩, by simp [i, Fin.ext_iff]⟩
  rw [F.radial_row] at hs
  by_contra! h
  exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg (by linarith : 2 * F.coefficient ≤ 0)
    (sq_nonneg F.radius))) hs

end Configuration

end ACS12

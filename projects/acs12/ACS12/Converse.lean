import ACS12.Physical
import CenteredCircle.PhysicalConverse

/-! The regular polygon gives a solution for every real force exponent. -/

namespace ACS12

open scoped BigOperators
open CenteredCircle.AllN
set_option backward.isDefEq.respectTransparency false

noncomputable def unitForce (α : ℝ) (n : ℕ) (i : Fin n) : ℂ :=
  ∑ j : Fin n, forceTerm α 1 (regularPoint n j - regularPoint n i)

private theorem unitForce_rotation (α : ℝ) (n : ℕ) [NeZero n] (i : Fin n) :
    unitForce α n i = regularPoint n i * unitForce α n 0 := by
  rw [unitForce, ← Equiv.sum_comp (Equiv.addLeft i)]
  change (∑ k : Fin n, forceTerm α 1 (regularPoint n (i + k) - regularPoint n i)) = _
  have hterm (k : Fin n) :
      forceTerm α 1 (regularPoint n (i + k) - regularPoint n i) =
      regularPoint n i * forceTerm α 1 (regularPoint n k - 1) := by
    rw [regularPoint_add,
      show regularPoint n i * regularPoint n k - regularPoint n i =
        regularPoint n i * (regularPoint n k - 1) by ring,
      forceTerm, norm_mul, regularPoint_norm, one_mul]
    simp only [forceTerm, Complex.real_smul]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum]
  simp only [unitForce, regularPoint_zero]

private theorem unitForce_zero_im (α : ℝ) (n : ℕ) [NeZero n] : (unitForce α n 0).im = 0 := by
  let f : Fin n → ℝ := fun k => (forceTerm α 1 (regularPoint n k - 1)).im
  have hterm (k : Fin n) : f (-k) = -f k := by
    simp only [f, forceTerm, Complex.smul_im, smul_eq_mul]
    rw [regularPoint_star, show star (regularPoint n k) - 1 = star (regularPoint n k - 1) by simp,
      norm_star]
    simp only [Complex.star_def, Complex.conj_im]
    ring
  have he := Equiv.sum_comp (Equiv.neg (Fin n)) f
  change (∑ k : Fin n, f (-k)) = ∑ k : Fin n, f k at he
  rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_neg_distrib] at he
  have hz : (∑ k : Fin n, f k) = 0 := by linarith
  simpa only [unitForce, regularPoint_zero, Complex.im_sum, f] using hz

private theorem unitForce_radial (α : ℝ) (n : ℕ) [NeZero n] (i : Fin n) :
    unitForce α n i = (unitForce α n 0).re • regularPoint n i := by
  have he : unitForce α n 0 = ((unitForce α n 0).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa only [Complex.ofReal_im] using unitForce_zero_im α n
  calc
    unitForce α n i = regularPoint n i * unitForce α n 0 := unitForce_rotation α n i
    _ = (unitForce α n 0).re • regularPoint n i := by
      conv_lhs => rw [he]
      rw [Complex.real_smul, mul_comm]

noncomputable def regularCoefficient (α : ℝ) (n : ℕ) [NeZero n] (m R : ℝ) : ℝ :=
  -(m / R ^ (α + 2)) * (unitForce α n 0).re

private theorem similarity_forceTerm (α m : ℝ) (O γ a b : ℂ) :
    forceTerm α m ((O + γ * b) - (O + γ * a)) =
      (m / ‖γ‖ ^ (α + 2) : ℝ) • (γ * forceTerm α 1 (b - a)) := by
  rw [show (O + γ * b) - (O + γ * a) = γ * (b - a) by ring, forceTerm, norm_mul,
    Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  simp only [forceTerm, Complex.real_smul, div_eq_mul_inv, mul_inv_rev, one_mul,
    Complex.ofReal_mul, Complex.ofReal_inv]
  ring

theorem regularPosition_force {n : ℕ} [NeZero n] (α : ℝ) (O : ℂ) {R : ℝ} (hR : 0 < R)
    (m θ : ℝ) (i : Fin n) :
    (∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
      forceTerm α m (regularPosition n O R θ j - regularPosition n O R θ i)) =
      (-regularCoefficient α n m R) • (regularPosition n O R θ i - O) := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), sub_self, forceTerm_zero, sub_zero]
  let γ := (R : ℂ) * unitRay θ
  change (∑ j : Fin n, forceTerm α m ((O + γ * regularPoint n j) -
    (O + γ * regularPoint n i))) = (-regularCoefficient α n m R) • (O + γ * regularPoint n i - O)
  rw [Finset.sum_congr rfl (fun j _ => similarity_forceTerm α m O γ
    (regularPoint n i) (regularPoint n j)), show ‖γ‖ = R from regular_rotation_norm hR θ,
    add_sub_cancel_left]
  rw [← Finset.smul_sum, ← Finset.mul_sum]
  change (m / R ^ (α + 2)) • (γ * unitForce α n i) = _
  rw [unitForce_radial]
  simp only [regularCoefficient, Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_mul]
  ring

noncomputable def regularConfiguration {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (α : ℝ) (O : ℂ) (m R θ : ℝ) (hm : 0 < m) (hR : 0 < R) : Configuration n α where
  mass := fun _ => m
  position := regularPosition n O R θ
  center := O
  radius := R
  coefficient := regularCoefficient α n m R
  mass_pos := fun _ => hm
  radius_pos := hR
  distinct := regularPosition_injective (NeZero.ne n) O hR θ
  on_circle := regularPosition_on_circle n O hR θ
  centered := regularPosition_centered hn O m R θ
  central := regularPosition_force α O hR m θ

/-- Every regular polygon of any positive radius and common positive mass solves
the original centered equations. The force coefficient is strictly positive. -/
theorem regular_polygon_converse {n : ℕ} (hn : 2 ≤ n)
    (α : ℝ) (O : ℂ) (m R θ : ℝ) (hm : 0 < m) (hR : 0 < R) :
    ∃ F : Configuration n α,
      F.center = O ∧ F.radius = R ∧ (∀ i, F.mass i = m) ∧ 0 < F.coefficient ∧
      ∀ i, F.position i = O + (R : ℂ) * unitRay (θ + 2 * Real.pi * (i : ℝ) / (n : ℝ)) := by
  letI : NeZero n := ⟨by omega⟩
  let F := regularConfiguration hn α O m R θ hm hR
  exact ⟨F, rfl, rfl, fun _ => rfl, F.coefficient_pos hn, regularPosition_phase n O R θ⟩

end ACS12

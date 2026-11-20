import CenteredCircle.PhasePairGeometry
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Group.Fin.Basic

/-! Finite cyclic geometry for the independent physical converse. -/

namespace CenteredCircle.AllN

open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def regularRoot (n : ℕ) : ℂ := unitRay (2 * Real.pi / (n : ℝ))
noncomputable def regularPoint (n : ℕ) (k : Fin n) : ℂ := regularRoot n ^ k.val

theorem regularPoint_phase (n : ℕ) (k : Fin n) :
    regularPoint n k = unitRay (2 * Real.pi * (k : ℝ) / (n : ℝ)) := by
  unfold regularPoint regularRoot unitRay
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem regularRoot_primitive {n : ℕ} (hn : n ≠ 0) : IsPrimitiveRoot (regularRoot n) n := by
  have he : regularRoot n = Complex.exp (2 * Real.pi * Complex.I / (n : ℂ)) := by
    unfold regularRoot unitRay
    congr 1
    push_cast
    ring
  rw [he]
  exact Complex.isPrimitiveRoot_exp n hn

theorem regularPoint_norm (n : ℕ) (k : Fin n) : ‖regularPoint n k‖ = 1 := by
  rw [regularPoint_phase, norm_unitRay]

theorem regularPoint_ne_zero (n : ℕ) (k : Fin n) : regularPoint n k ≠ 0 := by
  intro h
  have hh := regularPoint_norm n k
  rw [h, norm_zero] at hh
  norm_num at hh

theorem regularPoint_injective {n : ℕ} (hn : n ≠ 0) : Function.Injective (regularPoint n) := by
  intro i j h
  exact Fin.ext ((regularRoot_primitive hn).pow_inj i.isLt j.isLt h)

theorem regularPoint_sum {n : ℕ} (hn : 2 ≤ n) : (∑ k : Fin n, regularPoint n k) = 0 := by
  unfold regularPoint
  rw [Fin.sum_univ_eq_sum_range]
  exact (regularRoot_primitive (by omega : n ≠ 0)).geom_sum_eq_zero (by omega)

theorem regularPoint_zero (n : ℕ) [NeZero n] : regularPoint n 0 = 1 := by
  simp [regularPoint]

theorem regularPoint_add (n : ℕ) [NeZero n] (i j : Fin n) :
    regularPoint n (i + j) = regularPoint n i * regularPoint n j := by
  unfold regularPoint
  rw [Fin.val_add, ← pow_eq_pow_mod _ (regularRoot_primitive (NeZero.ne n)).pow_eq_one, pow_add]

theorem regularPoint_star (n : ℕ) [NeZero n] (i : Fin n) :
    regularPoint n (-i) = star (regularPoint n i) := by
  apply mul_right_cancel₀ (regularPoint_ne_zero n i)
  rw [← regularPoint_add, neg_add_cancel, regularPoint_zero]
  rw [mul_comm (star _), Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, regularPoint_norm]
  norm_num

end CenteredCircle.AllN

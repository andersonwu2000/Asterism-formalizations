import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! Complete finite directed-circle current conservation before binding the original torque rows. -/
namespace ACS12.HighCurrent

open Finset

noncomputable def cutIndicator (a b t : ℝ) : ℝ :=
  (if a ≤ t then 1 else 0) - (if b ≤ t then 1 else 0) + (if b < a then 1 else 0)

noncomputable def cutFlux {ι : Type*} [Fintype ι] (x : ι → ℝ) (J : ι → ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, ∑ j, J i j * cutIndicator (x i) (x j) t

noncomputable def nodeDivergence {ι : Type*} [Fintype ι] (J : ι → ι → ℝ) (i : ι) : ℝ :=
  (∑ j, J i j) - ∑ j, J j i

noncomputable def wrapFlux {ι : Type*} [Fintype ι] (x : ι → ℝ) (J : ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, J i j * (if x j < x i then 1 else 0)

theorem cutIndicator_bounds (a b t : ℝ) : 0 ≤ cutIndicator a b t ∧ cutIndicator a b t ≤ 1 := by
  unfold cutIndicator
  split_ifs <;> constructor <;> norm_num at * <;> linarith

theorem cutIndicator_self (a t : ℝ) : cutIndicator a a t = 0 := by
  simp only [cutIndicator,sub_self,lt_self_iff_false,if_false,add_zero]

theorem cutIndicator_start {a b : ℝ} (hab : a ≠ b) : cutIndicator a b a = 1 := by
  rcases lt_or_gt_of_ne hab with h | h
  · simp only [cutIndicator,le_refl,if_true,h.not_ge,if_false,
      not_lt.mpr h.le,sub_zero,add_zero]
  · simp only [cutIndicator,le_refl,if_true,h.le,h,sub_self,zero_add]

theorem cutFlux_decomposition {ι : Type*} [Fintype ι] (x : ι → ℝ) (J : ι → ι → ℝ) (t : ℝ) :
    cutFlux x J t =
      (∑ i, (if x i ≤ t then 1 else 0) * nodeDivergence J i) + wrapFlux x J := by
  have hOut : (∑ i, ∑ j, J i j * (if x i ≤ t then 1 else 0)) =
      ∑ i, (if x i ≤ t then 1 else 0) * (∑ j, J i j) := by
    apply sum_congr rfl
    intro i _
    rw [← sum_mul]
    ring
  have hIn : (∑ i, ∑ j, J i j * (if x j ≤ t then 1 else 0)) =
      ∑ i, (if x i ≤ t then 1 else 0) * (∑ j, J j i) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    rw [← sum_mul]
    ring
  unfold cutFlux
  simp_rw [cutIndicator,mul_add,mul_sub,sum_add_distrib,sum_sub_distrib]
  rw [hOut,hIn]
  simp only [nodeDivergence,mul_sub,sum_sub_distrib,wrapFlux]

theorem cutFlux_constant {ι : Type*} [Fintype ι] (x : ι → ℝ) (J : ι → ι → ℝ)
    (hD : ∀ i, nodeDivergence J i = 0) (t : ℝ) :
    cutFlux x J t = wrapFlux x J := by
  rw [cutFlux_decomposition]
  simp only [hD,mul_zero,sum_const_zero,zero_add]

theorem cutFlux_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) (J : ι → ι → ℝ)
    (hJ : ∀ i j, 0 ≤ J i j) (t : ℝ) : 0 ≤ cutFlux x J t := by
  exact sum_nonneg fun i _ => sum_nonneg fun j _ =>
    mul_nonneg (hJ i j) (cutIndicator_bounds _ _ _).1

theorem outgoing_le_cutFlux {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (J : ι → ι → ℝ) (hX : Function.Injective x)
    (hJ : ∀ i j, 0 ≤ J i j) (hDiagonal : ∀ i, J i i = 0) (o : ι) :
    (∑ j, J o j) ≤ cutFlux x J (x o) := by
  have hRow : (∑ j, J o j * cutIndicator (x o) (x j) (x o)) = ∑ j, J o j := by
    apply sum_congr rfl
    intro j _
    by_cases hjo : j = o
    · subst j
      rw [hDiagonal,zero_mul]
    · rw [cutIndicator_start (fun h => hjo (hX h).symm),mul_one]
  unfold cutFlux
  rw [← hRow]
  exact single_le_sum (f := fun i => ∑ j, J i j * cutIndicator (x i) (x j) (x o))
    (fun i _ => sum_nonneg fun j _ =>
      mul_nonneg (hJ i j) (cutIndicator_bounds (x i) (x j) (x o)).1) (mem_univ o)

theorem total_incident_le_two_flux {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (J : ι → ι → ℝ) (hX : Function.Injective x)
    (hJ : ∀ i j, 0 ≤ J i j) (hDiagonal : ∀ i, J i i = 0)
    (hD : ∀ i, nodeDivergence J i = 0) (o : ι) :
    (∑ j, J o j) + (∑ j, J j o) ≤ 2 * wrapFlux x J := by
  have hOut := outgoing_le_cutFlux x J hX hJ hDiagonal o
  rw [cutFlux_constant x J hD] at hOut
  have hBalance := hD o
  unfold nodeDivergence at hBalance
  linarith only [hOut,hBalance]

end ACS12.HighCurrent

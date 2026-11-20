import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! One complete crossing rectangle is paid once by the two original disjoint side sums. -/
namespace ACS12.HighCurrent

open Finset

theorem complete_rectangle_bound {ι : Type*} (S : Finset ι) (e : ι → ℝ)
    (back front : ι → Prop) [DecidablePred back] [DecidablePred front]
    (J : ι → ι → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (he : ∀ i ∈ S, 0 ≤ e i) (hSides : ∀ i ∈ S, ¬(back i ∧ front i))
    (hJ : ∀ i ∈ S, ∀ j ∈ S, J i j ≤
      4 * c * (if back i then e i else 0) * (if front j then e j else 0)) :
    (∑ i ∈ S, ∑ j ∈ S, J i j) ≤ c * (∑ i ∈ S, e i) ^ 2 := by
  let b (i : ι) := if back i then e i else 0
  let f (i : ι) := if front i then e i else 0
  let B := ∑ i ∈ S, b i
  let F := ∑ i ∈ S, f i
  let E := ∑ i ∈ S, e i
  have hb (i : ι) (hi : i ∈ S) : 0 ≤ b i := by unfold b; split_ifs; exact he i hi; exact le_rfl
  have hf (i : ι) (hi : i ∈ S) : 0 ≤ f i := by unfold f; split_ifs; exact he i hi; exact le_rfl
  have hB : 0 ≤ B := sum_nonneg hb
  have hF : 0 ≤ F := sum_nonneg hf
  have hE : 0 ≤ E := sum_nonneg he
  have hMasks (i : ι) (hi : i ∈ S) : b i + f i ≤ e i := by
    have hSide := hSides i hi
    have hPos := he i hi
    unfold b f
    split_ifs <;> simp_all
  have hBF : B + F ≤ E := by
    have h := sum_le_sum hMasks
    simpa only [sum_add_distrib] using h
  have hSum := sum_le_sum (fun i hi => sum_le_sum (fun j hj => hJ i hi j hj))
  have hFactor : (∑ i ∈ S, ∑ j ∈ S, 4 * c * b i * f j) = 4 * c * B * F := by
    calc
      _ = ∑ i ∈ S, (4 * c * b i) * F := by
        apply sum_congr rfl
        intro i _
        exact (mul_sum _ _ _).symm
      _ = (∑ i ∈ S, 4 * c * b i) * F := (sum_mul _ _ _).symm
      _ = _ := by rw [← mul_sum]
  change (∑ i ∈ S, ∑ j ∈ S, J i j) ≤ ∑ i ∈ S, ∑ j ∈ S, 4 * c * b i * f j at hSum
  rw [hFactor] at hSum
  have hSquare := mul_nonneg hc (sq_nonneg (B - F))
  have hSq := mul_le_mul_of_nonneg_left ((sq_le_sq₀ (add_nonneg hB hF) hE).mpr hBF) hc
  nlinarith only [hSum,hSquare,hSq]

end ACS12.HighCurrent

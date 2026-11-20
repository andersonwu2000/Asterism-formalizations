import ACS12.HighCurrentFlow

/-! The actual complete cut at a label retains its outgoing incident half and all nonincident crossings. -/
namespace ACS12.HighCurrent

open Finset

theorem cutIndicator_end (a b : ℝ) : cutIndicator a b b = 0 := by
  unfold cutIndicator
  by_cases h : a ≤ b
  · simp only [h,le_refl,if_true,not_lt.mpr h,if_false]
    ring
  · simp only [h,le_refl,if_true,lt_of_not_ge h,if_false]
    ring

theorem cutFlux_node_decomposition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (J : ι → ι → ℝ) (hx : Function.Injective x) (hDiag : ∀ i, J i i = 0) (o : ι) :
    cutFlux x J (x o) = (∑ j, J o j) +
      ∑ i ∈ univ.erase o, ∑ j ∈ univ.erase o, J i j * cutIndicator (x i) (x j) (x o) := by
  have hRoot : (∑ j, J o j * cutIndicator (x o) (x j) (x o)) = ∑ j, J o j := by
    apply sum_congr rfl
    intro j _
    by_cases hjo : j = o
    · subst j
      rw [hDiag,zero_mul]
    · rw [cutIndicator_start (fun h => hjo (hx h).symm),mul_one]
  have hOther (i : ι) : (∑ j, J i j * cutIndicator (x i) (x j) (x o)) =
      ∑ j ∈ univ.erase o, J i j * cutIndicator (x i) (x j) (x o) := by
    rw [sum_erase_eq_sub (mem_univ o),cutIndicator_end,mul_zero,sub_zero]
  unfold cutFlux
  rw [← sum_erase_add univ (fun i => ∑ j, J i j * cutIndicator (x i) (x j) (x o)) (mem_univ o),hRoot]
  rw [sum_congr rfl (fun i _ => hOther i)]
  ring

end ACS12.HighCurrent

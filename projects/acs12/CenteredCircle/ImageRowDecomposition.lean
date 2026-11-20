import CenteredCircle.AnchoredSource

/-!
Exact decompositions of the same periodic source at the two anchors. The sign
parameter treats the radial sum and signed torque together; at sign -1 the
self-image term cancels identically.
-/

namespace CenteredCircle.AllN

open scoped BigOperators

theorem sum_with_anchor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι) (c : ℝ) (f : ι → ℝ) :
    (∑ i, if i = a then c else f i) = c + ∑ i ∈ Finset.univ.erase a, f i := by
  have hs := Finset.add_sum_erase Finset.univ (fun i => if i = a then c else f i)
    (Finset.mem_univ a)
  have hr : (∑ i ∈ Finset.univ.erase a, if i = a then c else f i) =
      ∑ i ∈ Finset.univ.erase a, f i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact if_neg (Finset.mem_erase.mp hi).1
  simpa only [if_pos rfl, hr] using hs.symm

namespace AnchoredCircleSource

variable {ι : Type*} [DecidableEq ι] (F : AnchoredCircleSource ι)

theorem root_image_atom (K : ℝ → ℝ) (ε : ℝ)
    (hs : Summable (fun j : ℕ => K (1 + j * F.period))) (i : ι) :
    ε * imageTail K F.period (F.leftDistance i) +
      imageTail K F.period (F.rightDistance i + 1) + (if i = F.neighbor then K 1 else 0) =
      if i = F.root then (1 + ε) * imageTail K F.period F.period
      else imageTail K F.period (F.coordinate i) +
        ε * imageTail K F.period (F.period - F.coordinate i) := by
  have hsplit := imageTail_split K F.period 1 hs
  by_cases hi : i = F.root
  · subst i
    simp only [rightDistance, leftDistance, F.coordinate_root, zero_add,
      sub_zero, sub_add_cancel, true_or, ite_true, F.root_ne_neighbor, ite_false]
    ring
  · by_cases hj : i = F.neighbor
    · subst i
      simp only [rightDistance, leftDistance, F.coordinate_neighbor, or_true,
        ite_true, hi, ite_false]
      rw [show 1 + F.period - 1 + 1 = 1 + F.period by ring]
      linarith
    · simp only [rightDistance, leftDistance, hi, hj, false_or, ite_false,
        sub_add_cancel, add_zero]
      ring

theorem neighbor_image_atom (K : ℝ → ℝ) (ε : ℝ)
    (hs : Summable (fun j : ℕ => K (1 + j * F.period))) (i : ι) :
    ε * imageTail K F.period (F.leftDistance i + 1) +
      imageTail K F.period (F.rightDistance i) + (if i = F.root then ε * K 1 else 0) =
      if i = F.neighbor then (1 + ε) * imageTail K F.period F.period
      else imageTail K F.period (F.rightDistance i) +
        ε * imageTail K F.period (F.period - F.rightDistance i) := by
  have hsplit := imageTail_split K F.period 1 hs
  by_cases hi : i = F.neighbor
  · subst i
    have hne := Ne.symm F.root_ne_neighbor
    simp only [rightDistance, leftDistance, F.coordinate_neighbor, or_true,
      ite_true, hne, ite_false, add_zero]
    rw [show F.period - 1 + 1 = F.period by ring,
      show 1 + F.period - 1 = F.period by ring]
    ring
  · by_cases hj : i = F.root
    · subst i
      simp only [rightDistance, leftDistance, F.coordinate_root, true_or,
        ite_true, hi, ite_false, sub_zero, zero_add]
      rw [show F.period - (F.period - 1) = 1 by ring,
        show F.period + 1 = 1 + F.period by ring]
      nlinarith [congrArg (fun z : ℝ => ε * z) hsplit]
    · simp only [rightDistance, leftDistance, hi, hj, false_or, ite_false, add_zero]
      rw [show F.period - (F.coordinate i - 1) = F.period - F.coordinate i + 1 by ring]
      ring

end AnchoredCircleSource

end CenteredCircle.AllN

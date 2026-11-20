import ACS12.HighPhysicalCurrent

/-! Every original nonincident edge crossing a label lies in the same two complete shorter-half-circle sides. -/
namespace ACS12.HighCurrent

theorem cutIndicator_zero_or_one (a b t : ℝ) :
    cutIndicator a b t = 0 ∨ cutIndicator a b t = 1 := by
  unfold cutIndicator
  split_ifs <;> norm_num at * <;> try linarith

theorem crossing_cut_halfArcs {n : ℕ} (a : Fin n → ℝ) (ha : StrictMono a)
    (ha₀ : ∀ i, 0 ≤ a i) (haπ : ∀ i, a i < 2 * Real.pi)
    {o i j : Fin n} (hio : i ≠ o) (hjo : j ≠ o) (hij : i ≠ j)
    (hShort : halfArc a i j < Real.pi / 2)
    (hCut : cutIndicator (a i) (a j) (a o) = 1) :
    Real.pi / 2 < halfArc a o i ∧ halfArc a o j < Real.pi / 2 ∧
      halfArc a i j = (Real.pi - halfArc a o i) + halfArc a o j := by
  have hi₀ := ha₀ i
  have hj₀ := ha₀ j
  have ho₀ := ha₀ o
  have hiπ := haπ i
  have hjπ := haπ j
  have hoπ := haπ o
  unfold cutIndicator at hCut
  simp only [ha.le_iff_le,ha.lt_iff_lt] at hCut
  rcases lt_or_gt_of_ne hio with hi | hi
  all_goals have hai := ha hi
  all_goals rcases lt_or_gt_of_ne hjo with hj | hj
  all_goals have haj := ha hj
  all_goals rcases lt_or_gt_of_ne hij with hi_j | hi_j
  all_goals have haij := ha hi_j
  all_goals unfold halfArc at hShort ⊢
  all_goals split_ifs at hCut hShort ⊢ <;> norm_num at hCut <;> try omega
  all_goals refine ⟨?_,?_,?_⟩ <;> linarith

end ACS12.HighCurrent

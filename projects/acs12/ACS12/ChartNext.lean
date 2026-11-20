import ACS12.ChartArc

/-! The next occupied sites of the original finite source. -/

namespace CenteredCircle.AllN.AnchoredCircleSource

variable {ι : Type*} [DecidableEq ι] (S : AnchoredCircleSource ι)

def IsNext (i j : ι) : Prop :=
  S.coordinate i < S.coordinate j ∧
    ∀ k, ¬(S.coordinate i < S.coordinate k ∧ S.coordinate k < S.coordinate j)

theorem root_neighbor_next : S.IsNext S.root S.neighbor := by
  rw [IsNext, S.coordinate_root, S.coordinate_neighbor]
  refine ⟨by norm_num, ?_⟩
  intro k hk
  by_cases hr : k = S.root
  · simpa only [hr, S.coordinate_root, lt_self_iff_false, false_and] using hk
  by_cases hn : k = S.neighbor
  · simpa only [hn, S.coordinate_neighbor, lt_self_iff_false, and_false] using hk
  exact (S.other_coordinate k hr hn).not_ge hk.2.le

theorem IsNext.forward_le {i j : ι} (h : S.IsNext i j) (k : ι) :
    S.forwardDistance i j ≤ S.forwardDistance i k := by
  rcases h with ⟨hij, hEmpty⟩
  by_cases hik : i = k
  · subst k
    rw [S.forwardDistance_self, S.forwardDistance_eq_sub hij]
    linarith [S.coordinate_nonneg i, S.coordinate_lt_period j]
  rcases lt_or_gt_of_ne (S.coordinate_injective.ne hik) with hk | hk
  · rw [S.forwardDistance_eq_sub hij, S.forwardDistance_eq_sub hk]
    have hle : S.coordinate j ≤ S.coordinate k := le_of_not_gt fun hlt => hEmpty k ⟨hk, hlt⟩
    linarith
  · rw [S.forwardDistance_eq_sub hij, S.forwardDistance_eq_wrap hk]
    linarith [S.coordinate_nonneg k, S.coordinate_lt_period j]

theorem IsNext.backward_le {i j : ι} (h : S.IsNext i j) (k : ι) :
    S.forwardDistance i j ≤ S.forwardDistance k j := by
  rcases h with ⟨hij, hEmpty⟩
  by_cases hkj : k = j
  · subst k
    rw [S.forwardDistance_self, S.forwardDistance_eq_sub hij]
    linarith [S.coordinate_nonneg i, S.coordinate_lt_period j]
  rcases lt_or_gt_of_ne (S.coordinate_injective.ne hkj) with hk | hk
  · rw [S.forwardDistance_eq_sub hij, S.forwardDistance_eq_sub hk]
    have hle : S.coordinate k ≤ S.coordinate i := le_of_not_gt fun hlt => hEmpty k ⟨hlt, hk⟩
    linarith
  · rw [S.forwardDistance_eq_sub hij, S.forwardDistance_eq_wrap hk]
    linarith [S.coordinate_nonneg i, S.coordinate_lt_period k]

variable [Fintype ι]

theorem exists_third (hn : 3 ≤ Fintype.card ι) : ∃ j, S.IsNext S.neighbor j := by
  let W := (Finset.univ.erase S.root).erase S.neighbor
  have hnR : S.neighbor ≠ S.root := by
    intro h
    have he := congrArg S.coordinate h
    rw [S.coordinate_root, S.coordinate_neighbor] at he
    norm_num at he
  have hcard : W.card = Fintype.card ι - 1 - 1 := by
    simp only [W, Finset.card_erase_of_mem (Finset.mem_univ S.root),
      Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hnR, Finset.mem_univ _⟩), Finset.card_univ]
  have hW : W.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨j, hj, hmin⟩ := W.exists_min_image S.coordinate hW
  have hjN := (Finset.mem_erase.mp hj).1
  have hjR := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
  have hj0 := S.other_coordinate j hjR hjN
  rw [← S.coordinate_neighbor] at hj0
  refine ⟨j, hj0, fun k hk => ?_⟩
  have hkN : k ≠ S.neighbor := fun h => (lt_irrefl _) (h ▸ hk.1)
  have hkR : k ≠ S.root := by
    intro h
    rw [h, S.coordinate_root, S.coordinate_neighbor] at hk
    linarith [hk.1]
  have hkW : k ∈ W := Finset.mem_erase.mpr
    ⟨hkN, Finset.mem_erase.mpr ⟨hkR, Finset.mem_univ _⟩⟩
  exact (hmin k hkW).not_gt hk.2

theorem exists_fourth (hn : 4 ≤ Fintype.card ι) {j : ι}
    (hj : S.IsNext S.neighbor j) : ∃ k, S.IsNext j k := by
  let W := ((Finset.univ.erase S.root).erase S.neighbor).erase j
  have hNR : S.neighbor ≠ S.root := by
    intro h
    have he := congrArg S.coordinate h
    rw [S.coordinate_root, S.coordinate_neighbor] at he
    norm_num at he
  have hjN : j ≠ S.neighbor := fun h => (lt_irrefl _) (h ▸ hj.1)
  have hjR : j ≠ S.root := by
    intro h
    have hh := hj.1
    rw [h, S.coordinate_root, S.coordinate_neighbor] at hh
    norm_num at hh
  have hjMem : j ∈ (Finset.univ.erase S.root).erase S.neighbor :=
    Finset.mem_erase.mpr ⟨hjN, Finset.mem_erase.mpr ⟨hjR, Finset.mem_univ _⟩⟩
  have hcard : W.card = Fintype.card ι - 1 - 1 - 1 := by
    simp only [W, Finset.card_erase_of_mem hjMem, Finset.card_erase_of_mem (Finset.mem_univ S.root),
      Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hNR, Finset.mem_univ _⟩), Finset.card_univ]
  have hW : W.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨k, hk, hmin⟩ := W.exists_min_image S.coordinate hW
  have hkj := (Finset.mem_erase.mp hk).1
  have hkN := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
  have hkR := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).2).1
  have hk0 := S.other_coordinate k hkR hkN
  rw [← S.coordinate_neighbor] at hk0
  have hjk : S.coordinate j < S.coordinate k := by
    exact lt_of_le_of_ne (le_of_not_gt fun h => hj.2 k ⟨hk0, h⟩)
      (S.coordinate_injective.ne hkj.symm)
  refine ⟨k, hjk, fun l hl => ?_⟩
  have hlJ : l ≠ j := fun h => (lt_irrefl _) (h ▸ hl.1)
  have hlN : l ≠ S.neighbor := fun h => (lt_irrefl _) (h ▸ hj.1.trans hl.1)
  have hlR : l ≠ S.root := by
    intro h
    have hh := hj.1.trans hl.1
    rw [h, S.coordinate_root, S.coordinate_neighbor] at hh
    norm_num at hh
  have hlW : l ∈ W := Finset.mem_erase.mpr
    ⟨hlJ, Finset.mem_erase.mpr ⟨hlN, Finset.mem_erase.mpr ⟨hlR, Finset.mem_univ _⟩⟩⟩
  exact (hmin l hlW).not_gt hl.2

end CenteredCircle.AllN.AnchoredCircleSource

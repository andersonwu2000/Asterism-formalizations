import ACS12.ChartArc

/-! Complete exterior sums before and after any consecutive edge. -/

namespace CenteredCircle.AllN.AnchoredCircleSource

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (S : AnchoredCircleSource ι)

noncomputable def backwardExterior (K : ℝ → ℝ) (i : ι) : ℝ :=
  ∑ k, S.mass k * imageTail K S.period (S.forwardDistance k i)

noncomputable def forwardExterior (K : ℝ → ℝ) (i : ι) : ℝ :=
  ∑ k, S.mass k * imageTail K S.period (S.forwardDistance i k)

theorem forwardExterior_edge (K : ℝ → ℝ) {i j : ι}
    (hij : S.coordinate i < S.coordinate j)
    (hEmpty : ∀ k, ¬(S.coordinate i < S.coordinate k ∧ S.coordinate k < S.coordinate j))
    (hSum : Summable (fun t : ℕ => K (S.forwardDistance i j + t * S.period))) :
    S.forwardExterior K i = S.mass j * K (S.forwardDistance i j) +
      S.forwardExterior (fun t => K (t + S.forwardDistance i j)) j := by
  let h := S.forwardDistance i j
  have hn : i ≠ j := fun he => (lt_irrefl _) (he ▸ hij)
  rw [forwardExterior, forwardExterior, ← Finset.sum_erase_add _ _ (Finset.mem_univ j),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  have hPart : (∑ k ∈ Finset.univ.erase j, S.mass k * imageTail K S.period (S.forwardDistance i k)) =
      ∑ k ∈ Finset.univ.erase j, S.mass k * imageTail (fun t => K (t + h)) S.period
        (S.forwardDistance j k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [imageTail_shift]
    have hkj := (Finset.mem_erase.mp hk).1
    by_cases hki : k = i
    · subst k
      rw [S.forwardDistance_flip hn, S.forwardDistance_self]
      congr 2
      dsimp only [h]
      ring
    · rw [(S.consecutive_distance_split hij hEmpty hki hkj).1]
  rw [hPart, S.forwardDistance_self, imageTail_shift, imageTail_split K _ _ hSum]
  simp only [h]
  rw [add_comm S.period (S.forwardDistance i j)]
  ring

theorem backwardExterior_edge (K : ℝ → ℝ) {i j : ι}
    (hij : S.coordinate i < S.coordinate j)
    (hEmpty : ∀ k, ¬(S.coordinate i < S.coordinate k ∧ S.coordinate k < S.coordinate j))
    (hSum : Summable (fun t : ℕ => K (S.forwardDistance i j + t * S.period))) :
    S.backwardExterior K j = S.mass i * K (S.forwardDistance i j) +
      S.backwardExterior (fun t => K (t + S.forwardDistance i j)) i := by
  let h := S.forwardDistance i j
  have hn : i ≠ j := fun he => (lt_irrefl _) (he ▸ hij)
  rw [backwardExterior, backwardExterior, ← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  have hPart : (∑ k ∈ Finset.univ.erase i, S.mass k * imageTail K S.period (S.forwardDistance k j)) =
      ∑ k ∈ Finset.univ.erase i, S.mass k * imageTail (fun t => K (t + h)) S.period
        (S.forwardDistance k i) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [imageTail_shift]
    have hki := (Finset.mem_erase.mp hk).1
    by_cases hkj : k = j
    · subst k
      rw [S.forwardDistance_flip hn, S.forwardDistance_self]
      congr 2
      dsimp only [h]
      ring
    · rw [(S.consecutive_distance_split hij hEmpty hki hkj).2]
  rw [hPart, S.forwardDistance_self, imageTail_shift, imageTail_split K _ _ hSum]
  simp only [h]
  rw [add_comm S.period (S.forwardDistance i j)]
  ring

end CenteredCircle.AllN.AnchoredCircleSource

import CenteredCircle.PhysicalProjection
import Mathlib.Data.Finset.Max

/-!
Elementary circular distance and the density-maximal ordered pair. Maximizing
over all pairs is equivalent to maximizing mass / nearest-neighbor spacing,
and avoids making an unproved cyclic-enumeration choice.
-/

namespace CenteredCircle.AllN

noncomputable def shortArc (P a b : ℝ) : ℝ := min |b - a| (P - |b - a|)

theorem shortArc_symm (P a b : ℝ) : shortArc P a b = shortArc P b a := by
  simp only [shortArc, abs_sub_comm b a]

theorem shortArc_le_half (P a b : ℝ) : shortArc P a b ≤ P / 2 := by
  unfold shortArc
  apply min_le_iff.mpr
  rcases le_total |b - a| (P / 2) with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

theorem shortArc_pos {P a b : ℝ} (ha0 : 0 ≤ a) (haP : a < P)
    (hb0 : 0 ≤ b) (hbP : b < P) (hab : a ≠ b) : 0 < shortArc P a b := by
  apply lt_min
  · exact abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hab))
  · apply sub_pos.mpr
    rw [abs_lt]
    constructor <;> linarith

theorem normalized_mass_cap {mi ma di da : ℝ} (hma : 0 < ma) (hdi : 0 < di) (hda : 0 < da)
    (h : mi / di ≤ ma / da) : mi / ma ≤ di / da := by
  have hcross : mi * da ≤ ma * di := (div_le_div_iff₀ hdi hda).mp h
  apply (div_le_div_iff₀ hma hda).mpr
  simpa only [mul_comm] using hcross

theorem exists_density_maximal_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a m : ι → ℝ) {P : ℝ} (ha0 : ∀ i, 0 ≤ a i) (haP : ∀ i, a i < P)
    (hinj : Function.Injective a) (hm : ∀ i, 0 < m i) (hn : 1 < Fintype.card ι) :
    ∃ r b : ι, r ≠ b ∧ 0 < shortArc P (a r) (a b) ∧ shortArc P (a r) (a b) ≤ P / 2 ∧
      m b ≤ m r ∧ ∀ i j, i ≠ j →
        m i / m r ≤ shortArc P (a i) (a j) / shortArc P (a r) (a b) := by
  classical
  let S : Finset (ι × ι) := Finset.univ.filter (fun p => p.1 ≠ p.2)
  have htwo : ∃ r b : ι, r ≠ b := Fintype.one_lt_card_iff.mp hn
  have hS : S.Nonempty := by
    obtain ⟨r, b, hrb⟩ := htwo
    exact ⟨(r, b), by simp [S, hrb]⟩
  obtain ⟨p, hp, hpmax⟩ := S.exists_max_image
    (fun p : ι × ι => m p.1 / shortArc P (a p.1) (a p.2)) hS
  have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
  have hd (i j : ι) (hij : i ≠ j) : 0 < shortArc P (a i) (a j) :=
    shortArc_pos (ha0 i) (haP i) (ha0 j) (haP j) (hinj.ne hij)
  have hcap (i j : ι) (hij : i ≠ j) :
      m i / m p.1 ≤ shortArc P (a i) (a j) / shortArc P (a p.1) (a p.2) := by
    apply normalized_mass_cap (hm p.1) (hd i j hij) (hd _ _ hne)
    exact hpmax (i, j) (by simp [S, hij])
  refine ⟨p.1, p.2, hne, hd _ _ hne, shortArc_le_half _ _ _, ?_, hcap⟩
  have hb := hcap p.2 p.1 (Ne.symm hne)
  rw [shortArc_symm P (a p.2) (a p.1), div_self (ne_of_gt (hd _ _ hne))] at hb
  exact (div_le_one (hm p.1)).mp hb

theorem density_pair_period_ge_two {P d : ℝ} (hd : 0 < d) (hhalf : d ≤ P / 2) :
    2 ≤ P / d := by
  apply (le_div_iff₀ hd).mpr
  linarith

end CenteredCircle.AllN

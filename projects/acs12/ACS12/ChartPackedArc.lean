import ACS12.ChartHeadPacking

/-! The original packing bounds after moving the boundary to any occupied site. -/

namespace CenteredCircle.AllN.AnchoredCircleSource

variable {ι : Type*} [DecidableEq ι] (S : AnchoredCircleSource ι)

private theorem forwardDistance_circular_caps (hcaps : S.HasCircularMassCaps)
    (i j k : ι) (hjk : j ≠ k) :
    S.mass j ≤ |S.forwardDistance i k - S.forwardDistance i j| ∧
      S.mass j ≤ S.period - |S.forwardDistance i k - S.forwardDistance i j| := by
  by_cases hji : j = i
  · subst j
    rw [S.forwardDistance_self, abs_of_nonpos (sub_nonpos.mpr (S.forwardDistance_le_period i k)),
      neg_sub, ← S.forwardDistance_flip hjk]
    exact ⟨(S.forwardDistance_caps hcaps hjk.symm).2,
      by rw [S.forwardDistance_flip hjk]; simpa using (S.forwardDistance_caps hcaps hjk).1⟩
  by_cases hki : k = i
  · subst k
    rw [S.forwardDistance_self, abs_of_nonneg (sub_nonneg.mpr (S.forwardDistance_le_period i j)),
      ← S.forwardDistance_flip hjk.symm]
    exact ⟨(S.forwardDistance_caps hcaps hjk).1,
      by rw [S.forwardDistance_flip hjk.symm]; simpa using (S.forwardDistance_caps hcaps hjk.symm).2⟩
  simp only [forwardDistance, if_neg (Ne.symm hji), if_neg (Ne.symm hki)]
  rcases clockwiseArc_difference_abs (r := S.coordinate i) (S.coordinate_nonneg j)
      (S.coordinate_lt_period j) (S.coordinate_nonneg k) (S.coordinate_lt_period k) with h | h
  · rw [h]
    exact hcaps j k hjk
  · rw [h]
    obtain ⟨h₁, h₂⟩ := hcaps j k hjk
    exact ⟨h₂, by linarith⟩

private theorem backwardDistance_circular_caps (hcaps : S.HasCircularMassCaps)
    (i j k : ι) (hjk : j ≠ k) :
    S.mass j ≤ |S.forwardDistance k i - S.forwardDistance j i| ∧
      S.mass j ≤ S.period - |S.forwardDistance k i - S.forwardDistance j i| := by
  by_cases hji : j = i
  · subst j
    rw [S.forwardDistance_self, abs_of_nonpos (sub_nonpos.mpr (S.forwardDistance_le_period k i)),
      neg_sub, S.forwardDistance_flip hjk, sub_sub_cancel]
    exact ⟨(S.forwardDistance_caps hcaps hjk).1,
      by rw [← S.forwardDistance_flip hjk]; exact (S.forwardDistance_caps hcaps hjk.symm).2⟩
  by_cases hki : k = i
  · subst k
    rw [S.forwardDistance_self, abs_of_nonneg (sub_nonneg.mpr (S.forwardDistance_le_period j i)),
      S.forwardDistance_flip hjk.symm, sub_sub_cancel]
    exact ⟨(S.forwardDistance_caps hcaps hjk.symm).2,
      by rw [← S.forwardDistance_flip hjk.symm]; exact (S.forwardDistance_caps hcaps hjk).1⟩
  rw [S.forwardDistance_flip (Ne.symm hki), S.forwardDistance_flip (Ne.symm hji),
    show S.period - S.forwardDistance i k - (S.period - S.forwardDistance i j) =
      -(S.forwardDistance i k - S.forwardDistance i j) by ring, abs_neg]
  exact S.forwardDistance_circular_caps hcaps i j k hjk

private theorem mass_le_period [Nontrivial ι] (hcaps : S.HasCircularMassCaps) (j : ι) :
    S.mass j ≤ S.period := by
  obtain ⟨i, hi⟩ := exists_ne j
  exact ((S.forwardDistance_caps hcaps hi.symm).1).trans (S.forwardDistance_le_period j i)

private theorem mass_le_forwardDistance [Nontrivial ι] (hcaps : S.HasCircularMassCaps) (i j : ι) :
    S.mass j ≤ S.forwardDistance i j := by
  by_cases h : i = j
  · rw [h, S.forwardDistance_self]
    exact S.mass_le_period hcaps j
  · exact (S.forwardDistance_caps hcaps h).2

private theorem mass_le_backwardDistance [Nontrivial ι] (hcaps : S.HasCircularMassCaps) (i j : ι) :
    S.mass j ≤ S.forwardDistance j i := by
  by_cases h : j = i
  · rw [h, S.forwardDistance_self]
    exact S.mass_le_period hcaps i
  · exact (S.forwardDistance_caps hcaps h).1

variable [Fintype ι] [Nontrivial ι]

theorem forwardExterior_le_head (hcaps : S.HasCircularMassCaps) {K : ℝ → ℝ}
    {d s : ℝ} (hd : 0 < d) (hK : QuadratureData K d) (i j : ι)
    (hfirst : ∀ k, S.forwardDistance i j ≤ S.forwardDistance i k)
    (hdj : d ≤ S.forwardDistance i j) (hs : 0 < s) (hms : S.mass j ≤ s) :
    S.forwardExterior K i ≤ samplingHead K (S.forwardDistance i j) s := by
  have hcap := S.forwardDistance_circular_caps hcaps i
  have hinj : Function.Injective (S.forwardDistance i) := by
    intro k l he
    by_contra hne
    have h := (hcap k l hne).1
    rw [he, sub_self, abs_zero] at h
    exact (S.mass_pos k).not_ge h
  exact periodic_source_head_bound hK hd S.period_pos (S.forwardDistance i) S.mass
    (S.forwardDistance_le_period i) (fun k => hdj.trans (hfirst k)) hinj
    (fun k => (S.mass_pos k).le) (S.mass_le_forwardDistance hcaps i) hcap j hs hfirst hms

theorem backwardExterior_le_head (hcaps : S.HasCircularMassCaps) {K : ℝ → ℝ}
    {d s : ℝ} (hd : 0 < d) (hK : QuadratureData K d) (i j : ι)
    (hfirst : ∀ k, S.forwardDistance j i ≤ S.forwardDistance k i)
    (hdj : d ≤ S.forwardDistance j i) (hs : 0 < s) (hms : S.mass j ≤ s) :
    S.backwardExterior K i ≤ samplingHead K (S.forwardDistance j i) s := by
  have hcap := S.backwardDistance_circular_caps hcaps i
  have hinj : Function.Injective (fun k => S.forwardDistance k i) := by
    intro k l he
    change S.forwardDistance k i = S.forwardDistance l i at he
    by_contra hne
    have h := (hcap k l hne).1
    rw [he, sub_self, abs_zero] at h
    exact (S.mass_pos k).not_ge h
  exact periodic_source_head_bound hK hd S.period_pos (fun k => S.forwardDistance k i) S.mass
    (fun k => S.forwardDistance_le_period k i) (fun k => hdj.trans (hfirst k)) hinj
    (fun k => (S.mass_pos k).le) (S.mass_le_backwardDistance hcaps i) hcap j hs hfirst hms

theorem forwardExterior_le_tail (hcaps : S.HasCircularMassCaps) {K : ℝ → ℝ}
    (i : ι) (hK : QuadratureData K (S.mass i)) :
    S.forwardExterior K i ≤ samplingTail K 0 (S.mass i) := by
  have hcap := S.forwardDistance_circular_caps hcaps i
  have hinj : Function.Injective (S.forwardDistance i) := by
    intro k l he
    by_contra hne
    have h := (hcap k l hne).1
    rw [he, sub_self, abs_zero] at h
    exact (S.mass_pos k).not_ge h
  have hdom (k : ι) : S.mass i ≤ S.forwardDistance i k := by
    by_cases h : i = k
    · rw [← h, S.forwardDistance_self]
      exact S.mass_le_period hcaps i
    · exact (S.forwardDistance_caps hcaps h).1
  exact periodic_source_quadrature hK (S.mass_pos i) S.period_pos (S.forwardDistance i) S.mass
    (S.forwardDistance_le_period i) hdom hinj (fun k => (S.mass_pos k).le)
    (S.mass_le_forwardDistance hcaps i) hcap

theorem backwardExterior_le_tail (hcaps : S.HasCircularMassCaps) {K : ℝ → ℝ}
    (i : ι) (hK : QuadratureData K (S.mass i)) :
    S.backwardExterior K i ≤ samplingTail K 0 (S.mass i) := by
  have hcap := S.backwardDistance_circular_caps hcaps i
  have hinj : Function.Injective (fun k => S.forwardDistance k i) := by
    intro k l he
    change S.forwardDistance k i = S.forwardDistance l i at he
    by_contra hne
    have h := (hcap k l hne).1
    rw [he, sub_self, abs_zero] at h
    exact (S.mass_pos k).not_ge h
  have hdom (k : ι) : S.mass i ≤ S.forwardDistance k i := by
    by_cases h : k = i
    · rw [h, S.forwardDistance_self]
      exact S.mass_le_period hcaps i
    · exact (S.forwardDistance_caps hcaps h).2
  exact periodic_source_quadrature hK (S.mass_pos i) S.period_pos (fun k => S.forwardDistance k i)
    S.mass (fun k => S.forwardDistance_le_period k i) hdom hinj (fun k => (S.mass_pos k).le)
    (S.mass_le_backwardDistance hcaps i) hcap

end CenteredCircle.AllN.AnchoredCircleSource

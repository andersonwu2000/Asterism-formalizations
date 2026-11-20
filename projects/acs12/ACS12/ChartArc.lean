import CenteredCircle.PhysicalNormalization

/-! Forward distances and consecutive edges in the attained incident chart. -/

namespace CenteredCircle.AllN.AnchoredCircleSource

variable {ι : Type*} [DecidableEq ι] (S : AnchoredCircleSource ι)

/-- The forward distance uses the first positive image at a repeated site. -/
noncomputable def forwardDistance (i j : ι) : ℝ :=
  if i = j then S.period else clockwiseArc S.period (S.coordinate i) (S.coordinate j)

@[simp] theorem forwardDistance_self (i : ι) : S.forwardDistance i i = S.period := by
  simp [forwardDistance]

theorem forwardDistance_eq_sub {i j : ι} (h : S.coordinate i < S.coordinate j) :
    S.forwardDistance i j = S.coordinate j - S.coordinate i := by
  have hne : i ≠ j := fun he => (lt_irrefl _) (he ▸ h)
  simp [forwardDistance, hne, clockwiseArc, h.le]

theorem forwardDistance_eq_wrap {i j : ι} (h : S.coordinate j < S.coordinate i) :
    S.forwardDistance i j = S.coordinate j - S.coordinate i + S.period := by
  have hne : i ≠ j := fun he => (lt_irrefl _) (he ▸ h)
  simp [forwardDistance, hne, clockwiseArc, not_le.mpr h]

theorem forwardDistance_pos (i j : ι) : 0 < S.forwardDistance i j := by
  by_cases hij : i = j
  · simpa only [hij, forwardDistance_self] using S.period_pos
  · rw [forwardDistance, if_neg hij]
    exact clockwiseArc_pos (S.coordinate_nonneg i) (S.coordinate_lt_period i)
      (S.coordinate_nonneg j) (S.coordinate_lt_period j) (S.coordinate_injective.ne hij)

theorem forwardDistance_lt_period {i j : ι} (hij : i ≠ j) :
    S.forwardDistance i j < S.period := by
  rw [forwardDistance, if_neg hij]
  exact (clockwiseArc_range (S.coordinate_nonneg i) (S.coordinate_lt_period i)
    (S.coordinate_nonneg j) (S.coordinate_lt_period j)).2

theorem forwardDistance_flip {i j : ι} (hij : i ≠ j) :
    S.forwardDistance j i = S.period - S.forwardDistance i j := by
  rcases lt_or_gt_of_ne (S.coordinate_injective.ne hij) with h | h
  · rw [S.forwardDistance_eq_wrap h, S.forwardDistance_eq_sub h]
    ring
  · rw [S.forwardDistance_eq_sub h, S.forwardDistance_eq_wrap h]
    ring

theorem forwardDistance_caps (hcaps : S.HasCircularMassCaps) {i j : ι} (hij : i ≠ j) :
    S.mass i ≤ S.forwardDistance i j ∧ S.mass j ≤ S.forwardDistance i j := by
  have hi := hcaps i j hij
  have hj := hcaps j i hij.symm
  rw [abs_sub_comm] at hj
  rcases lt_or_gt_of_ne (S.coordinate_injective.ne hij) with h | h
  · rw [S.forwardDistance_eq_sub h]
    rw [abs_of_pos (sub_pos.mpr h)] at hi hj
    exact ⟨hi.1, hj.1⟩
  · rw [S.forwardDistance_eq_wrap h]
    rw [abs_of_neg (sub_neg.mpr h)] at hi hj
    constructor <;> linarith [hi.2, hj.2]

theorem consecutive_distance_split {i j k : ι} (hij : S.coordinate i < S.coordinate j)
    (h : ∀ l, ¬(S.coordinate i < S.coordinate l ∧ S.coordinate l < S.coordinate j))
    (hki : k ≠ i) (hkj : k ≠ j) :
    S.forwardDistance i k = S.forwardDistance j k + S.forwardDistance i j ∧
      S.forwardDistance k j = S.forwardDistance k i + S.forwardDistance i j := by
  have hout : S.coordinate k < S.coordinate i ∨ S.coordinate j < S.coordinate k := by
    rcases lt_or_gt_of_ne (S.coordinate_injective.ne hki) with hk | hk
    · exact Or.inl hk
    · exact Or.inr (lt_of_le_of_ne (le_of_not_gt (fun hk' => h k ⟨hk, hk'⟩))
        (S.coordinate_injective.ne hkj.symm))
  rw [S.forwardDistance_eq_sub hij]
  rcases hout with hk | hk
  · rw [S.forwardDistance_eq_wrap hk, S.forwardDistance_eq_wrap (hk.trans hij),
      S.forwardDistance_eq_sub (hk.trans hij), S.forwardDistance_eq_sub hk]
    constructor <;> ring
  · rw [S.forwardDistance_eq_sub (hij.trans hk), S.forwardDistance_eq_sub hk,
      S.forwardDistance_eq_wrap hk, S.forwardDistance_eq_wrap (hij.trans hk)]
    constructor <;> ring


theorem forwardDistance_adjacent_split {i j k : ι} (hij : i ≠ j) (hik : i ≠ k)
    (h : S.forwardDistance i j < S.forwardDistance i k) :
    S.forwardDistance i k = S.forwardDistance j k + S.forwardDistance i j := by
  rcases lt_or_gt_of_ne (S.coordinate_injective.ne hij) with hI | hI <;>
    rcases lt_or_gt_of_ne (S.coordinate_injective.ne hik) with hK | hK
  · rw [S.forwardDistance_eq_sub hI,S.forwardDistance_eq_sub hK] at h ⊢
    have hJ : S.coordinate j < S.coordinate k := by linarith only [h]
    rw [S.forwardDistance_eq_sub hJ]
    ring
  · rw [S.forwardDistance_eq_sub hI,S.forwardDistance_eq_wrap hK,S.forwardDistance_eq_wrap (hK.trans hI)]
    ring
  · rw [S.forwardDistance_eq_wrap hI,S.forwardDistance_eq_sub hK] at h
    exfalso
    linarith only [h,S.coordinate_lt_period k,S.coordinate_nonneg j]
  · rw [S.forwardDistance_eq_wrap hI,S.forwardDistance_eq_wrap hK] at h ⊢
    have hJ : S.coordinate j < S.coordinate k := by linarith only [h]
    rw [S.forwardDistance_eq_sub hJ]
    ring


theorem forwardDistance_le_period (i j : ι) : S.forwardDistance i j ≤ S.period := by
  by_cases h : i = j
  · simp [h]
  · exact (S.forwardDistance_lt_period h).le

theorem forwardDistance_injective (i : ι) : Function.Injective (S.forwardDistance i) := by
  intro j k h
  by_cases hj : j = i
  · subst j
    by_contra hk
    rw [S.forwardDistance_self] at h
    exact (ne_of_lt (S.forwardDistance_lt_period hk)) h.symm
  by_cases hk : k = i
  · subst k
    rw [S.forwardDistance_self] at h
    exact ((ne_of_lt (S.forwardDistance_lt_period (Ne.symm hj))) h).elim
  rcases lt_or_gt_of_ne (S.coordinate_injective.ne (Ne.symm hj)) with hJ | hJ <;>
    rcases lt_or_gt_of_ne (S.coordinate_injective.ne (Ne.symm hk)) with hK | hK
  · rw [S.forwardDistance_eq_sub hJ,S.forwardDistance_eq_sub hK] at h
    exact S.coordinate_injective (by linarith only [h])
  · rw [S.forwardDistance_eq_sub hJ,S.forwardDistance_eq_wrap hK] at h
    exact (by linarith only [h,S.coordinate_lt_period j,S.coordinate_nonneg k] : False).elim
  · rw [S.forwardDistance_eq_wrap hJ,S.forwardDistance_eq_sub hK] at h
    exact (by linarith only [h,S.coordinate_lt_period k,S.coordinate_nonneg j] : False).elim
  · rw [S.forwardDistance_eq_wrap hJ,S.forwardDistance_eq_wrap hK] at h
    exact S.coordinate_injective (by linarith only [h])

theorem backwardDistance_injective (i : ι) : Function.Injective (fun j => S.forwardDistance j i) := by
  intro j k h
  change S.forwardDistance j i = S.forwardDistance k i at h
  by_cases hj : j = i
  · subst j
    by_contra hk
    rw [S.forwardDistance_self] at h
    exact (ne_of_lt (S.forwardDistance_lt_period (Ne.symm hk))) h.symm
  by_cases hk : k = i
  · subst k
    rw [S.forwardDistance_self] at h
    exact ((ne_of_lt (S.forwardDistance_lt_period hj)) h).elim
  apply S.forwardDistance_injective i
  rw [S.forwardDistance_flip hj,S.forwardDistance_flip hk,h]

end CenteredCircle.AllN.AnchoredCircleSource

namespace CenteredCircle.AllN.NormalizedCircleChart

variable {ι : Type*} [DecidableEq ι] {a m : ι → ℝ}
    (C : NormalizedCircleChart a m (2 * Real.pi))

theorem forward_pair_phase {i j : ι} (hij : i ≠ j) :
    unitRay (C.scale * C.source.coordinate j - C.scale * C.source.coordinate i) =
      unitRay (2 * Real.pi * C.source.forwardDistance i j / C.source.period) := by
  rw [C.kernel_angle]
  rcases lt_or_gt_of_ne (C.source.coordinate_injective.ne hij) with h | h
  · rw [C.source.forwardDistance_eq_sub h, mul_sub]
  · rw [C.source.forwardDistance_eq_wrap h, mul_add, mul_sub, C.scale_mul_period, unitRay_periodic]

end CenteredCircle.AllN.NormalizedCircleChart

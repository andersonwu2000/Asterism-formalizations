import CenteredCircle.CircularSpacing

/-! Recentering and orientation on a circle, with exact distance preservation. -/

namespace CenteredCircle.AllN

noncomputable def clockwiseArc (P a b : ℝ) : ℝ :=
  if a ≤ b then b - a else b - a + P

theorem clockwiseArc_self (P a : ℝ) : clockwiseArc P a a = 0 := by simp [clockwiseArc]

theorem clockwiseArc_range {P a b : ℝ} (ha0 : 0 ≤ a) (haP : a < P)
    (hb0 : 0 ≤ b) (hbP : b < P) :
    0 ≤ clockwiseArc P a b ∧ clockwiseArc P a b < P := by
  unfold clockwiseArc
  split_ifs with h <;> constructor <;> linarith

theorem clockwiseArc_pos {P a b : ℝ} (ha0 : 0 ≤ a) (haP : a < P)
    (hb0 : 0 ≤ b) (hbP : b < P) (hne : a ≠ b) :
    0 < clockwiseArc P a b := by
  unfold clockwiseArc
  split_ifs with h
  · exact sub_pos.mpr (lt_of_le_of_ne h hne)
  · linarith

theorem clockwiseArc_shortArc {P a b : ℝ} (ha0 : 0 ≤ a) (haP : a < P)
    (hb0 : 0 ≤ b) (hbP : b < P) :
    min (clockwiseArc P a b) (P - clockwiseArc P a b) = shortArc P a b := by
  by_cases h : a ≤ b
  · simp only [clockwiseArc, if_pos h, shortArc, abs_of_nonneg (sub_nonneg.mpr h)]
  · have hab : b - a ≤ 0 := by linarith
    simp only [clockwiseArc, if_neg h, shortArc, abs_of_nonpos hab]
    rw [show P - (b - a + P) = a - b by ring,
      show -(b - a) = a - b by ring, show b - a + P = P - (a - b) by ring, min_comm]

theorem clockwiseArc_difference_abs {P r a b : ℝ}
    (ha0 : 0 ≤ a) (haP : a < P) (hb0 : 0 ≤ b) (hbP : b < P) :
    |clockwiseArc P r b - clockwiseArc P r a| = |b - a| ∨
    |clockwiseArc P r b - clockwiseArc P r a| = P - |b - a| := by
  by_cases ha : r ≤ a
  · by_cases hb : r ≤ b
    · left
      simp only [clockwiseArc, if_pos ha, if_pos hb]
      congr 1
      ring
    · right
      simp only [clockwiseArc, if_pos ha, if_neg hb]
      rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
      ring
  · by_cases hb : r ≤ b
    · right
      simp only [clockwiseArc, if_neg ha, if_pos hb]
      rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
      ring
    · left
      simp only [clockwiseArc, if_neg ha, if_neg hb]
      congr 1
      ring

theorem clockwiseArc_shortArc_preserved {P r a b : ℝ}
    (ha0 : 0 ≤ a) (haP : a < P) (hb0 : 0 ≤ b) (hbP : b < P) :
    shortArc P (clockwiseArc P r a) (clockwiseArc P r b) = shortArc P a b := by
  rcases clockwiseArc_difference_abs (r := r) ha0 haP hb0 hbP with h | h
  · simp only [shortArc, h]
  · simp only [shortArc, h]
    rw [show P - (P - |b - a|) = |b - a| by ring, min_comm]

noncomputable def reverseCircle (P x : ℝ) : ℝ := if x = 0 then 0 else P - x

theorem reverseCircle_zero (P : ℝ) : reverseCircle P 0 = 0 := by simp [reverseCircle]

theorem reverseCircle_range {P x : ℝ} (hP : 0 < P) (hx0 : 0 ≤ x) (hxP : x < P) :
    0 ≤ reverseCircle P x ∧ reverseCircle P x < P := by
  unfold reverseCircle
  split_ifs with h
  · exact ⟨le_rfl, hP⟩
  · constructor <;> linarith [lt_of_le_of_ne hx0 (Ne.symm h)]

theorem reverseCircle_shortArc_preserved {P a b : ℝ}
    (ha0 : 0 ≤ a) (haP : a < P) (hb0 : 0 ≤ b) (hbP : b < P) :
    shortArc P (reverseCircle P a) (reverseCircle P b) = shortArc P a b := by
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · subst b
      simp only [reverseCircle_zero]
    · have hab : 0 ≤ P - b := by linarith
      simp only [reverseCircle_zero, reverseCircle, if_neg hb, ite_true, shortArc, sub_zero,
        abs_of_nonneg hab, abs_of_nonneg hb0]
      rw [show P - (P - b) = b by ring, min_comm]
  · by_cases hb : b = 0
    · subst b
      have haa : 0 ≤ P - a := by linarith
      simp only [reverseCircle_zero, reverseCircle, if_neg ha, ite_true, shortArc, zero_sub,
        abs_neg, abs_of_nonneg haa, abs_of_nonneg ha0]
      rw [show P - (P - a) = a by ring, min_comm]
    · simp only [reverseCircle, if_neg ha, if_neg hb, shortArc]
      rw [show P - b - (P - a) = -(b - a) by ring, abs_neg]

noncomputable def orientedCircle (P r : ℝ) (forward : Bool) (x : ℝ) : ℝ :=
  if forward then clockwiseArc P r x else reverseCircle P (clockwiseArc P r x)

theorem orientedCircle_root (P r : ℝ) (forward : Bool) : orientedCircle P r forward r = 0 := by
  cases forward <;> simp [orientedCircle, clockwiseArc_self, reverseCircle_zero]

theorem orientedCircle_range {P r x : ℝ} (hP : 0 < P)
    (hr0 : 0 ≤ r) (hrP : r < P) (hx0 : 0 ≤ x) (hxP : x < P) (forward : Bool) :
    0 ≤ orientedCircle P r forward x ∧ orientedCircle P r forward x < P := by
  have h := clockwiseArc_range hr0 hrP hx0 hxP
  cases forward
  · exact reverseCircle_range hP h.1 h.2
  · exact h

theorem orientedCircle_shortArc {P r a b : ℝ} (hP : 0 < P)
    (hr0 : 0 ≤ r) (hrP : r < P) (ha0 : 0 ≤ a) (haP : a < P)
    (hb0 : 0 ≤ b) (hbP : b < P) (forward : Bool) :
    shortArc P (orientedCircle P r forward a) (orientedCircle P r forward b) = shortArc P a b := by
  have ha := clockwiseArc_range hr0 hrP ha0 haP
  have hb := clockwiseArc_range hr0 hrP hb0 hbP
  cases forward
  · exact (reverseCircle_shortArc_preserved ha.1 ha.2 hb.1 hb.2).trans
      (clockwiseArc_shortArc_preserved ha0 haP hb0 hbP)
  · exact clockwiseArc_shortArc_preserved ha0 haP hb0 hbP

theorem exists_short_orientation {P r b : ℝ} (hr0 : 0 ≤ r) (hrP : r < P)
    (hb0 : 0 ≤ b) (hbP : b < P) (hne : r ≠ b) :
    ∃ forward : Bool, orientedCircle P r forward b = shortArc P r b := by
  have hp := clockwiseArc_pos hr0 hrP hb0 hbP hne
  have he := clockwiseArc_shortArc hr0 hrP hb0 hbP
  rcases le_total (clockwiseArc P r b) (P - clockwiseArc P r b) with h | h
  · exact ⟨true, by simpa only [min_eq_left h] using he⟩
  · refine ⟨false, ?_⟩
    simpa only [orientedCircle, Bool.false_eq_true, if_false, reverseCircle,
      if_neg (ne_of_gt hp), min_eq_right h] using he

end CenteredCircle.AllN

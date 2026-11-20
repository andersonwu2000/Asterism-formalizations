import ACS12.FiniteUnimodalCapacity
import Mathlib.Analysis.Convex.Deriv

/-! The two triangles of the crossing primitive have a finite atom-pair realization.
The same cut is charged once, with each slice paid by its preceding occupation gaps. -/
namespace ACS12.HighCurrent

open Finset MeasureTheory

private theorem occupied_antitone_integral {ι : Type*} [DecidableEq ι]
    (t w : ι → ℝ) (S : Finset ι) {a b : ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b) (hCont : ContinuousOn f (Set.Icc a b))
    (hPos : ∀ x ∈ Set.Icc a b, 0 ≤ f x) (hAnti : AntitoneOn f (Set.Icc a b))
    (hDom : ∀ i ∈ S, t i ∈ Set.Icc a b)
    (hFirst : ∀ i ∈ S, w i ≤ t i - a)
    (hSep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → w i ≤ |t i - t j|) :
    (∑ i ∈ S, w i * f (t i)) ≤ ∫ x in a..b, f x := by
  suffices hAll : ∀ T : Finset ι, T ⊆ S → ∀ c ∈ Set.Icc a b,
      (∀ i ∈ T, c ≤ t i ∧ w i ≤ t i - c) →
      (∑ i ∈ T, w i * f (t i)) ≤ ∫ x in c..b, f x by
    exact hAll S Subset.rfl a ⟨le_rfl, hab⟩ (fun i hi => ⟨(hDom i hi).1, hFirst i hi⟩)
  intro T
  induction T using Finset.strongInductionOn
  rename_i T ih
  intro hTS c hc hDomC
  by_cases hT : T.Nonempty
  · obtain ⟨i, hi, hiMin⟩ := T.exists_min_image t hT
    have hti := hDom i (hTS hi)
    have hct := (hDomC i hi).1
    have hInt₁ : IntervalIntegrable f volume c (t i) :=
      (hCont.mono (by rw [Set.uIcc_of_le hct]; exact Set.Icc_subset_Icc hc.1 hti.2)).intervalIntegrable
    have hInt₂ : IntervalIntegrable f volume (t i) b :=
      (hCont.mono (by rw [Set.uIcc_of_le hti.2]; exact Set.Icc_subset_Icc_left hti.1)).intervalIntegrable
    have hPay : w i * f (t i) ≤ ∫ x in c..t i, f x := by
      have hLower := intervalIntegral.integral_mono_on hct (intervalIntegrable_const (c := f (t i)))
        hInt₁ (fun x hx => hAnti ⟨hc.1.trans hx.1, hx.2.trans hti.2⟩ hti hx.2)
      rw [intervalIntegral.integral_const, smul_eq_mul] at hLower
      exact (mul_le_mul_of_nonneg_right (hDomC i hi).2 (hPos _ hti)).trans hLower
    have hLater := ih (T.erase i) (erase_ssubset hi) (fun j hj => hTS (mem_of_mem_erase hj)) (t i) hti
      (fun j hj => by
        have hjT := mem_of_mem_erase hj
        have hOrd := hiMin j hjT
        have hGap := hSep j (hTS hjT) i (hTS hi) (mem_erase.mp hj).1
        exact ⟨hOrd, by rwa [abs_of_nonneg (sub_nonneg.mpr hOrd)] at hGap⟩)
    rw [← sum_erase_add T (fun j => w j * f (t j)) hi,
      ← intervalIntegral.integral_add_adjacent_intervals hInt₁ hInt₂]
    linarith only [hPay, hLater]
  · rw [not_nonempty_iff_eq_empty.mp hT, sum_empty]
    exact intervalIntegral.integral_nonneg hc.2 (fun x hx => hPos x ⟨hc.1.trans hx.1, hx.2⟩)

noncomputable def crossSlice (K : ℝ → ℝ) (t v : ℝ) : ℝ :=
  K (t + max t v) - K (2 * max t v) / 2

private theorem crossSlice_add (K : ℝ → ℝ) (t v : ℝ) :
    crossSlice K t v + crossSlice K v t = K (t + v) := by
  rcases le_total t v with h | h
  · simp only [crossSlice, max_eq_right h, max_eq_left h, show v + v = 2 * v by ring]
    ring
  · simp only [crossSlice, max_eq_left h, max_eq_right h, show t + t = 2 * t by ring, add_comm v t]
    ring

theorem crossSlice_nonneg {K : ℝ → ℝ} (hNon : ∀ s > 0, 0 ≤ K s)
    (hAnti : AntitoneOn K (Set.Ioi 0)) {t v : ℝ} (ht : 0 < t) :
    0 ≤ crossSlice K t v := by
  have hOrd : t + max t v ≤ 2 * max t v := by linarith only [le_max_left t v]
  have h₁ : 0 < t + max t v := by linarith only [ht, le_max_left t v]
  have h₂ : 0 < 2 * max t v := h₁.trans_le hOrd
  have h := hAnti h₁ h₂ hOrd
  unfold crossSlice
  linarith only [h, hNon _ h₂]

private theorem crossSlice_antitone {K : ℝ → ℝ} (hK : ConvexOn ℝ (Set.Ioi 0) K)
    {t : ℝ} (ht : 0 < t) : Antitone (crossSlice K t) := by
  intro u v huv
  let a := max t u
  let b := max t v
  have ha : t ≤ a := le_max_left _ _
  have hab : a ≤ b := max_le_max_left _ huv
  rcases hab.eq_or_lt with hab | hab
  · change K (t + b) - K (2 * b) / 2 ≤ K (t + a) - K (2 * a) / 2
    rw [hab]
  have hA : 0 < t + a := by linarith only [ht, ha]
  have hB : 0 < t + b := by linarith only [hA, hab]
  have hC : 0 < 2 * a := by linarith only [ht, ha]
  have hD : 0 < 2 * b := by linarith only [hC, hab]
  have h₁ := hK.secant_mono hA hB hD
    (by linarith only [hab] : t + b ≠ t + a)
    (by linarith only [ha, hab] : 2 * b ≠ t + a)
    (by linarith only [ha, hab] : t + b ≤ 2 * b)
  have h₂ := hK.secant_mono hD hA hC
    (by linarith only [ha, hab] : t + a ≠ 2 * b)
    (by linarith only [hab] : 2 * a ≠ 2 * b)
    (by linarith only [ha] : t + a ≤ 2 * a)
  have h₂' : (K (2 * b) - K (t + a)) / (2 * b - (t + a)) ≤
      (K (2 * b) - K (2 * a)) / (2 * b - 2 * a) := by
    rw [← neg_sub (K (t + a)) (K (2 * b)), ← neg_sub (t + a) (2 * b), neg_div_neg_eq,
      ← neg_sub (K (2 * a)) (K (2 * b)), ← neg_sub (2 * a) (2 * b), neg_div_neg_eq]
    exact h₂
  have hSlope : (K (t + b) - K (t + a)) / (b - a) ≤
      ((K (2 * b) - K (2 * a)) / 2) / (b - a) := by
    have h := h₁.trans h₂'
    rw [show t + b - (t + a) = b - a by ring, show 2 * b - 2 * a = 2 * (b - a) by ring] at h
    convert h using 1
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
    ring
  have h := (div_le_div_iff_of_pos_right (sub_pos.mpr hab)).mp hSlope
  change K (t + b) - K (2 * b) / 2 ≤ K (t + a) - K (2 * a) / 2
  linarith only [h]

/-- A finite two-sided current estimate. Division by the occupation scale
reduces each side to the same gap-integral bound. -/
theorem quartic_crossing_primitive {ι : Type*} [DecidableEq ι] (A B : Finset ι)
    (t s m : ι → ℝ) {L : ℝ} (hL : 0 ≤ L) {K : ℝ → ℝ}
    (hK : ConvexOn ℝ (Set.Ioi 0) K) (hCont : ContinuousOn K (Set.Ioi 0))
    (hNon : ∀ z > 0, 0 ≤ K z) (hAnti : AntitoneOn K (Set.Ioi 0))
    (hm : ∀ i ∈ A ∪ B, 0 < m i)
    (ht : ∀ i ∈ A, t i ∈ Set.Icc 0 L) (hs : ∀ j ∈ B, s j ∈ Set.Icc 0 L)
    (hAt : ∀ i ∈ A, m i ≤ t i) (hBs : ∀ j ∈ B, m j ≤ s j)
    (hPackA : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → m i ≤ |t i - t j|)
    (hPackB : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → m i ≤ |s i - s j|) :
    (∑ i ∈ A, ∑ j ∈ B, m i * m j * K (t i + s j)) ≤
      (∑ i ∈ A, m i * ∫ v in (0 : ℝ)..L, crossSlice K (t i) v) +
      (∑ j ∈ B, m j * ∫ v in (0 : ℝ)..L, crossSlice K (s j) v) := by
  have hPay (T : Finset ι) (x : ι → ℝ)
      (hx : ∀ i ∈ T, x i ∈ Set.Icc 0 L) (hFirst : ∀ i ∈ T, m i ≤ x i)
      (hPack : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → m i ≤ |x i - x j|)
      {z : ℝ} (hz : 0 < z) :
      (∑ i ∈ T, m i * crossSlice K z (x i)) ≤ ∫ v in (0 : ℝ)..L, crossSlice K z v := by
    apply occupied_antitone_integral x m T hL
    · unfold crossSlice
      apply ContinuousOn.sub
      · exact hCont.comp (by fun_prop) (fun v _ => by
          change 0 < z + max z v
          linarith only [hz, le_max_left z v])
      · apply ContinuousOn.div_const
        exact hCont.comp (by fun_prop) (fun v _ => by
          change 0 < 2 * max z v
          linarith only [hz, le_max_left z v])
    · exact fun _ _ => crossSlice_nonneg hNon hAnti hz
    · exact (crossSlice_antitone hK hz).antitoneOn _
    · exact hx
    · simpa only [sub_zero] using hFirst
    · exact hPack
  have hA (i : ι) (hi : i ∈ A) : 0 < t i := (hm i (mem_union_left _ hi)).trans_le (hAt i hi)
  have hB (j : ι) (hj : j ∈ B) : 0 < s j := (hm j (mem_union_right _ hj)).trans_le (hBs j hj)
  have h₁ := sum_le_sum (s := A) (fun i hi =>
    mul_le_mul_of_nonneg_left (hPay B s hs hBs hPackB (hA i hi))
      (hm i (mem_union_left _ hi)).le)
  have h₂ := sum_le_sum (s := B) (fun j hj =>
    mul_le_mul_of_nonneg_left (hPay A t ht hAt hPackA (hB j hj))
      (hm j (mem_union_right _ hj)).le)
  calc
    _ = (∑ i ∈ A, m i * ∑ j ∈ B, m j * crossSlice K (t i) (s j)) +
        (∑ j ∈ B, m j * ∑ i ∈ A, m i * crossSlice K (s j) (t i)) := by
      simp only [mul_sum]
      rw [sum_comm (s := B), ← sum_add_distrib]
      apply sum_congr rfl
      intro i _
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro j _
      rw [← crossSlice_add K (t i) (s j)]
      ring
    _ ≤ _ := add_le_add h₁ h₂

/-- The whole truncated kernel is integrated exactly, including the endpoint of support. -/
theorem crossSlice_integral {K : ℝ → ℝ} {t L : ℝ}
    (ht : 0 < t) (htL : t ≤ L)
    (hCont : ContinuousOn K (Set.Ioi 0)) (hZero : ∀ x, L ≤ x → K x = 0) :
    (∫ v in (0 : ℝ)..L, crossSlice K t v) =
      t / 2 * K (2 * t) + (3 / 4) * ∫ v in (2 * t)..(2 * L), K v := by
  have hC : Continuous fun v => crossSlice K t v := by
    apply continuous_iff_continuousAt.mpr
    intro v
    unfold crossSlice
    apply ContinuousAt.sub
    · exact (hCont.continuousAt (Ioi_mem_nhds (by linarith only [ht, le_max_left t v]))).comp
        (by fun_prop)
    · apply ContinuousAt.div_const
      exact (hCont.continuousAt (Ioi_mem_nhds (by linarith only [ht, le_max_left t v]))).comp
        (by fun_prop)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hC.intervalIntegrable (μ := volume) 0 t) (hC.intervalIntegrable (μ := volume) t L)]
  have hStart : (∫ v in (0 : ℝ)..t, crossSlice K t v) = t / 2 * K (2 * t) := by
    calc
      _ = ∫ _v in (0 : ℝ)..t, K (2 * t) / 2 := by
        apply intervalIntegral.integral_congr
        intro v hv
        rw [Set.uIcc_of_le ht.le] at hv
        unfold crossSlice
        rw [max_eq_left hv.2, show t + t = 2 * t by ring]
        ring
      _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]; ring
  let f (v : ℝ) := K (t + v)
  let g (v : ℝ) := K (2 * v) / 2
  have hf : IntervalIntegrable f volume t L := by
    apply ContinuousOn.intervalIntegrable
    apply hCont.comp (by fun_prop)
    intro v hv
    rw [Set.uIcc_of_le htL] at hv
    change 0 < t + v
    linarith only [ht, hv.1]
  have hg : IntervalIntegrable g volume t L := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div_const
    apply hCont.comp (by fun_prop)
    intro v hv
    rw [Set.uIcc_of_le htL] at hv
    change 0 < 2 * v
    linarith only [ht, hv.1]
  have hEnd : (∫ v in t..L, crossSlice K t v) = (3 / 4) * ∫ v in (2 * t)..(2 * L), K v := by
    have hFn : (∫ v in t..L, crossSlice K t v) = ∫ v in t..L, f v - g v := by
      apply intervalIntegral.integral_congr
      intro v hv
      rw [Set.uIcc_of_le htL] at hv
      simp only [crossSlice, max_eq_right hv.1, f, g]
    rw [hFn, intervalIntegral.integral_sub hf hg]
    dsimp only [f, g]
    rw [intervalIntegral.integral_comp_add_left, intervalIntegral.integral_div,
      intervalIntegral.integral_comp_mul_left K (by norm_num : (2 : ℝ) ≠ 0), smul_eq_mul,
      show t + t = 2 * t by ring]
    have hEq : (∫ v in (2 * t)..(t + L), K v) = ∫ v in (2 * t)..(2 * L), K v := by
      have hI {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : IntervalIntegrable K volume a b :=
        (hCont.mono (by rw [Set.uIcc_of_le hab]; exact fun _ hx => ha.trans_le hx.1)).intervalIntegrable
      have hZ : (∫ v in (t + L)..(2 * L), K v) = 0 := by
        rw [← intervalIntegral.integral_zero]
        apply intervalIntegral.integral_congr
        intro v hv
        rw [Set.uIcc_of_le (show t + L ≤ 2 * L by linarith only [htL])] at hv
        exact hZero v (by linarith only [ht, hv.1])
      have hAdd := intervalIntegral.integral_add_adjacent_intervals
        (hI (by positivity : 0 < 2 * t) (by linarith only [htL] : 2 * t ≤ t + L))
        (hI (by linarith only [ht, htL] : 0 < t + L) (by linarith only [htL] : t + L ≤ 2 * L))
      exact (by simpa only [hZ, add_zero] using hAdd)
    rw [hEq]
    ring
  rw [hStart, hEnd]

end ACS12.HighCurrent

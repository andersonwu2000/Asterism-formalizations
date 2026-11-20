import ACS12.PureAdjacentCapConvex
import ACS12.PureAdjacentContact
import ACS12.PureAdjacentEndpoint

/-! The whole-band cubic adjacent source cap, including its cap/u contact. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN Set

private theorem pureStacks_one_sum {p : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) :
    pureAStack p 1 + pureBStack p 1 = p := by
  have hθ : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have h := lawPeanoTail_total hp hp₂ zero_lt_one hθ zero_lt_one
  have hA : samplingTail (lawPeanoKernel p 1 0 1 .a) 0 1 = pureAStack p 1 := by
    rw [samplingTail_eq_shift, zero_add, pureAStack]
    unfold samplingHead
    apply congrArg ((1 : ℝ) * ·)
    apply tsum_congr
    intro j
    exact (lawPeanoKernel_zero hp hp₂ zero_lt_one zero_lt_one (by positivity)).1
  have hB : samplingTail (lawPeanoKernel p 1 0 1 .b) 0 1 = pureBStack p 1 := by
    unfold pureBStack
    simp only [Real.one_rpow, one_mul]
    unfold samplingTail
    apply congrArg ((1 : ℝ) * ·)
    apply tsum_congr
    intro j
    exact (lawPeanoKernel_zero hp hp₂ zero_lt_one zero_lt_one (by positivity)).2
  rw [hA, hB, lawMoment_zero_slope (zero_lt_one.trans_le hp) zero_lt_one] at h
  simpa only [Real.one_rpow, mul_one, one_mul] using h

private theorem normalizedAtContact {p u : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hR : adjacentRatio u p = 1) :
    normalizedAdjacentCap u p = -(pureZ p - 1 - pureBStack p u) := by
  have hp₂ := hP.trans (by norm_num : (9 / 5 : ℝ) ≤ 2)
  have h := pureStacks_one_sum hp hp₂
  rw [pureBStack_one_eq hp hp₂] at h
  unfold normalizedAdjacentCap
  rw [hR, mul_one]
  linarith only [h]

private theorem contact_ratio (u p : ℝ) :
    adjacentRatio u p = 1 + (3 / 20) * (9 / 5 - adjacentCapSpan u - p) := by
  unfold adjacentRatio adjacentCapSpan
  ring

private theorem capSpan_pos {u : ℝ} (hu : 0 < u) (hu' : u ≤ 7 / 8) :
    0 < adjacentCapSpan u := by
  have h := pow_le_pow_left₀ hu.le hu' 2
  unfold adjacentCapSpan
  nlinarith only [h]

private theorem chord_negative {f : ℝ → ℝ} {l p : ℝ} (hl : l ≤ p) (hp : p < 9 / 5)
    (hConv : ConvexOn ℝ (Icc l (9 / 5)) (fun x => f x + (51 / 200) * x ^ 2))
    (hL : f l < -(13 / 50) * (9 / 5 - l) ^ 2) (hP : f (9 / 5) < 0) :
    f p < 0 := by
  let P : ℝ := 9 / 5
  let d := P - l
  let a := (P - p) / d
  let b := (p - l) / d
  have hd : 0 < d := sub_pos.mpr (hl.trans_lt hp)
  have ha : 0 < a := div_pos (sub_pos.mpr hp) hd
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hl) hd.le
  have hD : P - l ≠ 0 := hd.ne'
  have hab : a + b = 1 := by
    dsimp only [a, b, d]
    field_simp [hD]
    ring
  have hpb : a * l + b * P = p := by
    dsimp only [a, b, d]
    field_simp [hD]
    ring
  have h := hConv.2 (show l ∈ Icc l P from ⟨le_rfl, hl.trans hp.le⟩)
    (show P ∈ Icc l P from ⟨hl.trans hp.le, le_rfl⟩) ha.le hb hab
  simp only [smul_eq_mul, hpb] at h
  have hSq : a * l ^ 2 + b * P ^ 2 - p ^ 2 = a * b * d ^ 2 := by
    rw [← hpb]
    dsimp only [d]
    linear_combination -(a * l ^ 2 + b * P ^ 2) * hab
  have hb₁ : b ≤ 1 := by linarith only [ha.le, hab]
  have hCorr : (51 / 200) * a * b * d ^ 2 ≤ (51 / 200) * a * d ^ 2 := by
    have h' := mul_le_mul_of_nonneg_right hb₁ (show 0 ≤ (51 / 200) * a * d ^ 2 by positivity)
    nlinarith only [h']
  have hP' : b * f P ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb hP.le
  have hPos : 0 < a * d ^ 2 := mul_pos ha (sq_pos_of_pos hd)
  change f l < -(13 / 50) * d ^ 2 at hL
  have hL'' := mul_lt_mul_of_pos_left hL ha
  change f p + (51 / 200) * p ^ 2 ≤
    a * (f l + (51 / 200) * l ^ 2) + b * (f P + (51 / 200) * P ^ 2) at h
  have hJ : f p ≤ a * f l + b * f P +
      (51 / 200) * (a * l ^ 2 + b * P ^ 2 - p ^ 2) := by
    nlinarith only [h]
  rw [hSq] at hJ
  have hT : a * f l + b * f P + (51 / 200) * (a * b * d ^ 2) <
      -(13 / 50) * (a * d ^ 2) + (51 / 200) * (a * d ^ 2) := by
    have hE : a * (-(13 / 50) * d ^ 2) = -(13 / 50) * (a * d ^ 2) := by ring
    rw [hE] at hL''
    have hV : (51 / 200) * (a * b * d ^ 2) ≤ (51 / 200) * (a * d ^ 2) := by
      simpa only [mul_assoc] using hCorr
    exact add_lt_add_of_lt_of_le ((add_le_of_nonpos_right hP').trans_lt hL'') hV
  exact hJ.trans_lt (hT.trans_le (by linarith only [hPos]))

theorem pureAdjacentCap_neg {p L u : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hL : 0 < L) (hu : 0 < u) (hu' : u ≤ 7 / 8) :
    adjacentDiagonal p L 0 u (adjacentCap p u) < 0 := by
  have hp₂ := hP.trans (by norm_num : (9 / 5 : ℝ) ≤ 2)
  have hu₁ := hu'.trans_lt (by norm_num : (7 / 8 : ℝ) < 1)
  by_cases h : p = 9 / 5
  · rw [h]
    exact pureAdjacentCap_upper_neg hL hu hu'
  have hpP := lt_of_le_of_ne hP h
  by_cases hR : 1 ≤ adjacentRatio u p
  · have hM : u ≤ adjacentCap p u := by
      rw [adjacentCap_eq_ratio]
      exact le_mul_of_one_le_right hu.le hR
    have hθ : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
    have hU := adjacentSourceLaw_at_u_neg hp hp₂ hL hθ hu hu₁ hu le_rfl
    exact ((adjacentDiagonal_strictAnti hp hp₂ hL hθ hu).antitoneOn hu (adjacentCap_pos hP hu) hM).trans_lt hU
  have hE := normalizedAdjacentCap_eq hp hP hL hu
  have hEnd : normalizedAdjacentCap u (9 / 5) < 0 := by
    rw [← normalizedAdjacentCap_eq (by norm_num) le_rfl hL hu]
    exact mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos hu _) (pureAdjacentCap_upper_neg hL hu hu')
  have hMid : normalizedAdjacentCap u p < 0 := by
    by_cases hOne : adjacentRatio u 1 ≤ 1
    · have hCap : adjacentCap 1 u ≤ u := by
        rw [adjacentCap_eq_ratio]
        exact mul_le_of_le_one_right hu.le hOne
      have h0 := pureAdjacentCap_one_neg hL hu hu' hCap
      have hN := normalizedAdjacentCap_eq (p := 1) le_rfl (by norm_num) hL hu
      simp only [sub_self, Real.rpow_zero, one_mul] at hN
      have hLeft : normalizedAdjacentCap u 1 < -(13 / 50) * (9 / 5 - 1) ^ 2 := by
        rw [← hN]
        exact h0.trans (by norm_num)
      exact chord_negative hp hpP (normalizedAdjacentCap_semiconvex hu le_rfl hOne) hLeft hEnd
    · let l := 9 / 5 - adjacentCapSpan u
      have hl : 1 ≤ l := by
        rw [contact_ratio] at hOne
        change ¬ 1 + (3 / 20) * (l - 1) ≤ 1 at hOne
        linarith only [lt_of_not_ge hOne]
      have hlP : l ≤ 9 / 5 := sub_le_self _ (capSpan_pos hu hu').le
      have hτ : adjacentRatio u l = 1 := by rw [contact_ratio]; dsimp only [l]; ring
      have hlp : l ≤ p := by
        rw [contact_ratio] at hR
        change ¬ 1 ≤ 1 + (3 / 20) * (l - p) at hR
        linarith only [lt_of_not_ge hR]
      have hu0 : 39 / 50 ≤ u := by
        by_contra! hU
        have hS := pow_le_pow_left₀ hu.le hU.le 2
        unfold adjacentRatio at hOne
        nlinarith only [lt_of_not_ge hOne, hS]
      have hD := adjacentContact_deficit hl (hlP.trans (by norm_num)) hu0 hu'
      have hL' : normalizedAdjacentCap u l < -(13 / 50) * (9 / 5 - l) ^ 2 := by
        rw [normalizedAtContact hl hlP hτ]
        dsimp only [l]
        rw [sub_sub_cancel]
        linarith only [hD]
      exact chord_negative hlp hpP (normalizedAdjacentCap_semiconvex hu hl hτ.le) hL' hEnd
  rw [← hE] at hMid
  apply lt_of_mul_lt_mul_left _ (Real.rpow_nonneg hu.le (p - 1))
  simpa only [mul_zero] using hMid

end ACS12.GammaMeasure

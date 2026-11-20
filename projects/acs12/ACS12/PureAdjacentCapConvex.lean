import ACS12.PureAdjacentSemiConvex
import ACS12.PureAdjacentMixed
import ACS12.AdjacentCapMass

/-! The decreasing affine cap combines separate curvature and finite mixed differences. -/

namespace ACS12.GammaMeasure

open Set

noncomputable def adjacentRatio (u p : ℝ) : ℝ :=
  5 / 7 + (2304 / 8575) * u ^ 2 + (3 / 20) * (9 / 5 - p)

theorem adjacentCap_eq_ratio (p u : ℝ) :
    adjacentCap p u = u * adjacentRatio u p := rfl

theorem adjacentRatio_pos {u p : ℝ} (hP : p ≤ 9 / 5) : 0 < adjacentRatio u p := by
  unfold adjacentRatio
  have h := sub_nonneg.mpr hP
  positivity

theorem adjacentRatio_antitone (u : ℝ) : Antitone (adjacentRatio u) := by
  intro p q hpq
  unfold adjacentRatio
  linarith only [hpq]

private theorem adjacentRatio_affine (u p q a b : ℝ) (hab : a + b = 1) :
    adjacentRatio u (a * p + b * q) = a * adjacentRatio u p + b * adjacentRatio u q := by
  unfold adjacentRatio
  linear_combination -(5 / 7 + (2304 / 8575) * u ^ 2 + (3 / 20) * (9 / 5)) * hab

noncomputable def normalizedAdjacentCap (u p : ℝ) : ℝ :=
  pureAStack p (adjacentRatio u p) + pureBStack p u + 1 - (p + 1) * adjacentRatio u p

theorem normalizedAdjacentCap_eq {p L u : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hL : 0 < L) (hu : 0 < u) :
    u ^ (p - 1) * adjacentDiagonal p L 0 u (adjacentCap p u) = normalizedAdjacentCap u p := by
  have h := pureAdjacent_normalized hp (hP.trans (by norm_num)) hL hu (adjacentCap_pos hP hu)
  have hM : adjacentCap p u / u = adjacentRatio u p := by
    rw [adjacentCap_eq_ratio, mul_div_cancel_left₀ _ hu.ne']
  rw [hM] at h
  exact h

private theorem capA_jensen_ordered {u l p q a b : ℝ} (hl : 1 ≤ l)
    (hp : p ∈ Icc l (9 / 5)) (hq : q ∈ Icc l (9 / 5)) (hpq : p ≤ q)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hτ : adjacentRatio u l ≤ 1) :
    pureAStack (a * p + b * q) (adjacentRatio u (a * p + b * q)) +
        (17 / 100) * (a * p + b * q) ^ 2 ≤
      a * (pureAStack p (adjacentRatio u p) + (17 / 100) * p ^ 2) +
        b * (pureAStack q (adjacentRatio u q) + (17 / 100) * q ^ 2) := by
  let r := a * p + b * q
  let P := adjacentRatio u p
  let Q := adjacentRatio u q
  let R := adjacentRatio u r
  have hr : r ∈ Icc l (9 / 5) := convex_Icc _ _ hp hq ha hb hab
  have hP : 0 < P := adjacentRatio_pos hp.2
  have hQ : 0 < Q := adjacentRatio_pos hq.2
  have hR : 0 < R := adjacentRatio_pos hr.2
  have hP₁ : P ≤ 1 := ((adjacentRatio_antitone u) hp.1).trans hτ
  have hR₁ : R ≤ 1 := ((adjacentRatio_antitone u) hr.1).trans hτ
  have hp₁ := hl.trans hp.1
  have hq₁ := hl.trans hq.1
  have hp₂ := hp.2.trans (by norm_num : (9 / 5 : ℝ) ≤ 2)
  have hq₂ := hq.2.trans (by norm_num : (9 / 5 : ℝ) ≤ 2)
  have hPQ : Q ≤ P := (adjacentRatio_antitone u) hpq
  have hRP : R = a * P + b * Q := adjacentRatio_affine u p q a b hab
  have hF := (pureAStack_exponent_semiconvex hR hR₁).2
    (show p ∈ Icc 1 (9 / 5) from ⟨hp₁, hp.2⟩)
    (show q ∈ Icc 1 (9 / 5) from ⟨hq₁, hq.2⟩) ha hb hab
  simp only [smul_eq_mul] at hF
  have hP' := (pureAStack_convex hp₁ hp₂).2 hP hQ ha hb hab
  have hQ' := (pureAStack_convex hq₁ hq₂).2 hP hQ ha hb hab
  simp only [smul_eq_mul, ← hRP] at hP' hQ'
  have hCross := pureAStack_submodular hp₁ hpq hq₂ hQ hPQ hP₁
  have hMix : a * (a * pureAStack p P + b * pureAStack p Q) +
      b * (a * pureAStack q P + b * pureAStack q Q) ≤
      a * pureAStack p P + b * pureAStack q Q := by
    have hN := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ha hb)
      (sub_nonpos.mpr hCross)
    calc
      _ = (a + b) * (a * pureAStack p P + b * pureAStack q Q) +
          a * b * ((pureAStack p Q + pureAStack q P) - (pureAStack p P + pureAStack q Q)) := by ring
      _ ≤ _ := by rw [hab, one_mul]; exact add_le_of_nonpos_right hN
  change pureAStack r R + (17 / 100) * r ^ 2 ≤ _
  change pureAStack r R + (17 / 100) * r ^ 2 ≤
    a * (pureAStack p R + (17 / 100) * p ^ 2) +
    b * (pureAStack q R + (17 / 100) * q ^ 2) at hF
  have hFp := mul_le_mul_of_nonneg_left hP' ha
  have hFq := mul_le_mul_of_nonneg_left hQ' hb
  change _ ≤ a * (pureAStack p P + (17 / 100) * p ^ 2) +
    b * (pureAStack q Q + (17 / 100) * q ^ 2)
  nlinarith only [hF, hFp, hFq, hMix]

theorem normalizedAdjacentCap_semiconvex {u l : ℝ} (hu : 0 < u) (hl : 1 ≤ l)
    (hτ : adjacentRatio u l ≤ 1) :
    ConvexOn ℝ (Icc l (9 / 5)) (fun p => normalizedAdjacentCap u p + (51 / 200) * p ^ 2) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro p hp q hq a b ha hb hab
  simp only [smul_eq_mul]
  have hA : pureAStack (a * p + b * q) (adjacentRatio u (a * p + b * q)) +
        (17 / 100) * (a * p + b * q) ^ 2 ≤
      a * (pureAStack p (adjacentRatio u p) + (17 / 100) * p ^ 2) +
        b * (pureAStack q (adjacentRatio u q) + (17 / 100) * q ^ 2) := by
    rcases le_total p q with h | h
    · exact capA_jensen_ordered hl hp hq h ha hb hab hτ
    · simpa only [add_comm] using capA_jensen_ordered hl hq hp h hb ha (by linarith only [hab]) hτ
  have hB := (pureBStack_exponent_semiconvex hu).2
    (show p ∈ Icc 1 (9 / 5) from ⟨hl.trans hp.1, hp.2⟩)
    (show q ∈ Icc 1 (9 / 5) from ⟨hl.trans hq.1, hq.2⟩) ha hb hab
  simp only [smul_eq_mul] at hB
  let C := 5 / 7 + (2304 / 8575) * u ^ 2 + (3 / 20) * (9 / 5)
  let f (r : ℝ) := (3 / 20 - C) * r + 1 - C
  have hL (r : ℝ) : 1 - (r + 1) * adjacentRatio u r + (51 / 200) * r ^ 2 =
      (17 / 100) * r ^ 2 + (47 / 200) * r ^ 2 + f r := by
    unfold adjacentRatio
    dsimp only [C, f]
    ring
  have hAff : f (a * p + b * q) = a * f p + b * f q := by
    dsimp only [f]
    linear_combination -(1 - C) * hab
  unfold normalizedAdjacentCap
  have hE (r : ℝ) : (pureAStack r (adjacentRatio u r) + pureBStack r u + 1 -
      (r + 1) * adjacentRatio u r + (51 / 200) * r ^ 2) =
      (pureAStack r (adjacentRatio u r) + (17 / 100) * r ^ 2) +
      (pureBStack r u + (47 / 200) * r ^ 2) + f r := by
    linear_combination hL r
  rw [hE, hE, hE, hAff]
  nlinarith only [hA, hB]

end ACS12.GammaMeasure

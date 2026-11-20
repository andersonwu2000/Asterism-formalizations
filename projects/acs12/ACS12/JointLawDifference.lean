import ACS12.AdjacentReturnDensity

/-! Exact joint-source law differences at the original two source rows. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaDeficit (lineDensity signedDensity)

noncomputable def jointRetainedGap (m r s : ℝ) : ℝ :=
  Real.exp (-s * m) * adjacentBoseGap m r s

noncomputable def jointSourceResponse (u m r s : ℝ) : ℝ :=
  adjacentSourceResponse u m s + polyA (u * s) * jointRetainedGap m r s

noncomputable def fourthSourceResponse (u m r s : ℝ) : ℝ :=
  (m - r) - fourthDensity u m r m s

theorem jointRetainedGap_eq {m r s : ℝ} (hm : 0 < m) (hs : 0 < s) :
    jointRetainedGap m r s = scaledExpTail s m - Real.exp (-s * m) * (r + scaledExpTail s r) := by
  unfold jointRetainedGap adjacentBoseGap
  linear_combination scaledExpTail_bridge hs hm

theorem fourthSourceResponse_eq {u m r s : ℝ} (hu : 0 < u) (hm : 0 < m) (hs : 0 < s) :
    fourthSourceResponse u m r s =
      polyB (m * s) * (scaledExpTail s m - scaledExpTail s u +
        Real.exp (-s * u) * (scaledExpTail s u - scaledExpTail s 1)) +
      polyA (m * s) * adjacentBoseGap m r s := by
  unfold fourthSourceResponse fourthDensity fourthFirstStream adjacentBoseGap
  have hA : polyA (m * s) = 1 - (1 + m * s) * Real.exp (-s * m) := by
    unfold polyA
    rw [show -(m * s) = -s * m by ring]
  linear_combination -(polyB (m * s)) * scaledExpTail_bridge hs hu +
    - peanoBose_total hm hs - (m - r) * hA

theorem fourthSourceResponse_pos {u m r s : ℝ} (hm : 0 < m) (hmu : m ≤ u) (hu₁ : u < 1)
    (hr : 0 < r) (hrm : r ≤ m) (hs : 0 < s) :
    0 < fourthSourceResponse u m r s := by
  have hu := hm.trans_le hmu
  rw [fourthSourceResponse_eq hu hm hs]
  have hB := sub_nonneg.mpr ((scaledExpTail_strictAnti hs).antitoneOn hm hu hmu)
  have hC := sub_pos.mpr (scaledExpTail_strictAnti hs hu (mem_Ioi.mpr zero_lt_one) hu₁)
  exact add_pos_of_pos_of_nonneg
    (mul_pos (polyB_pos (mul_pos hm hs)) (add_pos_of_nonneg_of_pos hB (mul_pos (Real.exp_pos _) hC)))
    (mul_nonneg (polyA_pos (mul_pos hm hs)).le (adjacentBoseGap_bounds hs hr hrm).1)

theorem jointSourceResponse_pos {u m r s : ℝ} (hm : 0 < m) (hmu : m ≤ u) (hu₁ : u < 1)
    (hr : 0 < r) (hrm : r ≤ m) (hs : 0 < s) :
    0 < jointSourceResponse u m r s := by
  have hu := hm.trans_le hmu
  have hB := sub_pos.mpr (scaledExpTail_strictAnti hs hu (mem_Ioi.mpr zero_lt_one) hu₁)
  have hM := (adjacentBoseGap_bounds hs hm hmu).1
  have hR := (adjacentBoseGap_bounds hs hr hrm).1
  unfold jointSourceResponse adjacentSourceResponse outerSourceResponse jointRetainedGap
  rw [show u - adjacentEffectiveMass u m s = adjacentBoseGap u m s by unfold adjacentEffectiveMass; ring]
  exact add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg (mul_pos (polyB_pos (mul_pos hu hs)) hB)
      (mul_nonneg (polyA_pos (mul_pos hu hs)).le hM))
    (mul_nonneg (polyA_pos (mul_pos hu hs)).le (mul_nonneg (Real.exp_pos _).le hR))

theorem fourthSource_law_difference {p L θ₁ θ₂ u m r : ℝ} (hp : 1 ≤ p) (hp₂ : p < 2)
    (hL : 0 < L) (hθ₁ : θ₁ ∈ Icc (0 : ℝ) 1) (hθ₂ : θ₂ ∈ Icc (0 : ℝ) 1)
    (hu : 0 < u) (hm : 0 < m) (hr : 0 < r) :
    IntegrableOn (fun s => signedDensity p L s * fourthSourceResponse u m r s) (Ioi 0) ∧
      fourthSourceRow p L θ₂ u m r m - fourthSourceRow p L θ₁ u m r m =
        (θ₂ - θ₁) * ∫ s : ℝ in Ioi 0, signedDensity p L s * fourthSourceResponse u m r s := by
  let e := signedDensity p L
  let P := fourthDensity u m r m
  let R := fourthSourceResponse u m r
  have h0 : IntegrableOn (fun s => lineDensity p s * P s) (Ioi 0) := by
    simpa only [lawDensity, sub_zero, one_mul, zero_mul, add_zero] using
      (fourthSourceRow_integral (m := m) hp hp₂.le hL ⟨le_rfl, zero_le_one⟩ hu hm hr).1
  have h1 : IntegrableOn (fun s => imageDensity p L s * P s) (Ioi 0) := by
    simpa only [lawDensity, sub_self, zero_mul, one_mul, zero_add] using
      (fourthSourceRow_integral (m := m) hp hp₂.le hL ⟨zero_le_one, le_rfl⟩ hu hm hr).1
  obtain ⟨he, heE⟩ := signedDensity_total hp hp₂ hL
  obtain ⟨hI, hE⟩ := affineLaw_integral_difference (θ₁ := θ₁) (θ₂ := θ₂) h0 h1
  have hEq (s : ℝ) : e s * R s = (m - r) * e s - e s * P s := by dsimp only [R, P, fourthSourceResponse]; ring
  constructor
  · exact ((he.const_mul (m - r)).sub hI).congr (Eventually.of_forall fun s => (hEq s).symm)
  · rw [(fourthSourceRow_integral hp hp₂.le hL hθ₂ hu hm hr).2,
      (fourthSourceRow_integral hp hp₂.le hL hθ₁ hu hm hr).2,
      setIntegral_congr_fun measurableSet_Ioi (fun s _ => hEq s), integral_sub (he.const_mul (m - r)) hI,
      integral_const_mul, heE]
    unfold lawSelf
    dsimp only [e, P] at hE
    nlinarith only [hE]

private theorem lawPeanoHeadA_difference {p L θ₁ θ₂ u m r : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ₁ : θ₁ ∈ Icc (0 : ℝ) 1) (hθ₂ : θ₂ ∈ Icc (0 : ℝ) 1)
    (hu : 0 < u) (hm : 0 < m) (hr : 0 < r) :
    let F (s : ℝ) := polyA (u * s) * Real.exp (-s * m) * (r + scaledExpTail s r)
    IntegrableOn (fun s => signedDensity p L s * F s) (Ioi 0) ∧
      samplingHead (lawPeanoKernel p L θ₂ u .a) m r - samplingHead (lawPeanoKernel p L θ₁ u .a) m r =
        -(θ₂ - θ₁) * ∫ s : ℝ in Ioi 0, signedDensity p L s * F s := by
  let F (s : ℝ) := polyA (u * s) * Real.exp (-s * m) * (r + scaledExpTail s r)
  have h (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
      IntegrableOn (fun s => lawDensity p L θ s * F s) (Ioi 0) ∧
        samplingHead (lawPeanoKernel p L θ u .a) m r = ∫ s : ℝ in Ioi 0, lawDensity p L θ s * F s := by
    obtain ⟨hI, hE⟩ := lawPeanoHead_sampling hp hp₂ hL hθ hu hm hr .a
    have hF (s : ℝ) : lawPeanoDensity p L θ u .a s * Real.exp (-s * m) * (r + scaledExpTail s r) =
        lawDensity p L θ s * F s := by simp only [F, lawPeanoDensity, densityPolynomial]; ring
    exact ⟨hI.congr (Eventually.of_forall hF), hE.trans (setIntegral_congr_fun measurableSet_Ioi (fun s _ => hF s))⟩
  have h0 : IntegrableOn (fun s => lineDensity p s * F s) (Ioi 0) := by
    simpa only [lawDensity, sub_zero, one_mul, zero_mul, add_zero] using (h 0 ⟨le_rfl, zero_le_one⟩).1
  have h1 : IntegrableOn (fun s => imageDensity p L s * F s) (Ioi 0) := by
    simpa only [lawDensity, sub_self, zero_mul, one_mul, zero_add] using (h 1 ⟨zero_le_one, le_rfl⟩).1
  rw [(h θ₂ hθ₂).2, (h θ₁ hθ₁).2]
  exact affineLaw_integral_difference h0 h1

theorem jointAdjacent_law_difference {p L θ₁ θ₂ u m r : ℝ} (hp : 1 ≤ p) (hp₂ : p < 2)
    (hL : 0 < L) (hθ₁ : θ₁ ∈ Icc (0 : ℝ) 1) (hθ₂ : θ₂ ∈ Icc (0 : ℝ) 1)
    (hu : 0 < u) (hm : 0 < m) (hr : 0 < r) :
    IntegrableOn (fun s => signedDensity p L s * jointSourceResponse u m r s) (Ioi 0) ∧
      adjacentSourceLaw p L θ₂ u m m r - adjacentSourceLaw p L θ₁ u m m r =
        (θ₂ - θ₁) * ∫ s : ℝ in Ioi 0, signedDensity p L s * jointSourceResponse u m r s := by
  let e := signedDensity p L
  let Q := adjacentSourceResponse u m
  let A (r s : ℝ) := polyA (u * s) * Real.exp (-s * m) * (r + scaledExpTail s r)
  obtain ⟨hI, hE⟩ := adjacentDiagonal_law_difference hp hp₂ hL hθ₁ hθ₂ hu hm
  obtain ⟨hmI, hmE⟩ := lawPeanoHeadA_difference hp hp₂.le hL hθ₁ hθ₂ hu hm hm
  obtain ⟨hrI, hrE⟩ := lawPeanoHeadA_difference hp hp₂.le hL hθ₁ hθ₂ hu hm hr
  have hEq (s : ℝ) : e s * jointSourceResponse u m r s = e s * Q s + e s * A m s - e s * A r s := by
    unfold jointSourceResponse jointRetainedGap adjacentBoseGap
    dsimp only [Q, A]
    ring
  have hDiag (θ : ℝ) : adjacentSourceLaw p L θ u m m r = adjacentDiagonal p L θ u m +
      samplingHead (lawPeanoKernel p L θ u .a) m r - samplingHead (lawPeanoKernel p L θ u .a) m m := by
    unfold adjacentDiagonal adjacentSourceLaw
    ring
  constructor
  · exact ((hI.add hmI).sub hrI).congr (Eventually.of_forall fun s => (hEq s).symm)
  · rw [hDiag θ₂, hDiag θ₁, setIntegral_congr_fun measurableSet_Ioi (fun s _ => hEq s)]
    let F (s : ℝ) := e s * Q s
    let G (s : ℝ) := e s * A m s
    let H (s : ℝ) := e s * A r s
    change _ = (θ₂ - θ₁) * ∫ s : ℝ in Ioi 0, ((F + G) s - H s)
    have hF : IntegrableOn F (Ioi 0) := hI
    have hG : IntegrableOn G (Ioi 0) := hmI
    have hH : IntegrableOn H (Ioi 0) := hrI
    rw [integral_sub (hF.add hG) hH]
    change _ = (θ₂ - θ₁) * ((∫ s : ℝ in Ioi 0, F s + G s) - ∫ s : ℝ in Ioi 0, H s)
    rw [integral_add hF hG]
    dsimp only [F, G, H, e, Q, A]
    nlinarith only [hE, hmE, hrE]

end ACS12.GammaMeasure

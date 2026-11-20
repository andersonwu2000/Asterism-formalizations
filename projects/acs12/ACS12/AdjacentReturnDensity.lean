import ACS12.AdjacentReturnRoot

/-! Exact finite law differences for the adjacent root, including the complete signed mesh. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaDeficit (lineDensity signedDensity)

noncomputable def adjacentBoseGap (u m s : ℝ) : ℝ :=
  u - m + scaledExpTail s u - scaledExpTail s m

noncomputable def adjacentEffectiveMass (u m s : ℝ) : ℝ :=
  u - adjacentBoseGap u m s

noncomputable def adjacentSourceResponse (u m s : ℝ) : ℝ :=
  outerSourceResponse u (adjacentEffectiveMass u m s) s

noncomputable def adjacentNativeResponse (u m s : ℝ) : ℝ :=
  outerNativeResponse u (adjacentEffectiveMass u m s) s

theorem adjacentBoseGap_bounds {u m s : ℝ} (hs : 0 < s) (hm : 0 < m) (hmu : m ≤ u) :
    0 ≤ adjacentBoseGap u m s ∧ adjacentBoseGap u m s ≤ u - m := by
  let f (x : ℝ) := x + scaledExpTail s x
  have hD (x : ℝ) (hx : 0 < x) : HasDerivAt f (1 - BoseShape.C (s * x)) x := by
    exact (hasDerivAt_id x).add (scaledExpTail_derivative hs hx)
  have hM : MonotoneOn f (Icc m u) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun x hx => (hD x (hm.trans_le hx.1)).continuousAt.continuousWithinAt
    · exact fun x hx => (hD x (hm.trans_le (interior_subset hx).1)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Icc m u := interior_subset hx
      have hx₀ := hm.trans_le hx'.1
      rw [(hD x hx₀).deriv]
      linarith only [boseC_lt_half (mul_pos hs hx₀)]
  have hF := hM (show m ∈ Icc m u from ⟨le_rfl, hmu⟩) (show u ∈ Icc m u from ⟨hmu, le_rfl⟩) hmu
  have hB := (scaledExpTail_strictAnti hs).antitoneOn hm (hm.trans_le hmu) hmu
  unfold adjacentBoseGap
  dsimp only [f] at hF
  exact ⟨by linarith only [hF], by linarith only [hB]⟩

theorem affineLaw_integral_difference {p L θ₁ θ₂ : ℝ} {F : ℝ → ℝ}
    (h0 : IntegrableOn (fun s => lineDensity p s * F s) (Ioi 0))
    (h1 : IntegrableOn (fun s => imageDensity p L s * F s) (Ioi 0)) :
    IntegrableOn (fun s => signedDensity p L s * F s) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, lawDensity p L θ₂ s * F s) -
        (∫ s : ℝ in Ioi 0, lawDensity p L θ₁ s * F s) =
      -(θ₂ - θ₁) * ∫ s : ℝ in Ioi 0, signedDensity p L s * F s := by
  have hEq (s : ℝ) : signedDensity p L s * F s =
      lineDensity p s * F s - imageDensity p L s * F s := by unfold signedDensity; ring
  constructor
  · exact (h0.sub h1).congr (Eventually.of_forall fun s => (hEq s).symm)
  · rw [lawIntegral_eq h0 h1, lawIntegral_eq h0 h1,
      setIntegral_congr_fun measurableSet_Ioi (fun s _ => hEq s), integral_sub h0 h1]
    ring

private theorem lawPeanoA_difference {p L θ₁ θ₂ u q : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ₁ : θ₁ ∈ Icc (0 : ℝ) 1) (hθ₂ : θ₂ ∈ Icc (0 : ℝ) 1)
    (hu : 0 < u) (hq : 0 < q) :
    let F (s : ℝ) := polyA (u * s) * scaledExpTail s q
    IntegrableOn (fun s => signedDensity p L s * F s) (Ioi 0) ∧
      samplingTail (lawPeanoKernel p L θ₂ u .a) 0 q - samplingTail (lawPeanoKernel p L θ₁ u .a) 0 q =
        -(θ₂ - θ₁) * ∫ s : ℝ in Ioi 0, signedDensity p L s * F s := by
  let F (s : ℝ) := polyA (u * s) * scaledExpTail s q
  have h (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
      IntegrableOn (fun s => lawDensity p L θ s * F s) (Ioi 0) ∧
        samplingTail (lawPeanoKernel p L θ u .a) 0 q = ∫ s : ℝ in Ioi 0, lawDensity p L θ s * F s := by
    obtain ⟨hI, hE⟩ := lawPeanoTail_sampling hp hp₂ hL hθ hu (t := 0) le_rfl hq .a
    simp only [mul_zero, Real.exp_zero, mul_one, lawPeanoDensity, densityPolynomial] at hI hE
    have hF (s : ℝ) : lawDensity p L θ s * polyA (u * s) * scaledExpTail s q =
        lawDensity p L θ s * F s := by dsimp only [F]; ring
    exact ⟨hI.congr (Eventually.of_forall hF), hE.trans (setIntegral_congr_fun measurableSet_Ioi (fun s _ => hF s))⟩
  have h0 : IntegrableOn (fun s => lineDensity p s * F s) (Ioi 0) := by
    simpa only [lawDensity, sub_zero, one_mul, zero_mul, add_zero] using (h 0 ⟨le_rfl, zero_le_one⟩).1
  have h1 : IntegrableOn (fun s => imageDensity p L s * F s) (Ioi 0) := by
    simpa only [lawDensity, sub_self, zero_mul, one_mul, zero_add] using (h 1 ⟨zero_le_one, le_rfl⟩).1
  rw [(h θ₂ hθ₂).2, (h θ₁ hθ₁).2]
  exact affineLaw_integral_difference h0 h1

theorem adjacentDiagonal_law_difference {p L θ₁ θ₂ u m : ℝ} (hp : 1 ≤ p) (hp₂ : p < 2)
    (hL : 0 < L) (hθ₁ : θ₁ ∈ Icc (0 : ℝ) 1) (hθ₂ : θ₂ ∈ Icc (0 : ℝ) 1)
    (hu : 0 < u) (hm : 0 < m) :
    IntegrableOn (fun s => signedDensity p L s * adjacentSourceResponse u m s) (Ioi 0) ∧
      adjacentDiagonal p L θ₂ u m - adjacentDiagonal p L θ₁ u m =
        (θ₂ - θ₁) * ∫ s : ℝ in Ioi 0, signedDensity p L s * adjacentSourceResponse u m s := by
  let e := signedDensity p L
  let Q := outerSourceResponse u m
  let A (q s : ℝ) := polyA (u * s) * scaledExpTail s q
  obtain ⟨hI, hE⟩ := outerSourceLaw_difference (m := m) hp hp₂ hL hθ₁ hθ₂ hu
  obtain ⟨hmI, hmE⟩ := lawPeanoA_difference hp hp₂.le hL hθ₁ hθ₂ hu hm
  obtain ⟨huI, huE⟩ := lawPeanoA_difference hp hp₂.le hL hθ₁ hθ₂ hu hu
  have hEq (s : ℝ) : e s * adjacentSourceResponse u m s = e s * Q s - e s * A m s + e s * A u s := by
    unfold adjacentSourceResponse adjacentEffectiveMass adjacentBoseGap
    dsimp only [Q, A, outerSourceResponse]
    ring
  have hDiag (θ : ℝ) : adjacentDiagonal p L θ u m = adjacentSourceLaw p L θ u u m u +
      samplingTail (lawPeanoKernel p L θ u .a) 0 m - samplingTail (lawPeanoKernel p L θ u .a) 0 u := by
    have hShift (q : ℝ) : samplingTail (lawPeanoKernel p L θ u .a) 0 q =
        samplingHead (lawPeanoKernel p L θ u .a) q q := by
      rw [samplingTail_eq_shift, zero_add]
    unfold adjacentDiagonal adjacentSourceLaw
    rw [hShift m, hShift u]
    ring
  constructor
  · exact ((hI.sub hmI).add huI).congr (Eventually.of_forall fun s => (hEq s).symm)
  · rw [hDiag θ₂, hDiag θ₁, setIntegral_congr_fun measurableSet_Ioi (fun s _ => hEq s)]
    let F (s : ℝ) := e s * Q s
    let G (s : ℝ) := e s * A m s
    let H (s : ℝ) := e s * A u s
    change _ = (θ₂ - θ₁) * ∫ s : ℝ in Ioi 0, ((F - G) s + H s)
    have hF : IntegrableOn F (Ioi 0) := hI
    have hG : IntegrableOn G (Ioi 0) := hmI
    have hH : IntegrableOn H (Ioi 0) := huI
    rw [integral_add (hF.sub hG) hH]
    change _ = (θ₂ - θ₁) * ((∫ s : ℝ in Ioi 0, F s - G s) + ∫ s : ℝ in Ioi 0, H s)
    rw [integral_sub hF hG]
    dsimp only [F, G, H, e, Q, A]
    nlinarith only [hE, hmE, huE]

noncomputable def adjacentLawSignedValue (p L θ u m : ℝ) : ℝ :=
  middleLawBase p L θ u + m * lawRightTest p L θ u u + samplingTail (lawRightTest p L θ u) u m

private theorem lawRightTail_difference {p L θ₁ θ₂ u q : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ₁ : θ₁ ∈ Icc (0 : ℝ) 1) (hθ₂ : θ₂ ∈ Icc (0 : ℝ) 1)
    (hu : 0 < u) (hq : 0 < q) :
    let F (s : ℝ) := middleRightDensity u s * Real.exp (-s * u) * scaledExpTail s q
    IntegrableOn (fun s => signedDensity p L s * F s) (Ioi 0) ∧
      samplingTail (lawRightTest p L θ₂ u) u q - samplingTail (lawRightTest p L θ₁ u) u q =
        -(θ₂ - θ₁) * ∫ s : ℝ in Ioi 0, signedDensity p L s * F s := by
  let F (s : ℝ) := middleRightDensity u s * Real.exp (-s * u) * scaledExpTail s q
  have h (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
      IntegrableOn (fun s => lawDensity p L θ s * F s) (Ioi 0) ∧
        samplingTail (lawRightTest p L θ u) u q = ∫ s : ℝ in Ioi 0, lawDensity p L θ s * F s := by
    obtain ⟨hI, hE⟩ := lawRightTail_sampling (u := u) hp hp₂ hL hθ hu.le hq
    have hF (s : ℝ) : lawRightDensity p L θ u s * Real.exp (-s * u) * scaledExpTail s q =
        lawDensity p L θ s * F s := by dsimp only [F, lawRightDensity]; ring
    exact ⟨hI.congr (Eventually.of_forall hF), hE.trans (setIntegral_congr_fun measurableSet_Ioi (fun s _ => hF s))⟩
  have h0 : IntegrableOn (fun s => lineDensity p s * F s) (Ioi 0) := by
    simpa only [lawDensity, sub_zero, one_mul, zero_mul, add_zero] using (h 0 ⟨le_rfl, zero_le_one⟩).1
  have h1 : IntegrableOn (fun s => imageDensity p L s * F s) (Ioi 0) := by
    simpa only [lawDensity, sub_self, zero_mul, one_mul, zero_add] using (h 1 ⟨zero_le_one, le_rfl⟩).1
  rw [(h θ₂ hθ₂).2, (h θ₁ hθ₁).2]
  exact affineLaw_integral_difference h0 h1

theorem adjacentSignedValue_law_difference {p L θ₁ θ₂ u m : ℝ} (hp : 1 ≤ p) (hp₂ : p < 2)
    (hL : 0 < L) (hθ₁ : θ₁ ∈ Icc (0 : ℝ) 1) (hθ₂ : θ₂ ∈ Icc (0 : ℝ) 1)
    (hu : 0 < u) (hm : 0 < m) :
    IntegrableOn (fun s => signedDensity p L s * adjacentNativeResponse u m s) (Ioi 0) ∧
      adjacentLawSignedValue p L θ₂ u m - adjacentLawSignedValue p L θ₁ u m =
        -(θ₂ - θ₁) * ∫ s : ℝ in Ioi 0, signedDensity p L s * adjacentNativeResponse u m s := by
  let e := signedDensity p L
  let R := outerNativeResponse u m
  let A (q s : ℝ) := middleRightDensity u s * Real.exp (-s * u) * scaledExpTail s q
  obtain ⟨hI, hE⟩ := outerLawSignedValue_difference (m := m) hp hp₂ hL hθ₁ hθ₂ hu
  obtain ⟨hmI, hmE⟩ := lawRightTail_difference hp hp₂.le hL hθ₁ hθ₂ hu hm
  obtain ⟨huI, huE⟩ := lawRightTail_difference hp hp₂.le hL hθ₁ hθ₂ hu hu
  have hEq (s : ℝ) : e s * adjacentNativeResponse u m s = e s * R s + e s * A m s - e s * A u s := by
    unfold adjacentNativeResponse adjacentEffectiveMass adjacentBoseGap
    dsimp only [R, A, outerNativeResponse]
    ring
  have hDiag (θ : ℝ) : adjacentLawSignedValue p L θ u m = outerLawSignedValue p L θ u m +
      samplingTail (lawRightTest p L θ u) u m - samplingTail (lawRightTest p L θ u) u u := by
    unfold adjacentLawSignedValue outerLawSignedValue
    ring
  constructor
  · exact ((hI.add hmI).sub huI).congr (Eventually.of_forall fun s => (hEq s).symm)
  · rw [hDiag θ₂, hDiag θ₁, setIntegral_congr_fun measurableSet_Ioi (fun s _ => hEq s)]
    let F (s : ℝ) := e s * R s
    let G (s : ℝ) := e s * A m s
    let H (s : ℝ) := e s * A u s
    change _ = -(θ₂ - θ₁) * ∫ s : ℝ in Ioi 0, ((F + G) s - H s)
    have hF : IntegrableOn F (Ioi 0) := hI
    have hG : IntegrableOn G (Ioi 0) := hmI
    have hH : IntegrableOn H (Ioi 0) := huI
    rw [integral_sub (hF.add hG) hH]
    change _ = -(θ₂ - θ₁) * ((∫ s : ℝ in Ioi 0, F s + G s) - ∫ s : ℝ in Ioi 0, H s)
    rw [integral_add hF hG]
    dsimp only [F, G, H, e, R, A]
    nlinarith only [hE, hmE, huE]

end ACS12.GammaMeasure

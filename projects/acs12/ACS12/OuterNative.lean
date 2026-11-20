import ACS12.LawRightCoefficient

/-! The exact signed outer value and its once-self finite law return. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaDeficit (lineDensity signedDensity)

noncomputable def lawUnitSlope (p L θ : ℝ) : ℝ :=
  samplingTail (lawMoment p L θ 1) 0 1

noncomputable def middleLawBase (p L θ u : ℝ) : ℝ :=
  u * (lawMoment p L θ 0 1 + middleA u * lawMoment p L θ 1 1 - lawUnitSlope p L θ) -
    (1 - u) * lawSelf p L θ

noncomputable def outerLawSignedValue (p L θ u m : ℝ) : ℝ :=
  middleLawBase p L θ u + m * lawRightTest p L θ u u +
    samplingTail (lawRightTest p L θ u) u u

noncomputable def outerNativeDensity (u m s : ℝ) : ℝ :=
  u * ((1 + middleA u * s) * Real.exp (-s) - s * scaledExpTail s 1) +
    m * middleRightDensity u s * Real.exp (-s * u) +
    middleRightDensity u s * Real.exp (-s * u) * scaledExpTail s u

theorem lawUnitSlope_integral {p L θ : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) :
    IntegrableOn (fun s => lawDensity p L θ s * s * scaledExpTail s 1) (Ioi 0) ∧
      lawUnitSlope p L θ = ∫ s : ℝ in Ioi 0, lawDensity p L θ s * s * scaledExpTail s 1 := by
  let g (s : ℝ) := lawDensity p L θ s * s
  obtain ⟨B, _, hB⟩ := lawDensity_linear_envelope hp hp₂ hL hθ
  have hM : Measurable g := (lawDensity_measurable (zero_lt_one.trans_le hp) hL).mul measurable_id
  have hG (s : ℝ) (hs : 0 < s) : |g s| ≤ B * (s + s ^ 2) := by
    change |lawDensity p L θ s * s| ≤ _
    rw [abs_mul, abs_of_pos hs]
    exact (mul_le_mul_of_nonneg_right (hB s hs) hs.le).trans_eq (by ring)
  have h := signedTail_sampling_of_majorant (t := 0) hM zero_lt_one
    (signedTail_majorant_linearQuadratic hM hG le_rfl zero_lt_one)
  have hEq : lawMoment p L θ 1 = signedLaplace g := by
    funext t
    simp only [lawMoment, signedLaplace, g, pow_one]
  rw [lawUnitSlope, hEq]
  simpa only [g, mul_zero, Real.exp_zero, mul_one] using h

theorem outerLawSignedValue_integral {p L θ u m : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hu : 0 < u) :
    IntegrableOn (fun s => lawDensity p L θ s * outerNativeDensity u m s) (Ioi 0) ∧
      outerLawSignedValue p L θ u m =
        (∫ s : ℝ in Ioi 0, lawDensity p L θ s * outerNativeDensity u m s) -
          (1 - u) * lawSelf p L θ := by
  let w := lawDensity p L θ
  let a := middleA u
  let F₀ (s : ℝ) := w s * Real.exp (-s)
  let F₁ (s : ℝ) := w s * s * Real.exp (-s)
  let f (s : ℝ) := F₀ s + a * F₁ s
  let g (s : ℝ) := w s * s * scaledExpTail s 1
  let h (s : ℝ) := lawRightDensity p L θ u s * Real.exp (-s * u)
  let k (s : ℝ) := h s * scaledExpTail s u
  let μ := volume.restrict (Ioi (0 : ℝ))
  have h0 : Integrable F₀ μ := by
    simpa only [pow_zero, mul_one] using (lawMoment_integrable hp hp₂ hL hθ zero_lt_one 0)
  have h1 : Integrable F₁ μ := by
    simpa only [pow_one, mul_one] using (lawMoment_integrable hp hp₂ hL hθ zero_lt_one 1)
  have hf : Integrable f μ := h0.add (h1.const_mul a)
  obtain ⟨hg, hgE⟩ := lawUnitSlope_integral hp hp₂ hL hθ
  have hg' : Integrable g μ := hg
  have hh : Integrable h μ := lawRightDensity_integrable hp hp₂ hL hθ hu
  obtain ⟨hk, hkE⟩ := lawRightTail_sampling hp hp₂ hL hθ hu.le hu (u := u)
  have hk' : Integrable k μ := hk
  have hI : Integrable (fun s => u * f s + m * h s - u * g s - (-1) * k s) μ :=
    ((((hf.const_mul u).add (hh.const_mul m)).sub (hg'.const_mul u)).sub (hk'.const_mul (-1)))
  have hEq (s : ℝ) : w s * outerNativeDensity u m s = u * f s + m * h s - u * g s - (-1) * k s := by
    simp only [f, g, h, k, F₀, F₁, lawRightDensity, w, a, outerNativeDensity]
    ring
  constructor
  · exact hI.congr (Eventually.of_forall fun s => (hEq s).symm)
  · rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => hEq s),
      integral_four_terms hf hh hg' hk', outerLawSignedValue, middleLawBase, hgE, hkE]
    have hF : (∫ s : ℝ in Ioi 0, f s) = lawMoment p L θ 0 1 + a * lawMoment p L θ 1 1 := by
      change (∫ s : ℝ, F₀ s + a * F₁ s ∂μ) = _
      rw [integral_add h0 (h1.const_mul a), integral_const_mul]
      simp only [F₀, F₁, μ, w, lawMoment, pow_zero, pow_one, mul_one]
    rw [hF]
    simp only [h, g, k, μ, w, a, lawRightTest, signedLaplace, neg_one_mul, sub_neg_eq_add]
    ring

theorem outerNativeResponse_eq {u m s : ℝ} (hu : 0 < u) (hs : 0 < s) :
    outerNativeResponse u m s = outerNativeDensity u m s + (1 - u) := by
  let a := middleA u
  let z := middleZ u
  let A := middleA0 u s
  let g := middleRightDensity u s
  have hY := scaledExpTail_bridge hs hu
  have hX := scaledExpTail_bridge hs zero_lt_one
  simp only [mul_one] at hX
  have hB : (A + a * s) * scaledExpTail s 1 = 1 - A := by
    dsimp only [A, a, middleA0]
    linear_combination -(1 + middleA u * s) * hX
  have hG : g = z * s - A := rfl
  have haz : a + z = u := by dsimp only [a, z, middleZ]; ring
  have hGS : u * s - g = a * s + A := by
    rw [hG]
    linear_combination -s * haz
  have hA : (1 + a * s) * Real.exp (-s) = 1 - A := by dsimp only [A, a, middleA0]; ring
  change (1 - u) * A - g * (Real.exp (-s * u) * (u - m) -
      (scaledExpTail s u - scaledExpTail s 1)) =
    u * ((1 + a * s) * Real.exp (-s) - s * scaledExpTail s 1) +
      m * g * Real.exp (-s * u) + g * Real.exp (-s * u) * scaledExpTail s u + (1 - u)
  rw [hA]
  linear_combination hB - g * hY + scaledExpTail s 1 * hGS

theorem outerLawSignedValue_difference {p L θ₁ θ₂ u m : ℝ} (hp : 1 ≤ p) (hp₂ : p < 2)
    (hL : 0 < L) (hθ₁ : θ₁ ∈ Icc (0 : ℝ) 1) (hθ₂ : θ₂ ∈ Icc (0 : ℝ) 1) (hu : 0 < u) :
    let e := signedDensity p L
    let f := outerNativeResponse u m
    IntegrableOn (fun s => e s * f s) (Ioi 0) ∧
      outerLawSignedValue p L θ₂ u m - outerLawSignedValue p L θ₁ u m =
        -(θ₂ - θ₁) * ∫ s : ℝ in Ioi 0, e s * f s := by
  let e := signedDensity p L
  let P := outerNativeDensity u m
  let R := outerNativeResponse u m
  have h0 : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  have hρ : IntegrableOn (fun s => lineDensity p s * P s) (Ioi 0) := by
    simpa only [lawDensity, sub_zero, one_mul, zero_mul, add_zero] using
      (outerLawSignedValue_integral (m := m) hp hp₂.le hL h0 hu).1
  have hw : IntegrableOn (fun s => imageDensity p L s * P s) (Ioi 0) := by
    simpa only [lawDensity, sub_self, zero_mul, one_mul, zero_add] using
      (outerLawSignedValue_integral (m := m) hp hp₂.le hL h1 hu).1
  obtain ⟨he, heE⟩ := signedDensity_total hp hp₂ hL
  have hPE (s : ℝ) : e s * P s = lineDensity p s * P s - imageDensity p L s * P s := by
    dsimp only [e, signedDensity]
    ring
  have hEInt : IntegrableOn (fun s => e s * P s) (Ioi 0) :=
    (hρ.sub hw).congr (Eventually.of_forall fun s => (hPE s).symm)
  have hRE (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) : e s * R s = e s * P s + (1 - u) * e s := by
    change e s * outerNativeResponse u m s = _
    rw [outerNativeResponse_eq hu hs]
    ring
  constructor
  · apply (hEInt.add (he.const_mul (1 - u))).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hRE s hs).symm
  · rw [(outerLawSignedValue_integral hp hp₂.le hL hθ₂ hu).2,
      (outerLawSignedValue_integral hp hp₂.le hL hθ₁ hu).2,
      lawIntegral_eq hρ hw, lawIntegral_eq hρ hw]
    change _ = -(θ₂ - θ₁) * ∫ s : ℝ in Ioi 0, e s * R s
    rw [setIntegral_congr_fun measurableSet_Ioi hRE, integral_add hEInt (he.const_mul (1 - u)),
      integral_const_mul, heE, setIntegral_congr_fun measurableSet_Ioi (fun s _ => hPE s), integral_sub hρ hw]
    unfold lawSelf
    ring

end ACS12.GammaMeasure


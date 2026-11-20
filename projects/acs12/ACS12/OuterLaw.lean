import ACS12.AdjacentLaw
import ACS12.OuterRoot

/-! The affine outer source along the actual-to-pure law path. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaDeficit (lineDensity signedDensity lineDensity_exp_integral gamma_exp_integral)

noncomputable def outerLawDenom (p L θ u : ℝ) : ℝ :=
  u * lawMoment p L θ 1 u + lawMoment p L θ 0 u + lawSelf p L θ

noncomputable def outerLawDeficit (p L θ u : ℝ) : ℝ :=
  samplingTail (lawPeanoKernel p L θ u .b) 0 u - samplingTail (lawPeanoKernel p L θ u .b) 0 1

noncomputable def outerLawMass (p L θ u : ℝ) : ℝ :=
  u - outerLawDeficit p L θ u / outerLawDenom p L θ u

theorem outerLawDenom_pos {p L θ u : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hu : 0 < u) :
    0 < outerLawDenom p L θ u := by
  unfold outerLawDenom
  exact add_pos_of_pos_of_nonneg (add_pos (mul_pos hu (lawMoment_pos hp hp₂ hL hθ hu 1))
    (lawMoment_pos hp hp₂ hL hθ hu 0)) (lawSelf_nonneg (zero_lt_one.trans_le hp) hL hθ)

@[simp] theorem outerLawMass_one (p L u : ℝ) :
    outerLawMass p L 1 u = outerMass p L u := by
  simp only [outerLawMass, outerLawDeficit, outerLawDenom, lawPeanoKernel_one,
    lawMoment_one_slope, lawMoment_one_radial, lawSelf, one_mul, outerMass]

theorem lawPeanoTail_total {p L θ u : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hu : 0 < u) :
    samplingTail (lawPeanoKernel p L θ u .a) 0 u + samplingTail (lawPeanoKernel p L θ u .b) 0 u =
      u * u * lawMoment p L θ 1 u := by
  obtain ⟨hA, hAE⟩ := lawPeanoTail_sampling hp hp₂ hL hθ hu (t := 0) le_rfl hu .a
  obtain ⟨hB, hBE⟩ := lawPeanoTail_sampling hp hp₂ hL hθ hu (t := 0) le_rfl hu .b
  simp only [mul_zero, Real.exp_zero, mul_one] at hA hAE hB hBE
  rw [hAE, hBE, ← integral_add hA hB, lawMoment, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  simp only [lawPeanoDensity, densityPolynomial, pow_one]
  linear_combination lawDensity p L θ s * peanoBose_total hu (mem_Ioi.mp hs)

theorem outerLawDeficit_integral {p L θ u : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hu : 0 < u) :
    let f (s : ℝ) := lawPeanoDensity p L θ u .b s * (scaledExpTail s u - scaledExpTail s 1)
    IntegrableOn f (Ioi 0) ∧ outerLawDeficit p L θ u = ∫ s : ℝ in Ioi 0, f s := by
  obtain ⟨hU, hUE⟩ := lawPeanoTail_sampling hp hp₂ hL hθ hu (t := 0) le_rfl hu .b
  obtain ⟨h1, h1E⟩ := lawPeanoTail_sampling hp hp₂ hL hθ hu (t := 0) le_rfl zero_lt_one .b
  simp only [mul_zero, Real.exp_zero, mul_one] at hU hUE h1 h1E
  constructor
  · refine (hU.sub h1).congr (Eventually.of_forall fun s => ?_)
    simp only [Pi.sub_apply, mul_sub]
  · rw [outerLawDeficit, hUE, h1E, ← integral_sub hU h1]
    exact integral_congr_ae (Eventually.of_forall fun s => by ring)

theorem outerLawDeficit_pos {p L θ u : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hu : 0 < u) (hu₁ : u < 1) :
    0 < outerLawDeficit p L θ u := by
  obtain ⟨hI, hE⟩ := outerLawDeficit_integral hp hp₂ hL hθ hu
  rw [hE]
  letI : NeZero (volume.restrict (Ioi (0 : ℝ))) := ⟨positiveHalfLine_ne_zero⟩
  have h := integral_strict_of_ae_lt (volume.restrict (Ioi (0 : ℝ))) (integrable_zero ℝ ℝ _) hI ?_
  · simpa only [integral_zero] using h
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_pos (lawPeanoDensity_pos (zero_lt_one.trans_le hp) hL hθ hu hs .b)
      (sub_pos.mpr (scaledExpTail_strictAnti hs hu (mem_Ioi.mpr zero_lt_one) hu₁))

theorem outerLawMass_mem {p L θ u : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hu : 0 < u) (hu₁ : u < 1) :
    outerLawMass p L θ u ∈ Ioo 0 u := by
  have hD := outerLawDenom_pos hp hp₂ hL hθ hu
  have hF := outerLawDeficit_pos hp hp₂ hL hθ hu hu₁
  have hA := lawPeanoTail_nonneg hp hp₂ hL hθ hu (t := 0) le_rfl hu .a
  have hB := lawPeanoTail_nonneg hp hp₂ hL hθ hu (t := 0) le_rfl zero_lt_one .b
  have hT := lawPeanoTail_total hp hp₂ hL hθ hu
  have hLt : outerLawDeficit p L θ u < u * outerLawDenom p L θ u := by
    have hK := mul_pos hu (lawMoment_pos hp hp₂ hL hθ hu 0)
    have hS := mul_nonneg hu.le (lawSelf_nonneg (zero_lt_one.trans_le hp) hL hθ)
    unfold outerLawDenom outerLawDeficit
    nlinarith only [hA, hB, hT, hK, hS]
  exact ⟨sub_pos.mpr ((div_lt_iff₀ hD).mpr hLt), sub_lt_self _ (div_pos hF hD)⟩

theorem outerSourceLaw_eq {p L θ u : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hu : 0 < u) (m : ℝ) :
    adjacentSourceLaw p L θ u u m u =
      (outerLawMass p L θ u - m) * outerLawDenom p L θ u := by
  have hD := outerLawDenom_pos hp hp₂ hL hθ hu
  have hT := lawPeanoTail_total hp hp₂ hL hθ hu
  have hA : samplingHead (lawPeanoKernel p L θ u .a) u u =
      samplingTail (lawPeanoKernel p L θ u .a) 0 u := by
    rw [samplingTail_eq_shift, zero_add]
  rw [outerLawMass, sub_mul, sub_mul, div_mul_cancel₀ _ hD.ne', adjacentSourceLaw, hA]
  unfold outerLawDenom outerLawDeficit
  nlinarith only [hT]

noncomputable def outerSourceDensity (u m s : ℝ) : ℝ :=
  polyB (u * s) * scaledExpTail s 1 + polyA (u * s) * scaledExpTail s u -
    u * m * s * Real.exp (-s * u) + (u - m) * Real.exp (-s * u)

theorem outerSourceLaw_integral {p L θ u m : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hu : 0 < u) :
    IntegrableOn (fun s => lawDensity p L θ s * outerSourceDensity u m s) (Ioi 0) ∧
      adjacentSourceLaw p L θ u u m u =
        (∫ s : ℝ in Ioi 0, lawDensity p L θ s * outerSourceDensity u m s) +
          (u - m) * lawSelf p L θ := by
  let w := lawDensity p L θ
  let f (s : ℝ) := lawPeanoDensity p L θ u .b s * scaledExpTail s 1
  let g (s : ℝ) := lawPeanoDensity p L θ u .a s * scaledExpTail s u
  let h (s : ℝ) := w s * s * Real.exp (-s * u)
  let k (s : ℝ) := w s * Real.exp (-s * u)
  let μ := volume.restrict (Ioi (0 : ℝ))
  obtain ⟨hf, hfE⟩ := lawPeanoTail_sampling hp hp₂ hL hθ hu (t := 0) le_rfl zero_lt_one .b
  obtain ⟨hg, hgE⟩ := lawPeanoTail_sampling hp hp₂ hL hθ hu (t := 0) le_rfl hu .a
  simp only [mul_zero, Real.exp_zero, mul_one] at hf hfE hg hgE
  have hf' : Integrable f μ := hf
  have hg' : Integrable g μ := hg
  have hh : Integrable h μ := by simpa only [pow_one] using lawMoment_integrable hp hp₂ hL hθ hu 1
  have hk : Integrable k μ := by simpa only [pow_zero, mul_one] using lawMoment_integrable hp hp₂ hL hθ hu 0
  have hI : Integrable (fun s => 1 * f s + 1 * g s - (u * m) * h s - (-(u - m)) * k s) μ :=
    ((((hf'.const_mul 1).add (hg'.const_mul 1)).sub (hh.const_mul (u * m))).sub (hk.const_mul (-(u - m))))
  have hP (s : ℝ) : w s * outerSourceDensity u m s =
      1 * f s + 1 * g s - (u * m) * h s - (-(u - m)) * k s := by
    simp only [f, g, h, k, w, outerSourceDensity, lawPeanoDensity, densityPolynomial]
    ring
  constructor
  · exact hI.congr (Eventually.of_forall fun s => (hP s).symm)
  · rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => hP s),
      integral_four_terms hf' hg' hh hk, adjacentSourceLaw]
    have hA : samplingHead (lawPeanoKernel p L θ u .a) u u =
        samplingTail (lawPeanoKernel p L θ u .a) 0 u := by rw [samplingTail_eq_shift, zero_add]
    rw [hA, hfE, hgE]
    simp only [f, g, h, k, w, μ, lawMoment, pow_one, pow_zero, mul_one, one_mul]
    ring

noncomputable def outerSourceResponse (u m s : ℝ) : ℝ :=
  polyB (u * s) * (scaledExpTail s u - scaledExpTail s 1) + polyA (u * s) * (u - m)

theorem outerSourceResponse_eq {u m s : ℝ} (hu : 0 < u) (hs : 0 < s) :
    outerSourceResponse u m s = (u - m) - outerSourceDensity u m s := by
  unfold outerSourceResponse outerSourceDensity
  have hT := peanoBose_total hu hs
  simp only [polyA, show -(u * s) = -s * u by ring] at *
  linear_combination hT

theorem outerSourceLaw_difference {p L θ₁ θ₂ u m : ℝ} (hp : 1 ≤ p) (hp₂ : p < 2)
    (hL : 0 < L) (hθ₁ : θ₁ ∈ Icc (0 : ℝ) 1) (hθ₂ : θ₂ ∈ Icc (0 : ℝ) 1)
    (hu : 0 < u) :
    let e := signedDensity p L
    let f := outerSourceResponse u m
    IntegrableOn (fun s => e s * f s) (Ioi 0) ∧
      adjacentSourceLaw p L θ₂ u u m u - adjacentSourceLaw p L θ₁ u u m u =
        (θ₂ - θ₁) * ∫ s : ℝ in Ioi 0, e s * f s := by
  let e := signedDensity p L
  let Q := outerSourceDensity u m
  let R := outerSourceResponse u m
  have h0 : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  have hρ : IntegrableOn (fun s => lineDensity p s * Q s) (Ioi 0) := by
    simpa only [lawDensity, sub_zero, one_mul, zero_mul, add_zero] using
      (outerSourceLaw_integral (m := m) hp hp₂.le hL h0 hu).1
  have hw : IntegrableOn (fun s => imageDensity p L s * Q s) (Ioi 0) := by
    simpa only [lawDensity, sub_self, zero_mul, one_mul, zero_add] using
      (outerSourceLaw_integral (m := m) hp hp₂.le hL h1 hu).1
  obtain ⟨he, heE⟩ := signedDensity_total hp hp₂ hL
  have hP (s : ℝ) : e s * Q s = lineDensity p s * Q s - imageDensity p L s * Q s := by
    dsimp only [e, signedDensity]
    ring
  have hEInt : IntegrableOn (fun s => e s * Q s) (Ioi 0) :=
    (hρ.sub hw).congr (Eventually.of_forall fun s => (hP s).symm)
  have hPE (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      e s * R s = (u - m) * e s - e s * Q s := by
    change e s * outerSourceResponse u m s = _
    rw [outerSourceResponse_eq hu hs]
    ring
  constructor
  · apply ((he.const_mul (u - m)).sub hEInt).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hPE s hs).symm
  · rw [(outerSourceLaw_integral hp hp₂.le hL hθ₂ hu).2,
      (outerSourceLaw_integral hp hp₂.le hL hθ₁ hu).2, lawIntegral_eq hρ hw, lawIntegral_eq hρ hw]
    change _ = (θ₂ - θ₁) * ∫ s : ℝ in Ioi 0, e s * R s
    rw [setIntegral_congr_fun measurableSet_Ioi hPE, integral_sub (he.const_mul (u - m)) hEInt,
      integral_const_mul, heE, setIntegral_congr_fun measurableSet_Ioi (fun s _ => hP s), integral_sub hρ hw]
    unfold lawSelf
    ring

theorem outerLawMass_strictMono {p L u : ℝ} (hp : 1 ≤ p) (hp₂ : p < 2)
    (hL : 0 < L) (hu : 0 < u) (hu₁ : u < 1) :
    StrictMonoOn (fun θ => outerLawMass p L θ u) (Icc 0 1) := by
  intro θ₁ hθ₁ θ₂ hθ₂ hθ
  let m := outerLawMass p L θ₁ u
  have hm := (outerLawMass_mem hp hp₂.le hL hθ₁ hu hu₁).2
  obtain ⟨hI, hE⟩ := outerSourceLaw_difference (m := m) hp hp₂ hL hθ₁ hθ₂ hu
  letI : NeZero (volume.restrict (Ioi (0 : ℝ))) := ⟨positiveHalfLine_ne_zero⟩
  have hP : 0 < ∫ s : ℝ in Ioi 0, signedDensity p L s * outerSourceResponse u m s := by
    have h := integral_strict_of_ae_lt (volume.restrict (Ioi (0 : ℝ))) (integrable_zero ℝ ℝ _) hI ?_
    · simpa only [integral_zero] using h
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs₀ : 0 < s := hs
      have hBs := scaledExpTail_strictAnti hs₀ hu (mem_Ioi.mpr zero_lt_one) hu₁
      unfold outerSourceResponse
      exact mul_pos (signedDensity_pos hp hp₂ hL hs₀) (add_pos
        (mul_pos (polyB_pos (mul_pos hu hs₀)) (sub_pos.mpr hBs))
        (mul_pos (polyA_pos (mul_pos hu hs₀)) (sub_pos.mpr hm)))
  have hRoot : adjacentSourceLaw p L θ₁ u u m u = 0 := by
    rw [outerSourceLaw_eq hp hp₂.le hL hθ₁ hu]
    change (m - m) * _ = _
    rw [sub_self, zero_mul]
  rw [hRoot, sub_zero, outerSourceLaw_eq hp hp₂.le hL hθ₂ hu] at hE
  have hPos : 0 < (outerLawMass p L θ₂ u - m) * outerLawDenom p L θ₂ u :=
    hE.symm ▸ mul_pos (sub_pos.mpr hθ) hP
  exact sub_pos.mp (pos_of_mul_pos_left hPos (outerLawDenom_pos hp hp₂.le hL hθ₂ hu).le)

end ACS12.GammaMeasure


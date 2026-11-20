import ACS12.JointConeBose
import ACS12.JointHighBracket
import ACS12.JointFourthSecant

/-! A source-deficit inequality bounds the fourth-root displacement. -/
namespace ACS12.GammaMeasure

open Set MeasureTheory Filter CenteredCircle.AllN
open GammaDeficit (lineDensity)

private theorem jointAdjacent_le {p L θ u m r : ℝ} (hp : 1 ≤ p) (hp₂ : p < 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hm : 0 < m) (hmu : m ≤ u) (hu₁ : u < 1)
    (hr : 0 < r) (hrm : r ≤ m) :
    adjacentSourceLaw p L θ u m m r ≤
      (u - m) * ((∫ s : ℝ in Ioi 0, lawDensity p L θ s * fourthD m m s) + lawSelf p L θ) -
        outerLawDeficit p L θ u := by
  let w := lawDensity p L θ
  let A := lawPeanoKernel p L θ u .a
  let F (s : ℝ) := w s * fourthD m m s
  let K (v r s : ℝ) := lawPeanoDensity p L θ u .a s * Real.exp (-s * v) * (r + scaledExpTail s r)
  have hu := hm.trans_le hmu
  have hp₀ := zero_lt_one.trans_le hp
  have hF : IntegrableOn F (Ioi 0) :=
    actual_integrable_of_pure hp hp₂ hL hθ (by unfold fourthD polyA BoseShape.C; fun_prop)
      (fun s hs => (fourthD_pos hm hm hs).le) (pureFourth_moment hp hp₂.le hm).1
  obtain ⟨hU,hUE⟩ := lawPeanoHead_sampling hp hp₂.le hL hθ hu hu hu .a
  obtain ⟨hM,hME⟩ := lawPeanoHead_sampling hp hp₂.le hL hθ hu hm hr .a
  let Q (s : ℝ) := w s * (1 + u * s) * Real.exp (-s * u)
  have hQ₀ : IntegrableOn (fun s => w s * Real.exp (-s * u)) (Ioi 0) := by
    simpa only [pow_zero,mul_one] using lawMoment_integrable hp hp₂.le hL hθ hu 0
  have hQ₁ : IntegrableOn (fun s => w s * s * Real.exp (-s * u)) (Ioi 0) := by
    simpa only [pow_one] using lawMoment_integrable hp hp₂.le hL hθ hu 1
  have hQe (s : ℝ) : Q s = w s * Real.exp (-s * u) + u * (w s * s * Real.exp (-s * u)) := by
    unfold Q
    ring
  have hQI : IntegrableOn Q (Ioi 0) := (hQ₀.add (hQ₁.const_mul u)).congr (Eventually.of_forall fun s => (hQe s).symm)
  have hQE : (∫ s : ℝ in Ioi 0, Q s) = outerLawDenom p L θ u - lawSelf p L θ := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => hQe s),integral_add hQ₀ (hQ₁.const_mul u),
      integral_const_mul]
    unfold outerLawDenom lawMoment
    simp only [pow_zero,mul_one,pow_one]
    ring
  have hHead (s : ℝ) (hs : 0 < s) :
      K m r s ≤ K u u s + (u - m) * (F s - Q s) := by
    have hw := (lawDensity_pos hp₀ hL hθ hs).le
    have hβ := (scaledExpTail_secant hs hm hmu).2
    have hR := (adjacentBoseGap_bounds hs hr hrm).1
    have hD := (BoseShape.C_lt_one (mul_pos hs hm)).le
    have hC := (BoseShape.C_pos (mul_pos hs hm)).le
    have hAo := polyA_monotone_nonneg (show m * s ∈ Ici 0 from (mul_pos hm hs).le)
      (show u * s ∈ Ici 0 from (mul_pos hu hs).le) (mul_le_mul_of_nonneg_right hmu hs.le)
    have hP (x : ℝ) : polyA (x * s) = 1 - (1 + x * s) * Real.exp (-s * x) := by
      unfold polyA
      rw [show -(x * s) = -s * x by ring]
    have hFQ : F s - Q s =
        w s * (polyA (u * s) - polyA (m * s) * (1 - BoseShape.C (s * m))) := by
      unfold F Q fourthD
      rw [show BoseShape.C (m * s) = BoseShape.C (s * m) by rw [mul_comm]]
      rw [hP u,hP m]
      ring
    have hSmall := mul_le_mul_of_nonneg_right hAo (sub_nonneg.mpr hD)
    have hC' : polyA (u * s) * BoseShape.C (s * m) ≤
        polyA (u * s) - polyA (m * s) * (1 - BoseShape.C (s * m)) := by
      linarith only [hSmall]
    have hBound : (u - m) * (w s * polyA (u * s) * BoseShape.C (s * m)) ≤
        (u - m) * (F s - Q s) := by
      rw [hFQ]
      have h := mul_le_mul_of_nonneg_left hC' hw
      nlinarith only [mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hmu)]
    have hAux : K m r s - K u u s = w s * polyA (u * s) *
        (scaledExpTail s m - scaledExpTail s u - jointRetainedGap m r s) := by
      unfold K lawPeanoDensity densityPolynomial
      rw [jointRetainedGap_eq hm hs]
      linear_combination -(w s * polyA (u * s)) * scaledExpTail_bridge hs hu
    have hRet : 0 ≤ jointRetainedGap m r s := mul_nonneg (Real.exp_pos _).le hR
    have hLow := mul_le_mul_of_nonneg_left (show scaledExpTail s m - scaledExpTail s u - jointRetainedGap m r s ≤
        (u - m) * BoseShape.C (s * m) by linarith only [hβ,hRet])
      (mul_nonneg hw (polyA_pos (mul_pos hu hs)).le)
    nlinarith only [hBound,hAux,hLow]
  have hK : (∫ s : ℝ in Ioi 0, K m r s) ≤
      (∫ s : ℝ in Ioi 0, K u u s) + (u - m) * ((∫ s : ℝ in Ioi 0, F s) - ∫ s : ℝ in Ioi 0, Q s) := by
    have hUI : IntegrableOn (K u u) (Ioi 0) := hU
    have hMI : IntegrableOn (K m r) (Ioi 0) := hM
    have h := setIntegral_mono_on hMI (hUI.add ((hF.sub hQI).const_mul (u - m))) measurableSet_Ioi
      (fun s hs => hHead s hs)
    change (∫ s : ℝ in Ioi 0, K m r s) ≤
      ∫ s : ℝ in Ioi 0, K u u s + (u - m) * (F s - Q s) at h
    rw [integral_add (g := fun s => (u - m) * (F s - Q s)) hUI
      ((hF.sub hQI).const_mul (u - m)),integral_const_mul] at h
    rw [integral_sub hF hQI] at h
    exact h
  have hEq : adjacentSourceLaw p L θ u m m r = adjacentSourceLaw p L θ u u m u +
      samplingHead A m r - samplingHead A u u := by unfold adjacentSourceLaw A; ring
  rw [hEq,outerSourceLaw_eq hp hp₂.le hL hθ hu,outerLawMass]
  have hD := outerLawDenom_pos hp hp₂.le hL hθ hu
  have hC : (u - outerLawDeficit p L θ u / outerLawDenom p L θ u - m) * outerLawDenom p L θ u =
      (u - m) * outerLawDenom p L θ u - outerLawDeficit p L θ u := by field_simp [hD.ne']; ring
  rw [hC]
  change samplingHead A m r = (∫ s : ℝ in Ioi 0, K m r s) at hME
  change samplingHead A u u = (∫ s : ℝ in Ioi 0, K u u s) at hUE
  rw [hME,hUE]
  rw [hQE] at hK
  dsimp only [F] at *
  linarith only [hK]

private theorem jointFourth_ge {p L θ u m r : ℝ} (hp : 1 ≤ p) (hp₂ : p < 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (huL : 7 / 8 ≤ u) (hu₁ : u < 1)
    (hm : 0 < m) (hmu : m ≤ u) (hr : 0 < r) (hrm : r ≤ m) :
    let D := (∫ s : ℝ in Ioi 0, lawDensity p L θ s * fourthD m m s) + lawSelf p L θ
    (m - r) * D - (u - m) * (m ^ (-p) * (1 + pureP p)) -
      (∫ s : ℝ in Ioi 0, lawDensity p L θ s * polyB (m * s) * Real.exp (-s * u) * jointBoseGap u s)
      ≤ fourthSourceRow p L θ u m r m := by
  let w := lawDensity p L θ
  let D (s : ℝ) := fourthD m m s
  let B (s : ℝ) := polyB (m * s) * BoseShape.C (m * s)
  let T (s : ℝ) := w s * polyB (m * s) * Real.exp (-s * u) * jointBoseGap u s
  let H (s : ℝ) := w s * fourthDensity u m r m s
  let h := u - m
  let d := m - r
  have hu := hm.trans_le hmu
  have hp₀ := zero_lt_one.trans_le hp
  have hB (s : ℝ) (hs : 0 < s) : 0 ≤ B s :=
    mul_nonneg (polyB_pos (mul_pos hm hs)).le (BoseShape.C_pos (mul_pos hm hs)).le
  have hBI : IntegrableOn (fun s => lineDensity p s * B s) (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    have hE : (∫ s : ℝ in Ioi 0, lineDensity p s * B s) = m ^ (-p) * (1 + pureP p) := by
      simpa only [B,mul_assoc,pureP] using pureBoseB_moment_scaled hp hp₂.le hm
    rw [hE]
    have hP₀ := pureP_nonneg hp
    exact (mul_pos (Real.rpow_pos_of_pos hm _) (by positivity)).ne'
  have hD : IntegrableOn (fun s => w s * D s) (Ioi 0) :=
    actual_integrable_of_pure hp hp₂ hL hθ (by unfold D fourthD polyA BoseShape.C; fun_prop)
      (fun s hs => (fourthD_pos hm hm hs).le) (pureFourth_moment hp hp₂.le hm).1
  have hT : IntegrableOn T (Ioi 0) := (jointBoseGap_shifted hp hp₂ hL hθ huL hu₁ hm hmu).1
  obtain ⟨hHI,hHE⟩ := fourthSourceRow_integral (m := m) hp hp₂.le hL hθ hu hm hr
  have hPoint (s : ℝ) (hs : 0 < s) :
      d * (w s * D s) - h * (lineDensity p s * B s) - T s ≤ H s := by
    have hW := (lawDensity_pos hp₀ hL hθ hs).le
    have hWρ := lawDensity_le_pure hp hp₂ hL hθ hs
    have hM := (scaledExpTail_secant hs hm hmu).2
    have hR := (scaledExpTail_secant hs hr hrm).1
    rw [mul_comm s m] at hM hR
    have hHm := mul_le_mul_of_nonneg_left (neg_le_neg hM) (mul_nonneg hW (polyB_pos (mul_pos hm hs)).le)
    have hRr := mul_le_mul_of_nonneg_left hR (mul_nonneg hW (polyA_pos (mul_pos hm hs)).le)
    have hC := mul_le_mul_of_nonneg_right hWρ (mul_nonneg (sub_nonneg.mpr hmu) (hB s hs))
    have hA : fourthD m m s = 1 - polyA (m * s) + polyA (m * s) * BoseShape.C (m * s) := by
      unfold fourthD
      unfold polyA
      rw [show -(m * s) = -s * m by ring]
      ring
    have hHE := fourthSourceResponse_eq (r := r) hu hm hs
    unfold fourthSourceResponse adjacentBoseGap at hHE
    unfold H D B T w h d jointBoseGap at *
    linear_combination (norm := ring_nf) hHE * lawDensity p L θ s +
      (m - r) * lawDensity p L θ s * hA + hHm + hRr + hC <;> exact le_rfl
  have hLHS : IntegrableOn (fun s => d * (w s * D s) - h * (lineDensity p s * B s) - T s) (Ioi 0) :=
    ((hD.const_mul d).sub (hBI.const_mul h)).sub hT
  have hComp := setIntegral_mono_on hLHS hHI measurableSet_Ioi (fun s hs => hPoint s hs)
  rw [integral_sub (f := fun s => d * (w s * D s) - h * (lineDensity p s * B s))
      ((hD.const_mul d).sub (hBI.const_mul h)) hT,
    integral_sub (hD.const_mul d) (hBI.const_mul h),integral_const_mul,integral_const_mul] at hComp
  have hB' : (∫ s : ℝ in Ioi 0, lineDensity p s * B s) = m ^ (-p) * (1 + pureP p) := by
    simpa only [B,mul_assoc,pureP] using pureBoseB_moment_scaled hp hp₂.le hm
  rw [hB'] at hComp
  change _ ≤ fourthSourceRow p L θ u m r m
  change fourthSourceRow p L θ u m r m = (∫ s : ℝ in Ioi 0, H s) + d * lawSelf p L θ at hHE
  rw [hHE]
  change d * ((∫ s : ℝ in Ioi 0, w s * D s) + lawSelf p L θ) -
      h * (m ^ (-p) * (1 + pureP p)) - (∫ s : ℝ in Ioi 0, T s) ≤ _
  linarith only [hComp]

theorem deficit_joint_cone {p L θ u m : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (huL : 7 / 8 ≤ u) (hu₁ : u < 1)
    (hm : m ∈ Ioo (u / 2) u) (hDeficit : outerLawDeficit p L θ u ≤ (u - m) *
      ((∫ s : ℝ in Ioi 0, lawDensity p L θ s * fourthD m m s) + lawSelf p L θ)) :
    0 < m - fourthComparisonRoot p L θ u m m ∧
      m - fourthComparisonRoot p L θ u m m < (25 / 28) * (u - m) := by
  let r := fourthComparisonRoot p L θ u m m
  let w := lawDensity p L θ
  let D := (∫ s : ℝ in Ioi 0, w s * fourthD m m s) + lawSelf p L θ
  let I := m ^ (-p) * (1 + pureP p)
  let X := ∫ s : ℝ in Ioi 0, w s * polyB (m * s) * Real.exp (-s * u) * jointBoseGap u s
  let Y := outerLawDeficit p L θ u
  have hp₂ := hP.trans_lt (by norm_num : (9 / 5 : ℝ) < 2)
  have hu : 0 < u := by linarith only [huL]
  have hm₀ := (half_pos hu).trans hm.1
  obtain ⟨⟨hr,hrm⟩,hFourth,_⟩ :=
    fourthComparisonRoot_spec hp hp₂ hL hθ hm₀ hm.2.le hu₁ hm₀.le le_rfl
  change fourthSourceRow p L θ u m r m = 0 at hFourth
  have hQ : 0 ≤ (u - m) * D - Y := sub_nonneg.mpr hDeficit
  have hH := jointFourth_ge hp hp₂ hL hθ huL hu₁ hm₀ hm.2.le hr hrm.le
  change (m - r) * D - (u - m) * I - X ≤ _ at hH
  rw [hFourth] at hH
  obtain ⟨_,hY⟩ := outerLawDeficit_integral (u := u) hp hp₂.le hL hθ hu
  have hY' : Y = ∫ s : ℝ in Ioi 0, w s * polyB (u * s) * jointBoseGap u s := by
    unfold Y
    rw [hY]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s _
    unfold lawPeanoDensity densityPolynomial jointBoseGap w
    rfl
  have hX : X < (1 / 7) * Y := by
    rw [hY']
    exact (jointBoseGap_shifted hp hp₂ hL hθ huL hu₁ hm₀ hm.2.le).2
  have hD := fourthSlope_pure_le hp hp₂ hL hθ hm₀
  change m ^ (-p) * (pureQ p - pureP p) ≤ D at hD
  have hM := Real.rpow_pos_of_pos hm₀ (-p)
  have hI : I < (3 / 4) * D := by
    have h := mul_lt_mul_of_pos_left (jointCone_inner_moment_lt hp hP) hM
    unfold I
    nlinarith only [h,hD]
  have hD₀ : 0 < D := by
    have hP₀ := pureP_nonneg hp
    have hI₀ : 0 < I := mul_pos hM (by positivity)
    linarith only [hI,hI₀]
  refine ⟨sub_pos.mpr hrm,?_⟩
  apply lt_of_mul_lt_mul_right _ hD₀.le
  have hPaid := mul_lt_mul_of_pos_left hI (sub_pos.mpr hm.2)
  linarith only [hH,hQ,hX,hPaid]

theorem feasible_joint_cone {p L θ u m : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (huL : 7 / 8 ≤ u) (hu₁ : u < 1)
    (hm : m ∈ Ioo (u / 2) u) (hFeasible : 0 ≤ diagonalAdjacent p L θ u m) :
    0 < m - fourthComparisonRoot p L θ u m m ∧
      m - fourthComparisonRoot p L θ u m m < (25 / 28) * (u - m) := by
  have hp₂ : p < 2 := hP.trans_lt (by norm_num)
  have hu : 0 < u := by linarith only [huL]
  have hm₀ := (half_pos hu).trans hm.1
  obtain ⟨⟨hr,hrm⟩,_,_⟩ :=
    fourthComparisonRoot_spec hp hp₂ hL hθ hm₀ hm.2.le hu₁ hm₀.le le_rfl
  have hQ := jointAdjacent_le hp hp₂ hL hθ hm₀ hm.2.le hu₁ hr hrm.le
  have hDeficit := sub_nonneg.mp (hFeasible.trans hQ)
  exact deficit_joint_cone hp hP hL hθ huL hu₁ hm hDeficit

end ACS12.GammaMeasure


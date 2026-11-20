import ACS12.JointMomentScaling

/-! The complete fourth-root bracket C5, with the image self mass paid once. -/
namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaDeficit (lineDensity signedDensity)

theorem fourthSlope_pure_le {p L θ m : ℝ} (hp : 1 ≤ p) (hp₂ : p < 2) (hL : 0 < L)
    (hθ : θ ∈ Icc (0 : ℝ) 1) (hm : 0 < m) :
    m ^ (-p) * (pureQ p - pureP p) ≤
      (∫ s : ℝ in Ioi 0, lawDensity p L θ s * fourthD m m s) + lawSelf p L θ := by
  let D := fourthD m m
  have hMeas : Measurable D := by unfold D fourthD polyA BoseShape.C; fun_prop
  have hD₀ (s : ℝ) (hs : 0 < s) := (fourthD_pos hm hm hs).le
  have hD₁ (s : ℝ) (hs : 0 < s) : D s ≤ 1 := by
    have hA := (polyA_pos (mul_pos hm hs)).le
    have hC : BoseShape.C (m * s) ≤ 1 := (BoseShape.C_lt_one (mul_pos hm hs)).le
    have hP := mul_le_mul_of_nonneg_left hC hA
    have hE : (1 + m * s) * Real.exp (-s * m) + polyA (m * s) = 1 := by
      unfold polyA
      rw [show -(m * s) = -s * m by ring]
      ring
    dsimp only [D, fourthD]
    nlinarith only [hP, hE]
  obtain ⟨hρ, hρE⟩ := pureFourth_moment hp hp₂.le hm
  have hi : IntegrableOn (fun s => imageDensity p L s * D s) (Ioi 0) := by
    simpa only [lawDensity, sub_self, zero_mul, one_mul, zero_add] using
      actual_integrable_of_pure hp hp₂ hL (θ := 1) ⟨zero_le_one, le_rfl⟩ hMeas hD₀ hρ
  obtain ⟨he, heE⟩ := signedDensity_total hp hp₂ hL
  have hEq (s : ℝ) : signedDensity p L s * D s = lineDensity p s * D s - imageDensity p L s * D s := by
    unfold signedDensity
    ring
  have hI : IntegrableOn (fun s => signedDensity p L s * D s) (Ioi 0) :=
    (hρ.sub hi).congr (Eventually.of_forall fun s => (hEq s).symm)
  have hLe := setIntegral_mono_on hI he measurableSet_Ioi
    (fun s hs => by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hD₁ s hs) (signedDensity_pos hp hp₂ hL hs).le)
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => hEq s), integral_sub hρ hi, heE, hρE] at hLe
  rw [lawIntegral_eq hρ hi, hρE, lawSelf]
  nlinarith only [mul_le_mul_of_nonneg_left hLe hθ.1]

theorem fourthSource_diag_secant {p L θ u m r : ℝ} (hp : 1 ≤ p) (hp₂ : p < 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hu : 0 < u) (hr : 0 < r) (hrm : r ≤ m) :
    (m - r) * (m ^ (-p) * (pureQ p - pureP p)) ≤
      fourthSourceRow p L θ u m r m - fourthSourceRow p L θ u m m m := by
  have hm := hr.trans_le hrm
  let w := lawDensity p L θ
  let D := fourthD m m
  let F := fourthDensity u m r m
  let G := fourthDensity u m m m
  have hMeas : Measurable D := by unfold D fourthD polyA BoseShape.C; fun_prop
  have hD₀ (s : ℝ) (hs : 0 < s) := (fourthD_pos hm hm hs).le
  have hI : IntegrableOn (fun s => w s * D s) (Ioi 0) :=
    actual_integrable_of_pure hp hp₂ hL hθ hMeas hD₀ (pureFourth_moment hp hp₂.le hm).1
  obtain ⟨hF, hFE⟩ := fourthSourceRow_integral (m := m) hp hp₂.le hL hθ hu hm hr
  obtain ⟨hG, hGE⟩ := fourthSourceRow_integral (m := m) hp hp₂.le hL hθ hu hm hm
  change IntegrableOn (fun s => w s * F s) (Ioi 0) at hF
  change IntegrableOn (fun s => w s * G s) (Ioi 0) at hG
  have hPoint (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) : (m - r) * (w s * D s) ≤ w s * F s - w s * G s := by
    have hs₀ : 0 < s := hs
    have hβ := (scaledExpTail_secant hs₀ hr hrm).1
    rw [mul_comm s m] at hβ
    have h := mul_le_mul_of_nonneg_left hβ
      (mul_nonneg (lawDensity_pos (zero_lt_one.trans_le hp) hL hθ hs₀).le (polyA_pos (mul_pos hm hs₀)).le)
    simp only [D, F, G, fourthD, fourthDensity] at *
    linear_combination h
  have hCmp := setIntegral_mono_on (hI.const_mul (m-r)) (hF.sub hG) measurableSet_Ioi hPoint
  change (∫ s : ℝ in Ioi 0, (m - r) * (w s * D s)) ≤
    (∫ s : ℝ in Ioi 0, w s * F s - w s * G s) at hCmp
  rw [integral_const_mul, integral_sub hF hG] at hCmp
  change fourthSourceRow p L θ u m r m = (∫ s : ℝ in Ioi 0, w s * F s) + _ at hFE
  change fourthSourceRow p L θ u m m m = (∫ s : ℝ in Ioi 0, w s * G s) + _ at hGE
  rw [hFE, hGE]
  have hSlope := mul_le_mul_of_nonneg_left (fourthSlope_pure_le hp hp₂ hL hθ hm) (sub_nonneg.mpr hrm)
  change _ ≤ (m-r) * ((∫ s : ℝ in Ioi 0, w s * D s) + lawSelf p L θ) at hSlope
  nlinarith only [hSlope, hCmp]


end ACS12.GammaMeasure

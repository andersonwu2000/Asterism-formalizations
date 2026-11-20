import ACS12.JointActualCone
import ACS12.OuterJointHead
import ACS12.OuterGap

namespace ACS12.GammaMeasure
open CenteredCircle.AllN MeasureTheory Set Filter

theorem outerDenom_le_fourthSlope {p L θ u m : ℝ} (hp : 1 ≤ p) (hp₂ : p < 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hm : 0 < m) (hmu : m ≤ u) :
    outerLawDenom p L θ u ≤
      (∫ s : ℝ in Ioi 0, lawDensity p L θ s * fourthD m m s) + lawSelf p L θ := by
  have hu := hm.trans_le hmu
  let w := lawDensity p L θ
  let Q (s : ℝ) := w s * (1 + u * s) * Real.exp (-s * u)
  have hQ₀ : IntegrableOn (fun s => w s * Real.exp (-s * u)) (Ioi 0) := by
    simpa only [pow_zero,mul_one] using lawMoment_integrable hp hp₂.le hL hθ hu 0
  have hQ₁ : IntegrableOn (fun s => w s * s * Real.exp (-s * u)) (Ioi 0) := by
    simpa only [pow_one] using lawMoment_integrable hp hp₂.le hL hθ hu 1
  have hQe (s : ℝ) : Q s = w s * Real.exp (-s * u) + u * (w s * s * Real.exp (-s * u)) := by
    unfold Q; ring
  have hQI : IntegrableOn Q (Ioi 0) := (hQ₀.add (hQ₁.const_mul u)).congr
    (Eventually.of_forall fun s => (hQe s).symm)
  have hQE : (∫ s : ℝ in Ioi 0, Q s) = outerLawDenom p L θ u - lawSelf p L θ := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => hQe s),
      integral_add hQ₀ (hQ₁.const_mul u),integral_const_mul]
    unfold outerLawDenom lawMoment w
    simp only [pow_zero,mul_one,pow_one]
    ring
  have hDI : IntegrableOn (fun s => w s * fourthD m m s) (Ioi 0) :=
    actual_integrable_of_pure hp hp₂ hL hθ (by unfold fourthD polyA BoseShape.C; fun_prop)
      (fun s hs => (fourthD_pos hm hm hs).le) (pureFourth_moment hp hp₂.le hm).1
  have hComp := setIntegral_mono_on hQI hDI measurableSet_Ioi (fun s hs => ?_)
  · rw [hQE] at hComp
    linarith only [hComp]
  · have hA := polyA_monotone_nonneg (show m * s ∈ Ici 0 from (mul_pos hm hs).le)
      (show u * s ∈ Ici 0 from (mul_pos hu hs).le) (mul_le_mul_of_nonneg_right hmu hs.le)
    have hAC := mul_nonneg (polyA_pos (mul_pos hm hs)).le (BoseShape.C_pos (mul_pos hm hs)).le
    have hCore : (1 + u * s) * Real.exp (-s * u) ≤ fourthD m m s := by
      unfold polyA at hA
      rw [show -(m * s) = -s * m by ring, show -(u * s) = -s * u by ring] at hA
      unfold fourthD
      nlinarith only [hA,hAC]
    have h := mul_le_mul_of_nonneg_left hCore (lawDensity_pos (zero_lt_one.trans_le hp) hL hθ hs).le
    simpa only [Q,w,mul_assoc] using h

theorem outerMass_feasible {p L θ u : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (huL : 7 / 8 ≤ u) (hu₁ : u < 1) :
    let m := outerLawMass p L θ u
    m ∈ Ioo (u / 2) u ∧ 2 * u - 1 ≤ m ∧ 0 ≤ diagonalAdjacent p L θ u m := by
  let m := outerLawMass p L θ u
  let r := fourthComparisonRoot p L θ u m m
  have hp₂ : p < 2 := hP.trans_lt (by norm_num)
  have hu : 0 < u := by linarith only [huL]
  obtain ⟨hm,hmu⟩ := outerLawMass_mem hp hp₂.le hL hθ hu hu₁
  have hGap := outerLawGap_lt hp hP hL hθ hu hu₁
  change u - m < 1 - u at hGap
  have hmL : 2 * u - 1 ≤ m := by linarith only [hGap]
  have hmHalf : u / 2 < m := by linarith only [hGap,huL]
  have hD := outerLawDenom_pos hp hp₂.le hL hθ hu
  have hExact : outerLawDeficit p L θ u = (u-m) * outerLawDenom p L θ u := by
    dsimp only [m,outerLawMass]
    field_simp
    <;> ring
  have hSlope := outerDenom_le_fourthSlope hp hp₂ hL hθ hm hmu.le
  have hDeficit : outerLawDeficit p L θ u ≤ (u - m) *
      ((∫ s : ℝ in Ioi 0, lawDensity p L θ s * fourthD m m s) + lawSelf p L θ) := by
    rw [hExact]
    exact mul_le_mul_of_nonneg_left hSlope (sub_nonneg.mpr hmu.le)
  have hCone := (deficit_joint_cone hp hP hL hθ huL hu₁ ⟨hmHalf,hmu⟩ hDeficit).2
  change m - r < _ at hCone
  have hr₀ : 0 < 2 * m - u := by linarith only [hmHalf]
  have hr : 2 * m - u ≤ r := by linarith only [hCone,hmu]
  have hHead := outer_joint_head_lt hp hP hL hθ hu hm hmu hr₀ hr
  have hQ : adjacentSourceLaw p L θ u u m u < adjacentSourceLaw p L θ u m m r := by
    unfold adjacentSourceLaw
    linarith only [hHead]
  rw [outerSourceLaw_eq hp hp₂.le hL hθ hu] at hQ
  change (m-m) * outerLawDenom p L θ u < diagonalAdjacent p L θ u m at hQ
  simp only [sub_self,zero_mul] at hQ
  exact ⟨⟨hmHalf,hmu⟩,hmL,hQ.le⟩

end ACS12.GammaMeasure

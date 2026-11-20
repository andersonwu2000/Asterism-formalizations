import ACS12.AdjacentReturnDensity

/-! The complete clipped adjacent return by finite law and root differences. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaDeficit (signedDensity)

noncomputable def adjacentLawValue (p L θ u m : ℝ) : ℝ :=
  middleLawBase p L θ u + samplingHead (lawRightClip p L θ u) u m

theorem adjacentLawValue_eq {p L θ u m : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hu : 0 < u) (hm : 0 < m) :
    adjacentLawValue p L θ u m = adjacentLawSignedValue p L θ u m +
      samplingTail (lawRightNegative p L θ u) u m +
      m * (lawRightClip p L θ u u - lawRightTest p L θ u u) := by
  let K := lawRightClip p L θ u
  have hQ := lawRightClip_quadratureData (u := u) hp hp₂ hL hθ hu
  unfold adjacentLawValue adjacentLawSignedValue
  rw [samplingHead_split K u m (hQ.summable u m le_rfl hm)]
  change _ + (m * K u + samplingTail (fun t => max 0 (lawRightTest p L θ u t)) u m) = _
  rw [clipped_tail_eq hp hp₂ hL hθ hu.le hm]
  change _ = _ + m * (K u - lawRightTest p L θ u u)
  ring

theorem adjacentValue_motion_le {p L θ u x y : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hu : 0 < u) (hx : 0 < x) (hxy : x ≤ y)
    (hG : 0 < lawRightTest p L θ u u) :
    adjacentLawValue p L θ u y ≤ adjacentLawValue p L θ u x + (y - x) * lawRightTest p L θ u u := by
  let K := lawRightClip p L θ u
  have hy := hx.trans_le hxy
  have hQ := lawRightClip_quadratureData (u := u) hp hp₂ hL hθ hu
  have hTail := hQ.tail_anti u le_rfl hx hy hxy
  have hK : K u = lawRightTest p L θ u u := max_eq_right hG.le
  unfold adjacentLawValue
  rw [samplingHead_split K u y (hQ.summable u y le_rfl hy),
    samplingHead_split K u x (hQ.summable u x le_rfl hx), hK]
  nlinarith only [hTail]

theorem adjacentLawValue_lt_of_roots {p L θ₁ θ₂ u m₁ m₂ : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hL : 0 < L) (hθ₁ : θ₁ ∈ Icc (0 : ℝ) 1) (hθ₂ : θ₂ ∈ Icc (0 : ℝ) 1)
    (hθ : θ₁ < θ₂) (hu : 0 < u) (hu₁ : u < 1)
    (hm₁ : m₁ ∈ Ioo 0 u) (hm₂ : 0 < m₂) (hgap : u - m₁ ≤ 1 - u)
    (h₁ : adjacentDiagonal p L θ₁ u m₁ = 0) (h₂ : adjacentDiagonal p L θ₂ u m₂ = 0)
    (hG : 0 < lawRightTest p L θ₂ u u) :
    adjacentLawValue p L θ₂ u m₂ < adjacentLawValue p L θ₁ u m₁ := by
  have hp₂ : p < 2 := hP.trans_lt (by norm_num)
  let e := signedDensity p L
  let Q := adjacentSourceResponse u m₁
  let R := adjacentNativeResponse u m₁
  let D := outerLawDenom p L θ₂ u
  let G := lawRightTest p L θ₂ u u
  let c := G / D
  have hD : 0 < D := outerLawDenom_pos hp hp₂.le hL hθ₂ hu
  have hc : 0 ≤ c := (div_pos hG hD).le
  have hc' : c < 83 / 300 := lawRightCoefficient_lt hp hp₂.le hL hθ₂ hu hu₁
  have hMul : c * D = G := div_mul_cancel₀ _ hD.ne'
  obtain ⟨hQ, hQE⟩ := adjacentDiagonal_law_difference (m := m₁) hp hp₂ hL hθ₁ hθ₂ hu hm₁.1
  obtain ⟨hR, hRE⟩ := adjacentSignedValue_law_difference (m := m₁) hp hp₂ hL hθ₁ hθ₂ hu hm₁.1
  letI : NeZero (volume.restrict (Ioi (0 : ℝ))) := ⟨positiveHalfLine_ne_zero⟩
  have hQPos : 0 < ∫ s : ℝ in Ioi 0, e s * Q s := by
    have h := integral_strict_of_ae_lt (volume.restrict (Ioi (0 : ℝ))) (integrable_zero ℝ ℝ _) hQ ?_
    · simpa only [integral_zero] using h
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs₀ : 0 < s := hs
      have hGap := (adjacentBoseGap_bounds hs₀ hm₁.1 hm₁.2.le).1
      have hB := scaledExpTail_strictAnti hs₀ hu (mem_Ioi.mpr zero_lt_one) hu₁
      have hE : u - adjacentEffectiveMass u m₁ s = adjacentBoseGap u m₁ s := by
        unfold adjacentEffectiveMass
        ring
      change 0 < e s * Q s
      unfold Q adjacentSourceResponse outerSourceResponse
      rw [hE]
      exact mul_pos (signedDensity_pos hp hp₂ hL hs₀)
        (add_pos_of_pos_of_nonneg (mul_pos (polyB_pos (mul_pos hu hs₀)) (sub_pos.mpr hB))
          (mul_nonneg (polyA_pos (mul_pos hu hs₀)).le hGap))
  rw [h₁, sub_zero] at hQE
  have hRootPos : 0 < adjacentDiagonal p L θ₂ u m₁ := hQE.symm ▸ mul_pos (sub_pos.mpr hθ) hQPos
  have hm : m₁ < m₂ := by
    by_contra! h
    have hC := (adjacentDiagonal_strictAnti hp hp₂.le hL hθ₂ hu).antitoneOn hm₂ hm₁.1 h
    exact hRootPos.not_ge (hC.trans h₂.le)
  have hSec := adjacentDiagonal_secant_lt hp hp₂.le hL hθ₂ hu hm₁.1 hm
  rw [h₂, hQE, sub_pos] at hSec
  change (m₂ - m₁) * D < (θ₂ - θ₁) * ∫ s : ℝ in Ioi 0, e s * Q s at hSec
  have hMotion : (m₂ - m₁) * G ≤ (θ₂ - θ₁) * (c * ∫ s : ℝ in Ioi 0, e s * Q s) := by
    have h := mul_le_mul_of_nonneg_left hSec.le hc
    rw [← hMul]
    nlinarith only [h]
  have hEq (s : ℝ) : e s * (R s - c * Q s) = e s * R s - c * (e s * Q s) := by ring
  have hI : IntegrableOn (fun s => e s * (R s - c * Q s)) (Ioi 0) :=
    (hR.sub (hQ.const_mul c)).congr (Eventually.of_forall fun s => (hEq s).symm)
  have hPos : 0 < ∫ s : ℝ in Ioi 0, e s * (R s - c * Q s) := by
    have h := integral_strict_of_ae_lt (volume.restrict (Ioi (0 : ℝ))) (integrable_zero ℝ ℝ _) hI ?_
    · simpa only [integral_zero] using h
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs₀ : 0 < s := hs
      obtain ⟨hG₀, hG₁⟩ := adjacentBoseGap_bounds hs₀ hm₁.1 hm₁.2.le
      have hE : u - adjacentEffectiveMass u m₁ s = adjacentBoseGap u m₁ s := by
        unfold adjacentEffectiveMass
        ring
      exact mul_pos (signedDensity_pos hp hp₂ hL hs₀)
        (outerReturn_density_pos hu hu₁ hs₀ (hE.symm ▸ hG₀) (hE.symm ▸ hG₁.trans hgap) hc hc')
  have hN := mul_pos (sub_pos.mpr hθ) hPos
  simp_rw [hEq] at hN
  rw [integral_sub hR (hQ.const_mul c), integral_const_mul] at hN
  change 0 < (θ₂ - θ₁) * ((∫ s : ℝ in Ioi 0, e s * R s) -
    c * ∫ s : ℝ in Ioi 0, e s * Q s) at hN
  have hK₂ : lawRightClip p L θ₂ u u = lawRightTest p L θ₂ u u := max_eq_right hG.le
  have hK₁ : lawRightTest p L θ₁ u u ≤ lawRightClip p L θ₁ u u := le_max_right _ _
  have hFixed₂ := adjacentLawValue_eq hp hp₂.le hL hθ₂ hu hm₁.1
  have hFixed₁ := adjacentLawValue_eq hp hp₂.le hL hθ₁ hu hm₁.1
  rw [hK₂, sub_self, mul_zero, add_zero] at hFixed₂
  have hClipped := lawRightNegative_tail_antitone (u := u) hp hp₂ hL hθ₁ hθ₂ hθ.le hu.le hm₁.1
  have hValueMotion := adjacentValue_motion_le hp hp₂.le hL hθ₂ hu hm₁.1 hm.le hG
  have hNonneg := mul_nonneg hm₁.1.le (sub_nonneg.mpr hK₁)
  change adjacentLawSignedValue p L θ₂ u m₁ - adjacentLawSignedValue p L θ₁ u m₁ =
    -(θ₂ - θ₁) * ∫ s : ℝ in Ioi 0, e s * R s at hRE
  change adjacentLawValue p L θ₂ u m₂ ≤ adjacentLawValue p L θ₂ u m₁ + (m₂ - m₁) * G at hValueMotion
  nlinarith only [hMotion, hN, hRE, hFixed₂, hFixed₁, hClipped, hValueMotion, hNonneg]

theorem adjacentLawValue_one {p L u m : ℝ} (hp : 0 < p) (hL : 0 < L) (hu : 0 < u) (hm : 0 < m) :
    adjacentLawValue p L 1 u m =
      middleBase p L u + samplingHead (rightClip p L (middleA u) (middleZ u)) u m := by
  have hZ : lawUnitSlope p L 1 = unitSlopeTotal p L := by
    have hEq : lawMoment p L 1 1 = imageSlope p L := funext (lawMoment_one_slope p L)
    rw [lawUnitSlope, unitSlopeTotal, hEq]
  unfold adjacentLawValue
  rw [show middleLawBase p L 1 u = middleBase p L u by
    simp only [middleLawBase, middleBase, lawMoment_one_radial, lawMoment_one_slope, hZ, lawSelf, one_mul]]
  congr 1
  unfold samplingHead
  apply congrArg (m * ·)
  apply tsum_congr
  intro j
  change max 0 (lawRightTest p L 1 u _) = max 0 (rightTest p L (middleA u) (middleZ u) _)
  rw [lawRightTest_one hp hL (by positivity)]

end ACS12.GammaMeasure

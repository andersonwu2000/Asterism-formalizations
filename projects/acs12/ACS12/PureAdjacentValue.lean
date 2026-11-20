import ACS12.AdjacentEndpointCertificate
import ACS12.PureAdjacentOneValue
import ACS12.PureAdjacentExponentTail
import ACS12.PureNativeExponentMiddle
import ACS12.PureNativeExponentUpper
import ACS12.PureZCurvature

/-! Whole-band strict clipped value at the common cubic adjacent source cap. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN Set

private theorem normalizedNative_semiconvex {u l M : ℝ} (hu : 0 < u) (hl : 1 ≤ l)
    (hM : ∀ p ∈ interior (Icc l (9 / 5)), M ≤ pureNativeBandDD u p) :
    ConvexOn ℝ (Icc l (9 / 5)) (fun p => pureNativeBand u p - pureZ p + (1 / 16 - M / 2) * p ^ 2) := by
  let f (p : ℝ) := pureNativeBand u p - (M / 2) * p ^ 2
  let d (p : ℝ) := pureNativeBandD u p - M * p
  let e (p : ℝ) := pureNativeBandDD u p - M
  have hD (p : ℝ) : HasDerivAt f (d p) p := by
    convert (pureNativeBand_deriv hu).sub (((hasDerivAt_id p).pow 2).const_mul (M / 2)) using 1
    norm_num [d, id_eq] <;> ring
  have hE (p : ℝ) : HasDerivAt d (e p) p := by
    simpa only [d, e, id_eq, mul_one, Pi.sub_apply] using
      (pureNativeBandD_deriv hu).sub ((hasDerivAt_id p).const_mul M)
  have hF : ConvexOn ℝ (Icc l (9 / 5)) f := by
    exact convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (fun p _ => (hD p).continuousAt.continuousWithinAt)
      (fun p _ => (hD p).hasDerivWithinAt)
      (fun p _ => (hE p).hasDerivWithinAt)
      (fun p hp => sub_nonneg.mpr (hM p hp))
  have hZ := pureZ_semiconcave.subset (Icc_subset_Icc hl le_rfl) (convex_Icc _ _)
  apply (hF.add hZ).congr
  intro p _
  simp only [f, Pi.add_apply]
  ring

private theorem commonUpper_semiconvex {u M : ℝ} (hu : 0 < u)
    (hM : ∀ p ∈ Ioo (1 : ℝ) (9 / 5), M ≤ pureNativeBandDD u p) :
    ConvexOn ℝ (Icc 1 (9 / 5)) (fun p => commonAdjacentUpperValue u p + (1 / 16 - M / 2) * p ^ 2) := by
  have hK := normalizedNative_semiconvex hu (l := 1) le_rfl
    (fun p hp => hM p (by simpa only [interior_Icc] using hp))
  refine ⟨hK.1, ?_⟩
  intro p hp q hq a b ha hb hab
  have h := hK.2 hp hq ha hb hab
  simp only [smul_eq_mul] at h ⊢
  unfold commonAdjacentUpperValue
  have hE : upperFollowingValue u / u + (13 / 1875) * (9 / 5 - (a * p + b * q)) =
      a * (upperFollowingValue u / u + (13 / 1875) * (9 / 5 - p)) +
      b * (upperFollowingValue u / u + (13 / 1875) * (9 / 5 - q)) := by
    linear_combination -(upperFollowingValue u / u + (13 / 1875) * (9 / 5 : ℝ)) * hab
  nlinarith only [h, hE]

private theorem convex_chord_le {f : ℝ → ℝ} {a b p c : ℝ} (hab : a < b)
    (ha : a ≤ p) (hb : p ≤ b)
    (h : ConvexOn ℝ (Icc a b) (fun q => f q + c * q ^ 2)) :
    f p ≤ ((b - p) / (b - a)) * f a + ((p - a) / (b - a)) * f b +
      c * ((b - p) / (b - a)) * ((p - a) / (b - a)) * (b - a) ^ 2 := by
  let r := (b - p) / (b - a)
  let s := (p - a) / (b - a)
  have hd := sub_pos.mpr hab
  have hr : 0 ≤ r := div_nonneg (sub_nonneg.mpr hb) hd.le
  have hs : 0 ≤ s := div_nonneg (sub_nonneg.mpr ha) hd.le
  have hS : r + s = 1 := by dsimp only [r, s]; field_simp [hd.ne']; ring
  have hp : r * a + s * b = p := by dsimp only [r, s]; field_simp [hd.ne']; ring
  have hK := h.2 (show a ∈ Icc a b from ⟨le_rfl, hab.le⟩)
    (show b ∈ Icc a b from ⟨hab.le, le_rfl⟩) hr hs hS
  simp only [smul_eq_mul, hp] at hK
  have hC : r * a ^ 2 + s * b ^ 2 - p ^ 2 = r * s * (b - a) ^ 2 := by
    rw [← hp]
    linear_combination -(r * a ^ 2 + s * b ^ 2) * hS
  have hA : f p ≤ r * f a + s * f b + c * (r * a ^ 2 + s * b ^ 2 - p ^ 2) := by
    nlinarith only [hK]
  rw [hC] at hA
  simpa only [mul_assoc] using hA

private theorem convex_Icc_lt_zero {f : ℝ → ℝ} {a b p : ℝ} (ha : a ≤ p) (hb : p ≤ b)
    (h : ConvexOn ℝ (Icc a b) f) (hA : f a < 0) (hB : f b < 0) : f p < 0 := by
  rcases lt_or_eq_of_le (ha.trans hb) with hab | hab
  · have h' := convex_chord_le (c := 0) hab ha hb (by simpa only [zero_mul, add_zero] using h)
    have hS : (b - p) / (b - a) + (p - a) / (b - a) = 1 := by
      field_simp [(sub_pos.mpr hab).ne']
      ring
    have hR : 0 ≤ (b - p) / (b - a) := div_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hab.le)
    have hT : 0 ≤ (p - a) / (b - a) := div_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hab.le)
    let m := max (f a) (f b)
    have hm : m < 0 := max_lt hA hB
    have hM := add_le_add (mul_le_mul_of_nonneg_left (le_max_left (f a) (f b)) hR)
      (mul_le_mul_of_nonneg_left (le_max_right (f a) (f b)) hT)
    have hE : ((b - p) / (b - a)) * m + ((p - a) / (b - a)) * m = m := by rw [← add_mul, hS, one_mul]
    change _ ≤ _ * m + _ * m at hM
    rw [hE] at hM
    simp only [zero_mul, add_zero] at h'
    exact (h'.trans hM).trans_lt hm
  · rwa [le_antisymm hb (hab ▸ ha)]

private theorem middle_clip_eq {p L u : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hL : 0 < L) (hu : 1 / 2 ≤ u) :
    middleLawBase p L 0 u + samplingHead (lawRightClip p L 0 u) u (adjacentCap p u) =
      u * (pureNativeBand u p - pureZ p) + samplingTail (lawRightClip p L 0 u) u (adjacentCap p u) := by
  have hp₂ := hP.trans (by norm_num : (9 / 5 : ℝ) ≤ 2)
  have hu₀ := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hu
  have hθ : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have hm := adjacentCap_pos hP hu₀
  have hQd := lawRightClip_quadratureData (u := u) hp hp₂ hL hθ hu₀
  rw [middleLawBase_zero hp hp₂ hL, samplingHead_split _ _ _ (hQd.summable u _ le_rfl hm)]
  have hG : lawRightClip p L 0 u u = pureRight p u u := by
    unfold lawRightClip
    rw [lawRightTest_zero hp hp₂ hL hu₀, max_eq_right (pureRight_native_pos hp hp₂ hu).le]
  rw [hG]
  simp only [adjacentCap_eq_ratio]
  unfold pureNativeBand
  change u * (1 + middleA u * p - pureZ p) + _ = _
  ring

private theorem commonUpper_upper_lt {L u : ℝ} (hL : 0 < L) (huL : 2 / 3 ≤ u) (hu' : u ≤ 7 / 8) :
    commonAdjacentUpperValue u (9 / 5) < -(1 / 2000) := by
  have hu := (by norm_num : (1 / 2 : ℝ) ≤ 2 / 3).trans huL
  have hu₀ := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hu
  have h := (pureAdjacent_integral_endpoint hL ⟨huL,hu'⟩).1
  rw [middle_clip_eq (by norm_num) le_rfl hL hu, pureCapTail_upper_eq hL hu hu'] at h
  change u * (pureNativeBand u (9 / 5) - pureZ (9 / 5)) + upperFollowingValue u < _ at h
  have hE : u * commonAdjacentUpperValue u (9 / 5) =
      u * (pureNativeBand u (9 / 5) - pureZ (9 / 5)) + upperFollowingValue u := by
    unfold commonAdjacentUpperValue
    field_simp [hu₀.ne'] <;> ring
  apply lt_of_mul_lt_mul_left _ hu₀.le
  rw [hE]
  linarith only [h, hu']

theorem pure_adjacent_middle_value_neg {p L u : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hL : 0 < L) (huL : 2 / 3 ≤ u) (hu' : u ≤ 7 / 8) :
    middleLawBase p L 0 u + samplingHead (lawRightClip p L 0 u) u (adjacentCap p u) < 0 := by
  have hu := (by norm_num : (1 / 2 : ℝ) ≤ 2 / 3).trans huL
  have hu₀ := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hu
  have hPval := commonUpper_upper_lt hL huL hu'
  have hTailRatio : upperFollowingValue u / u < 7 / 80 := by
    have h := (pureAdjacent_integral_endpoint hL ⟨huL,hu'⟩).2
    rw [pureCapTail_upper_eq hL hu hu'] at h
    exact (div_lt_iff₀ hu₀).mpr h
  have hE : commonAdjacentUpperValue u p < 0 := by
    rcases le_total u (3 / 4) with hU | hU
    · have hConv := commonUpper_semiconvex (M := 1 / 8) hu₀
        (fun q hq => (pureNativeBandDD_middle_gt hq.1.le hq.2.le hu hU).le)
      simp only [show (1 / 16 : ℝ) - (1 / 8) / 2 = 0 by norm_num, zero_mul, add_zero] at hConv
      exact convex_Icc_lt_zero hp hP hConv
        ((commonAdjacentUpperValue_one_middle_lt hu hU hTailRatio).trans (by norm_num)) (hPval.trans (by norm_num))
    · have hConv := commonUpper_semiconvex (M := 49 / 500) hu₀
        (fun q hq => (pureNativeBandDD_upper_gt hq.1.le hq.2.le hU hu').le)
      simp only [show (1 / 16 : ℝ) - (49 / 500) / 2 = 27 / 2000 by norm_num] at hConv
      let a := (9 / 5 - p) / (9 / 5 - 1)
      let b := (p - 1) / (9 / 5 - 1)
      have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr hP) (by norm_num)
      have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hp) (by norm_num)
      have hab : a + b = 1 := by dsimp only [a, b]; ring
      have hb' : b ≤ 1 := by linarith only [ha, hab]
      have h := convex_chord_le (a := 1) (b := 9 / 5) (by norm_num) hp hP hConv
      change commonAdjacentUpperValue u p ≤ a * commonAdjacentUpperValue u 1 +
        b * commonAdjacentUpperValue u (9 / 5) + (27 / 2000) * a * b * (9 / 5 - 1) ^ 2 at h
      have h1 := mul_le_mul_of_nonneg_left (commonAdjacentUpperValue_one_high_lt hU hu' hTailRatio).le ha
      have h2 := mul_le_mul_of_nonneg_left hPval.le hb
      have h3 := mul_le_mul_of_nonneg_right hb' (show 0 ≤ (27 / 2000) * a * (9 / 5 - 1) ^ 2 by positivity)
      nlinarith only [h, h1, h2, h3, ha, hb, hab]
  have hTail := pureCapTail_exponent_le hp hP hL hu hu'
  rw [pureCapTail_upper_eq hL hu hu'] at hTail
  change _ ≤ upperFollowingValue u + (13 / 1875) * u * (9 / 5 - p) at hTail
  rw [middle_clip_eq hp hP hL hu]
  have hU : u * commonAdjacentUpperValue u p =
      u * (pureNativeBand u p - pureZ p) + upperFollowingValue u + (13 / 1875) * u * (9 / 5 - p) := by
    unfold commonAdjacentUpperValue
    field_simp [hu₀.ne'] <;> ring
  have h := mul_neg_of_pos_of_neg hu₀ hE
  rw [hU] at h
  linarith only [h, hTail]

end ACS12.GammaMeasure

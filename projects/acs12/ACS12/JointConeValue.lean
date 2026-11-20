import ACS12.JointConeIncrement
import ACS12.JointRectangleNative
import ACS12.JointDiagonalAdjacent
import ACS12.JointDiagonalFourth
import ACS12.JointLowerUnit
import ACS12.JointFarNativeLicense
import ACS12.JointFarFourthLicense
import ACS12.JointFarSign
import ACS12.JointFarDiagonal
import ACS12.JointClipScaled

/-! Convexity at zero gap and two endpoint checks for the complete receiver. -/
namespace ACS12.GammaMeasure

open Set CenteredCircle.AllN

theorem jointPureValue_convex_diagonal {p L u : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hL : 0 < L) (huL : 7 / 8 ≤ u) (hu₁ : u ≤ 1) :
    ConvexOn ℝ (Icc (2 * u - 1) u) (fun m => jointPureValue p L u m m jointCanonicalMu) := by
  have hp₂ := hP.trans (by norm_num : (9 / 5 : ℝ) ≤ 2)
  have hμ : 0 ≤ jointCanonicalMu := by linarith only [jointCanonicalMu_bounds.1]
  have hN := adjacentSignedValue_mass_convex hp hP hL huL hu₁
  have hQ := adjacentDiagonal_convex_paid hp hP hL huL
  have hH := (fourthDiagonal_convex_restored hp hp₂ hL huL).smul hμ
  convert (hN.add hQ).add hH using 1
  funext m
  simp only [jointPureValue,Pi.add_apply,smul_eq_mul]
  ring

private theorem convex_negative_between {a b x : ℝ} {f : ℝ → ℝ} (hab : a < b)
    (hx : x ∈ Icc a b) (hF : ConvexOn ℝ (Icc a b) f) (ha : f a < 0) (hb : f b < 0) : f x < 0 := by
  let t := (x - a) / (b - a)
  have hD := sub_pos.mpr hab
  have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hx.1) hD.le
  have ht' : t ≤ 1 := (div_le_one hD).mpr (sub_le_sub_right hx.2 a)
  have ht₁ : 0 ≤ 1 - t := sub_nonneg.mpr ht'
  have h := hF.2 (show a ∈ Icc a b from ⟨le_rfl,hab.le⟩)
    (show b ∈ Icc a b from ⟨hab.le,le_rfl⟩) ht₁ ht (sub_add_cancel 1 t)
  simp only [smul_eq_mul] at h
  have hX : (1 - t) * a + t * b = x := by
    unfold t
    field_simp [hD.ne']
    ring
  rw [hX] at h
  rcases lt_or_eq_of_le ht with ht | ht
  · exact h.trans_lt (add_neg_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos ht₁ ha.le) (mul_neg_of_pos_of_neg ht hb))
  · rw [← ht,sub_zero,one_mul,zero_mul,add_zero] at h
    exact h.trans_lt ha

private theorem jointCone_massPenalty_convex {p u : ℝ} (hp : 1 ≤ p) (hu : 0 < 2 * u - 1) :
    ConvexOn ℝ (Icc (2 * u - 1) u) (fun m => (u - m) * m ^ (-p)) := by
  let f (m : ℝ) := (u - m) * m ^ (-p)
  let g (m : ℝ) := -m ^ (-p) - p * (u - m) * m ^ (-p - 1)
  have hD (m : ℝ) (hm : 0 < m) : HasDerivAt f (g m) m := by
    have h := ((hasDerivAt_id m).const_sub u).mul
      (Real.hasDerivAt_rpow_const (x := m) (p := -p) (Or.inl hm.ne'))
    convert h using 1
    unfold g
    simp only [id_eq]
    ring
  have hE (m : ℝ) (hm : 0 < m) :
      HasDerivAt g (p * m ^ (-p - 2) * ((p + 1) * u - (p - 1) * m)) m := by
    have h₁ := Real.hasDerivAt_rpow_const (x := m) (p := -p) (Or.inl hm.ne')
    have h₂ := Real.hasDerivAt_rpow_const (x := m) (p := -p - 1) (Or.inl hm.ne')
    have h := h₁.neg.sub (((hasDerivAt_id m).const_sub u).mul h₂ |>.const_mul p)
    convert h using 1
    · funext x
      unfold g
      simp only [Pi.neg_apply,Pi.sub_apply,Pi.mul_apply,id_eq]
      ring
    have hPow : m ^ (-p - 1) = m ^ (-p - 2) * m := by
      rw [← Real.rpow_add_one hm.ne']
      congr 1
      ring
    rw [show -p - 1 - 1 = -p - 2 by ring,hPow]
    simp only [id_eq,zero_sub,neg_mul,one_mul]
    ring
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := g) (convex_Icc _ _)
    (fun m hm => (hD m (hu.trans_le hm.1)).continuousAt.continuousWithinAt)
    (fun m hm => (hD m (hu.trans_le (interior_subset hm).1)).hasDerivWithinAt)
    (fun m hm => (hE m (hu.trans_le (interior_subset hm).1)).hasDerivWithinAt)
  intro m hm
  have hm' : m ∈ Icc (2 * u - 1) u := interior_subset hm
  have hm₀ := hu.trans_le hm'.1
  have hU := hm₀.trans_le hm'.2
  have h := mul_le_mul_of_nonneg_left hm'.2 (sub_nonneg.mpr hp)
  exact mul_nonneg (by have := zero_lt_one.trans_le hp; positivity) (by linarith only [h,hU])

private theorem jointCone_unit_debit {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    jointPureUnit 1 0 p + (9 / 10) * max 0 (jointPureMismatch p) < 0 := by
  have hClip : 0 ≤ jointClipPrice p := by
    have hC := jointClipCut_pos hp
    unfold jointClipPrice jointClipAlpha
    positivity
  have hExtra := mul_le_mul_of_nonneg_left (jointPureMismatch_posPart_le hp hP) (by norm_num : (0 : ℝ) ≤ 1 / 10)
  rcases le_total (jointPureMismatch p) 0 with h | h
  · have hU := jointPureUnit_clip_lt (k := 1) (c := 0) (by norm_num) le_rfl le_rfl (by norm_num) hp hP
    rw [max_eq_left h,mul_zero,add_zero]
    linarith only [hU,hClip,hP]
  · have hU := jointPureUnit_clip_lt (k := 1) (c := 4 / 5) (by norm_num) le_rfl (by norm_num) le_rfl hp hP
    rw [max_eq_right h] at hExtra ⊢
    unfold jointPureUnit at hU ⊢
    linarith only [hU,hClip,hExtra,hP]

private theorem jointCone_far_debit {p L : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) (hL : 0 < L) :
    jointPureValue p L (7 / 8) (3 / 4) (3 / 4) jointCanonicalMu + jointClipPrice p / 8 +
        (9 / 80) * (3 / 4 : ℝ) ^ (-p) * max 0 (jointPureMismatch p) < 0 := by
  have hDiag := jointPure_farDiagonal_le hp hP hL
  have hPower : (3 / 4 : ℝ) ^ (-p) ≤ 1679 / 1000 := by
    have hE : (3 / 4 : ℝ) ^ (-p) = (3 / 4 : ℝ) ^ (1 - p) * (4 / 3) := by
      rw [show (4 / 3 : ℝ) = (3 / 4 : ℝ) ^ (-(1 : ℝ)) by norm_num [Real.rpow_neg_one],
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 3 / 4),show 1 - p + -1 = -p by ring]
    rw [hE]
    linarith only [jointLowerMassScale_le hP]
  have hA := mul_le_mul hPower (jointPureMismatch_posPart_le hp hP) (le_max_left _ _)
    (by norm_num : (0 : ℝ) ≤ 1679 / 1000)
  have hC : (1 / 80) * (3 / 4 : ℝ) ^ (-p) * max 0 (jointPureMismatch p) ≤
      (3 / 2000) * (9 / 5 - p) := by
    have hB := mul_nonneg (sub_nonneg.mpr hP) (show (0 : ℝ) ≤ 3 / 2000 - (1 / 80) * (1679 / 1000) * (69 / 1000) by norm_num)
    linarith only [hA,hB]
  have hChord := jointFarValue_linear_margin hp hP
  unfold jointFarValue at hChord
  linarith only [hDiag,hChord,hC,hP]

private theorem jointCone_lower_value_neg {p L u t q : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hL : 0 < L) (huL : 7 / 8 ≤ u) (hu₁ : u < 1) (ht : 0 ≤ t) (hq : 0 < q) (hq₁ : q ≤ 1) :
    jointPureValue p L u (2 * u - 1) (2 * u - 1) jointCanonicalMu +
      (9 / 10) * (1 - u) * (2 * u - 1) ^ (-p) * max 0 (jointPureMismatch p) +
        samplingTail (lawRightNegative p L 0 u) t q < 0 := by
  let d := 1 - u
  let m := lowerDiagonalMass d
  let θ := 8 * d
  let C := max 0 (jointPureMismatch p)
  let T := jointClipPrice p
  let Q (x : ℝ) := if x = 0 then jointPureUnit 1 0 p else lowerDiagonalResponse 0 p x / x
  have hd : 0 < d := sub_pos.mpr hu₁
  have hdU : d ≤ 1 / 8 := by unfold d; linarith only [huL]
  have hdI : d ∈ Icc (0 : ℝ) (1 / 8) := ⟨hd.le,hdU⟩
  have hmE : m = 2 * u - 1 := by unfold m d lowerDiagonalMass; ring
  have hp₀ := zero_lt_one.trans_le hp
  have hp₂ : p ≤ 2 := hP.trans (by norm_num)
  have hθ : 0 < θ := by unfold θ; positivity
  have hθ₁ : 0 ≤ 1 - θ := by unfold θ; linarith only [hdU]
  have hBlend : (1 - θ) • (0 : ℝ) + θ • (1 / 8 : ℝ) = d := by simp only [smul_eq_mul,θ]; ring
  have h₀ : (0 : ℝ) ∈ Icc 0 (1 / 8) := by norm_num
  have h₁ : (1 / 8 : ℝ) ∈ Icc 0 (1 / 8) := by norm_num
  have hQ := (lowerDiagonalQuotient_convex hp hP).2 h₀ h₁ hθ₁ hθ.le (by ring)
  change Q ((1 - θ) • (0 : ℝ) + θ • (1 / 8 : ℝ)) ≤ (1 - θ) • Q 0 + θ • Q (1 / 8) at hQ
  rw [hBlend] at hQ
  simp only [smul_eq_mul,Q,if_neg hd.ne',if_true,if_false,show (1 / 8 : ℝ) ≠ 0 by norm_num] at hQ
  have hM := (negativePower_convex hp₀).2 (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show (3 / 4 : ℝ) ∈ Ioi 0 by norm_num) hθ₁ hθ.le (by ring)
  simp only [smul_eq_mul,Real.one_rpow] at hM
  rw [show (1 - θ) * 1 + θ * (3 / 4) = m by unfold θ m lowerDiagonalMass; ring] at hM
  have hC₀ : 0 ≤ C := le_max_left _ _
  have hW := mul_le_mul_of_nonneg_left hM (show 0 ≤ (9 / 10) * C by positivity)
  have hClip := jointPureClip_tail_le hp hP hL huL hu₁ ht hq hq₁
  change samplingTail (lawRightNegative p L 0 u) t q ≤ 8 * d ^ 2 * T at hClip
  have hE := lowerDiagonalResponse_zero_eq hp hp₂ hL hdI
  rw [show 1 - d = u by unfold d; ring] at hE
  change lowerDiagonalResponse 0 p d = jointPureValue p L u m m jointCanonicalMu at hE
  have hFarE := lowerDiagonalResponse_zero_eq hp hp₂ hL h₁
  norm_num [lowerDiagonalMass] at hFarE
  have hFar := jointCone_far_debit hp hP hL
  rw [← hFarE] at hFar
  have hFar₈ : lowerDiagonalResponse 0 p (1 / 8) / (1 / 8) + (9 / 10) * (3 / 4 : ℝ) ^ (-p) * C + T < 0 := by
    change _ + _ / 8 + (9 / 80) * (3 / 4 : ℝ) ^ (-p) * C < 0 at hFar
    linarith only [hFar]
  have hUnit := jointCone_unit_debit hp hP
  have hStrict := add_neg_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos hθ₁ hUnit.le)
    (mul_neg_of_pos_of_neg hθ hFar₈)
  have hSum := add_le_add hQ hW
  have hB := mul_le_mul_of_nonneg_left hSum hd.le
  have hdE : d * (lowerDiagonalResponse 0 p d / d) = lowerDiagonalResponse 0 p d := by field_simp [hd.ne']
  rw [mul_add,hdE,hE] at hB
  have hS := mul_neg_of_pos_of_neg hd hStrict
  rw [← hmE]
  change _ + (9 / 10) * d * m ^ (-p) * C + _ < 0
  unfold θ at hB hS
  linarith only [hB,hClip,hS]

theorem jointPure_cone_value_neg {p L u m r : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) (hL : 0 < L)
    (huL : 7 / 8 ≤ u) (hu₁ : u < 1) (hm : m ∈ Icc (2 * u - 1) u)
    (hd : 0 ≤ m - r) (hdU : m - r ≤ (9 / 10) * (u - m)) :
    jointPureValue p L u m r jointCanonicalMu + samplingTail (lawRightNegative p L 0 u) u m < 0 := by
  let a := 2 * u - 1
  let C := max 0 (jointPureMismatch p)
  let T := samplingTail (lawRightNegative p L 0 u) u m
  let f (v : ℝ) := jointPureValue p L u v v jointCanonicalMu + (9 / 10) * C * ((u - v) * v ^ (-p)) + T
  have ha : 0 < a := by unfold a; linarith only [huL]
  have hau : a < u := by unfold a; linarith only [hu₁]
  have hu := ha.trans hau
  have hm₀ := ha.trans_le hm.1
  have hm₁ := hm.2.trans hu₁.le
  have hC₀ : 0 ≤ C := le_max_left _ _
  have hμ₀ : 0 ≤ jointCanonicalMu := by linarith only [jointCanonicalMu_bounds.1]
  have hμ₁ : jointCanonicalMu ≤ 9 / 500 := by linarith only [jointCanonicalMu_bounds.2]
  have hδ := sub_pos.mpr hu₁
  have hLower : f a < 0 := by
    have h := jointCone_lower_value_neg hp hP hL huL hu₁ hu.le hm₀ hm₁
    unfold f a T C
    convert h using 1
    ring
  have hUpper : f u < 0 := by
    have hD := jointPure_upperDiag_bound hp hP hL huL hu₁ hμ₀ hμ₁
    have hClip := jointPureClip_tail_le hp hP hL huL hu₁ hu.le hm₀ hm₁
    have hT₀ : 0 ≤ jointClipPrice p := by
      have hPos := jointClipCut_pos hp
      unfold jointClipPrice jointClipAlpha
      positivity
    have hδU : 1 - u ≤ 1 / 8 := by linarith only [huL]
    have hδ₂ : 8 * (1 - u) ^ 2 ≤ 1 - u := by
      nlinarith only [mul_le_mul_of_nonneg_left hδU hδ.le]
    have hT : T ≤ (1 - u) * jointClipPrice p :=
      hClip.trans (mul_le_mul_of_nonneg_right hδ₂ hT₀)
    have hU := jointPureUnit_clip_lt (k := 0) (c := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp hP
    simp only [jointPureUnit,zero_mul,add_zero] at hU
    unfold f
    simp only [sub_self,zero_mul,mul_zero,add_zero]
    have hU₀ : jointUnitValue p jointCanonicalMu + jointClipPrice p < 0 := by
      linarith only [hU, sub_nonneg.mpr hP]
    linarith only [hD, hT, mul_neg_of_pos_of_neg hδ hU₀, sq_nonneg (1 - u)]
  have hConv : ConvexOn ℝ (Icc a u) f := by
    have hBase := jointPureValue_convex_diagonal hp hP hL huL hu₁.le
    exact ((hBase.add ((jointCone_massPenalty_convex hp ha).smul (show 0 ≤ (9 / 10) * C by positivity))).add_const T)
  have hMid : f m < 0 := convex_negative_between hau hm hConv hLower hUpper
  have hGap := jointPure_wholeCone_increment hp hP hL huL hu₁.le hm.1 hm.2 hd hdU
  let κ := jointPureLambda * (p * (p + 1) * (13 / 6 : ℝ) ^ (-(p + 2 : ℝ))) *
    (288479 / 1588261500)
  have hp₀ : 0 ≤ p := by linarith only [hp]
  have hum : 0 ≤ u - m := sub_nonneg.mpr hm.2
  have hK : 0 ≤ κ * ((u - m) / m) := by
    unfold κ jointPureLambda
    positivity
  have hmPow : 0 ≤ m ^ (-p) := Real.rpow_nonneg hm₀.le _
  change jointPureValue p L u m r jointCanonicalMu -
      jointPureValue p L u m m jointCanonicalMu ≤
    (m - r) * m ^ (-p) * (jointPureMismatch p - κ * ((u - m) / m)) at hGap
  have hG := mul_le_mul_of_nonneg_left
    ((sub_le_self (jointPureMismatch p) hK).trans (le_max_right 0 (jointPureMismatch p)))
    (mul_nonneg hd hmPow)
  have hC := mul_le_mul_of_nonneg_right hdU (mul_nonneg hmPow hC₀)
  unfold f at hMid
  change _ + T < 0
  nlinarith only [hGap, hG, hC, hMid]

end ACS12.GammaMeasure

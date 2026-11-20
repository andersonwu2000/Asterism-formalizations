import ACS12.JointBoseReturnShape
import ACS12.JointBalancedReturn
import ACS12.JointLawDifference
import ACS12.JointFixedDualFrequency

/-! Exact full joint return density and both original source prices. -/
namespace ACS12.GammaMeasure

open CenteredCircle.AllN Set

private noncomputable def jointCorrection (u m s lam : ℝ) : ℝ :=
  (1 - u) * s * Real.exp (-s * u) * (1 - m - (1 - u) * returnQ u s) +
    (scaledExpTail s m - scaledExpTail s 1) *
      (Real.exp (-s * u) * middleRightDensity u s + lam * polyA (u * s))

private theorem jointReturn_identity {u m r s lam : ℝ} (hu : 0 < u) (hu₁ : u < 1) (hs : 0 < s) :
    adjacentNativeResponse u m s - lam * jointSourceResponse u m r s =
      balancedUnitReturn u m s lam + jointCorrection u m s lam - lam * polyA (u * s) * jointRetainedGap m r s := by
  have hQ := returnQ_identity hu₁ hs
  have hU := scaledExpTail_bridge hs hu
  have h1 := scaledExpTail_bridge hs zero_lt_one
  simp only [mul_one] at h1
  unfold adjacentNativeResponse adjacentEffectiveMass adjacentBoseGap outerNativeResponse
    jointSourceResponse adjacentSourceResponse outerSourceResponse balancedUnitReturn
    balancedRight jointCorrection middleRightDensity middleA0 middleZ polyA polyB
  rw [show -(u * s) = -s * u by ring]
  simp only [adjacentEffectiveMass, adjacentBoseGap]
  linear_combination s * (1 - u) * hQ +
    (lam * u * s - ((u - middleA u) * s - (1 - (1 + middleA u * s) * Real.exp (-s)))) * hU -
    (1 + middleA u * s) * (1 - Real.exp (-s * u)) * h1

private theorem jointRetainedDebit_le {u m r s lam : ℝ} (hm : 0 < m) (hmL : 3 / 4 ≤ m)
    (hmu : m ≤ u) (hu₁ : u < 1) (hr : 0 < r) (hrm : r ≤ m) (hs : 0 < s)
    (hBracket : m - r ≤ (4 / 5) * (1 - u)) (hlamU : lam ≤ 83 / 300) :
    lam * polyA (u * s) * jointRetainedGap m r s ≤
      (83 / 1875) * (1 - u) * (1 - Real.exp (-s)) := by
  let δ := 1 - u
  let Z := Real.exp (-s * m)
  have hu := hm.trans_le hmu
  have hA₀ := (polyA_pos (mul_pos hu hs)).le
  have hA := polyA_monotone_nonneg (mul_nonneg hu.le hs.le) hs.le
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hu₁.le hs.le)
  have hE : Z ≤ Real.exp (-(3 / 4) * s) :=
    Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_right hmL hs.le])
  have hK := (adjacentBoseGap_bounds hs hr hrm).2.trans hBracket
  have hK₀ := (adjacentBoseGap_bounds hs hr hrm).1
  have hAK := mul_le_mul hA hE (Real.exp_pos _).le (polyA_pos hs).le
  have hS := hAK.trans (retainedA_exp_lt_fifth hs).le
  have h := mul_le_mul hS hK hK₀
    (div_nonneg (expHead_den_pos hs).le (by norm_num : (0 : ℝ) ≤ 5))
  have hL := mul_le_mul hlamU h (mul_nonneg (mul_nonneg hA₀ (Real.exp_pos _).le) hK₀)
    (by norm_num : (0 : ℝ) ≤ 83 / 300)
  unfold jointRetainedGap
  change lam * polyA (u * s) * (Z * adjacentBoseGap m r s) ≤ _
  nlinarith only [hL]

private theorem jointFourth_price {u m r s : ℝ} (hm : 0 < m) (hmu : m ≤ u) (hu₁ : u < 1)
    (hmL : 2 * u - 1 ≤ m) (hr : 0 < r) (hrm : r ≤ m) (hs : 0 < s)
    (hBracket : m - r ≤ (4 / 5) * (1 - u)) :
    fourthSourceResponse u m r s ≤ (22 / 15) * (1 - u) * (1 - Real.exp (-s)) ∧
      (s ≤ 2 / 3 → fourthSourceResponse u m r s ≤ (9 / 10) * (1 - u) * (1 - Real.exp (-s))) := by
  let δ := 1 - u
  let x := m * s
  let X := Real.exp (-s)
  let Y := Real.exp (-s * u)
  let B := scaledExpTail s m - scaledExpTail s u + Y * (scaledExpTail s u - scaledExpTail s 1)
  let K := adjacentBoseGap m r s
  have hu := hm.trans_le hmu
  have hδ : 0 < δ := sub_pos.mpr hu₁
  have hx : 0 < x := mul_pos hm hs
  have hY : 0 < Y := Real.exp_pos _
  have hY₁ : Y ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [mul_pos hs hu])
  have hB : 0 ≤ B := by
    apply add_nonneg (sub_nonneg.mpr ((scaledExpTail_strictAnti hs).antitoneOn hm hu hmu))
    exact mul_nonneg hY.le (sub_nonneg.mpr ((scaledExpTail_strictAnti hs).antitoneOn hu (mem_Ioi.mpr zero_lt_one) hu₁.le))
  have hB₁ : B ≤ (1 - m) * BoseShape.C x := by
    have hC := BoseShape.C_antitone (mul_pos hs hm) (mul_pos hs hu)
      (mul_le_mul_of_nonneg_left hmu hs.le)
    have h₁ := (scaledExpTail_secant hs hm hmu).2
    have h₂ := ((scaledExpTail_secant hs hu hu₁.le).2).trans (mul_le_mul_of_nonneg_left hC hδ.le)
    have h₂₀ : 0 ≤ scaledExpTail s u - scaledExpTail s 1 :=
      sub_nonneg.mpr ((scaledExpTail_strictAnti hs).antitoneOn hu (mem_Ioi.mpr zero_lt_one) hu₁.le)
    have h₃ := mul_le_mul_of_nonneg_right hY₁ h₂₀
    rw [mul_comm s m] at h₁ h₂
    dsimp only [B,x] at *
    nlinarith only [h₁,h₂,h₃]
  have hK₀ := (adjacentBoseGap_bounds hs hr hrm).1
  have hK := (adjacentBoseGap_bounds hs hr hrm).2
  have hA₀ := (polyA_pos hx).le
  have hB₀ := (polyB_pos hx).le
  have hDen : 0 < 1 - X := expHead_den_pos hs
  have hX : 1 - Real.exp (-x) ≤ 1 - X := by
    apply sub_le_sub_left (Real.exp_le_exp.mpr _)
    dsimp only [x,X]
    nlinarith only [mul_le_mul_of_nonneg_right (hmu.trans hu₁.le) hs.le]
  have hA : polyA x ≤ 1 - X := by
    have h := mul_nonneg hx.le (Real.exp_pos (-x)).le
    apply le_trans _ hX
    unfold polyA
    nlinarith only [h]
  have hAB := mul_le_mul_of_nonneg_left hB₁ hB₀
  have hAK := mul_le_mul hA hK hK₀ hDen.le
  have hRow : fourthSourceResponse u m r s = polyB x * B + polyA x * K :=
    fourthSourceResponse_eq hu hm hs
  have hm₁ : 0 ≤ 1 - m := sub_nonneg.mpr (hmu.trans hu₁.le)
  have hm₂ : 1 - m ≤ 2 * δ := by dsimp only [δ]; linarith only [hmL]
  constructor
  · have hBC := (polyBC_lt_third hx).le.trans (div_le_div_of_nonneg_right hX (by norm_num))
    have hC := mul_le_mul_of_nonneg_left hBC hm₁
    have hD := mul_le_mul_of_nonneg_right hm₂ (div_nonneg hDen.le (by norm_num : (0 : ℝ) ≤ 3))
    have hE := mul_le_mul_of_nonneg_left hBracket hDen.le
    rw [hRow]
    change _ ≤ (22 / 15) * δ * (1 - X)
    nlinarith only [hAB,hAK,hC,hD,hE]
  · intro hSmall
    have hxs : x ≤ s := by dsimp only [x]; simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (hmu.trans hu₁.le) hs.le
    have hQ := pow_le_pow_left₀ hx.le hxs 2
    have hQ₁ : polyA x ≤ s ^ 2 / 2 := (densityPolynomial_lt_quadratic .a hx).le.trans
      (div_le_div_of_nonneg_right hQ (by norm_num))
    have hQ₂ : polyB x ≤ s ^ 2 / 2 := (densityPolynomial_lt_quadratic .b hx).le.trans
      (div_le_div_of_nonneg_right hQ (by norm_num))
    have hC := mul_le_mul_of_nonneg_left (boseC_lt_half hx).le hm₁
    have hC' : B ≤ δ := by linarith only [hB₁,hC,hm₂]
    have h₁ := mul_le_mul hQ₂ hC' hB (by positivity)
    have h₂ := mul_le_mul hQ₁ (hK.trans hBracket) hK₀ (by positivity)
    have hζ : s / (1 - X) ≤ 3 / 2 := by
      have h := mul_le_mul_of_nonneg_left (bose_inverse_B2 hs).le hs.le
      rw [mul_add, mul_add, mul_inv_cancel₀ hs.ne'] at h
      have hs₂ := pow_le_pow_left₀ hs.le hSmall 2
      change s * (1 - X)⁻¹ ≤ _
      nlinarith only [h,hSmall,hs₂]
    have hS : s ^ 2 ≤ 1 - X := by
      have h := mul_le_mul_of_nonneg_right ((div_le_iff₀ hDen).mp hζ) hs.le
      have h' := mul_le_mul_of_nonneg_right hSmall hDen.le
      nlinarith only [h,h']
    have h := mul_le_mul_of_nonneg_left hS hδ.le
    rw [hRow]
    change _ ≤ (9 / 10) * δ * (1 - X)
    nlinarith only [h₁,h₂,h]

private theorem fixedDual_fr1_exp {s : ℝ} :
    (5 / 8 : ℝ) * Real.exp (-(7 / 8) * s) * max 0 (s - 3 / 20) < 5 / 21 := by
  have hExp : (3 : ℝ) < Real.exp (181 / 160) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 181 / 160) 4
    norm_num [Finset.sum_range_succ,Nat.factorial] at h
    linarith only [h]
  by_cases h : s - 3 / 20 ≤ 0
  · rw [max_eq_left h,mul_zero]
    norm_num
  rw [max_eq_right (le_of_not_ge h)]
  let t := (7 / 8 : ℝ) * (s - 3 / 20)
  have ht : t ≤ Real.exp (t - 1) := by linarith only [Real.add_one_le_exp (t - 1)]
  have hScale : (5 / 8 : ℝ) * (s - 3 / 20) = (5 / 7) * t := by unfold t; ring
  have hE : Real.exp (-(7 / 8) * s) * Real.exp (t - 1) = Real.exp (-(181 / 160)) := by
    rw [← Real.exp_add]
    congr 1
    unfold t
    ring
  calc
    _ = (5 / 7 : ℝ) * (Real.exp (-(7 / 8) * s) * t) := by linear_combination Real.exp (-(7 / 8) * s) * hScale
    _ ≤ (5 / 7 : ℝ) * Real.exp (-(181 / 160)) := by
      rw [← hE]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le) (by norm_num)
    _ < 5 / 21 := by
      rw [Real.exp_neg,← div_eq_mul_inv]
      apply (div_lt_iff₀ (Real.exp_pos _)).mpr
      linarith only [hExp]

private theorem fixedDual_balanced {u m s : ℝ} (huL : 7 / 8 ≤ u) (hu₁ : u < 1)
    (hmL : 2 * u - 1 ≤ m) (hs : 0 < s) :
    (1 - u) * (1 - Real.exp (-s)) / 3 < balancedUnitReturn u m s (89 / 500) := by
  let δ := 1 - u
  let X := Real.exp (-s)
  let Y := Real.exp (-s * u)
  let q := returnQ u s
  let ζ := returnZeta s
  let β := expTailFactor s
  let a := middleA u
  let lam : ℝ := 89 / 500
  have hu : 0 < u := by linarith only [huL]
  have hδ : 0 < δ := sub_pos.mpr hu₁
  have hDen : 0 < 1 - X := expHead_den_pos hs
  have hY₀ : 0 < Y := Real.exp_pos _
  have hX₀ : 0 < X := Real.exp_pos _
  have hY : Y ≤ Real.exp (-(7 / 8) * s) := Real.exp_le_exp.mpr (by
    nlinarith only [mul_le_mul_of_nonneg_right huL hs.le])
  have hXY : X ≤ Y := Real.exp_le_exp.mpr (by
    nlinarith only [mul_le_mul_of_nonneg_right hu₁.le hs.le])
  have ha₀ : 0 ≤ a := by
    change 0 ≤ (6 / 25 : ℝ) * u * (2 - u)
    exact mul_nonneg (mul_nonneg (by norm_num) hu.le) (by linarith only [hu₁])
  have ha₁ : a ≤ 6 / 25 := middleA_le u
  have ha₂ : 189 / 800 ≤ a := by
    unfold a middleA
    have hProd := mul_nonneg (sub_nonneg.mpr huL) (show 0 ≤ 9 / 8 - u by linarith only [hu₁])
    nlinarith only [hProd]
  have hβ₀ : 0 ≤ β := div_nonneg hs.le (expTail_den_pos hs).le
  have hβ₁ : β ≤ 1 := (div_le_one (expTail_den_pos hs)).mpr (by linarith only [Real.add_one_le_exp s])
  have hβX : (1 - X) * β = s * X := by
    dsimp only [β,X]
    rw [BoseShape.expTail_eq_decay hs]
    rw [mul_comm,div_mul_cancel₀ _ hDen.ne']
  have hζ : ζ = s + β := returnZeta_eq hs
  have hζD : (1 - X) * ζ = s := by
    change (1 - X) * (s / (1 - X)) = s
    rw [mul_comm,div_mul_cancel₀ _ hDen.ne']
  obtain ⟨hq₀,hq₁⟩ := returnQ_bounds hu.le hu₁ hs
  have hQ := returnQ_identity hu₁ hs
  have hβBridge := scaledExpTail_bridge hs zero_lt_one
  simp only [mul_one] at hβBridge
  have hF : balancedUnitReturn u (2 * u - 1) s lam =
      δ * (middleA0 u s - lam * (1 - Y) +
        Y * (balancedRight u s - lam * u * s) * (q - 2)) := by
    unfold balancedUnitReturn balancedRight middleA0
    dsimp only [δ,a,q,X,Y] at *
    linear_combination
      -(s * (1 - middleA u + middleA u * Real.exp (-s) - lam * u) - 1 + Real.exp (-s)) * hQ +
      (1 + middleA u * s) * (1 - Real.exp (-s * u)) * hβBridge
  have hFA : balancedUnitReturn u (2 * u - 1) s lam ≤ balancedUnitReturn u m s lam := by
    have hA := (polyA_pos (mul_pos hu hs)).le
    unfold polyA at hA
    rw [show -(u * s) = -s * u by ring] at hA
    have hP := mul_nonneg (sub_nonneg.mpr hmL)
      (add_nonneg (mul_nonneg hY₀.le (balancedRight_pos (u := u) hs).le)
        (mul_nonneg (show 0 ≤ lam by norm_num [lam]) hA))
    unfold balancedUnitReturn
    dsimp only [Y] at hP
    linear_combination hP
  let k := 1 - a * (1 - X) - lam * u
  let W := k * ζ - 1
  have hk : 291 / 500 ≤ k := by
    unfold k lam
    nlinarith only [ha₁,hu₁,mul_nonneg ha₀ hX₀.le]
  have hW : balancedRight u s - lam * u * s = (1 - X) * W := by
    unfold balancedRight middleA0 W k
    change (1 - a) * s - (1 - (1 + a * s) * X) - lam * u * s = _
    linear_combination -(1 - a * (1 - X) - lam * u) * hζD
  have hBase : (291 / 500 : ℝ) * (1 - X) ≤ middleA0 u s - lam * (1 - Y) := by
    unfold middleA0
    change _ ≤ 1 - (1 + a * s) * X - lam * (1 - Y)
    have h := mul_le_mul_of_nonneg_right
      (show 291 / 500 ≤ 1 - a * β - lam by
        nlinarith only [ha₁,mul_le_mul_of_nonneg_left hβ₁ ha₀,show lam = 89 / 500 by rfl]) hDen.le
    have hL := mul_le_mul_of_nonneg_left (sub_le_sub_left hXY 1) (show 0 ≤ lam by norm_num [lam])
    linear_combination h + hL - a * hβX
  have hWt : W ≤ (5 / 8) * (s - 3 / 20) := by
    have hLamU : (3 / 20 : ℝ) ≤ lam * u := by unfold lam; linarith only [huL]
    have hA : 1 - a - lam * u ≤ 5 / 8 := by unfold lam; linarith only [ha₂,huL]
    have hB := mul_le_mul_of_nonneg_right hA hs.le
    have hE : a * X * ζ = a * β := by
      apply mul_left_cancel₀ hDen.ne'
      linear_combination a * X * hζD - a * hβX
    have hM := mul_le_mul_of_nonneg_left hβ₁ ha₀
    have hζEq := congrArg (fun t : ℝ => (1 - a - lam * u) * t) hζ
    dsimp only at hζEq
    have hCoeff : 0 ≤ 1 - a - lam * u := by unfold lam; linarith only [ha₁,hu₁]
    have hBound := mul_le_mul_of_nonneg_left hβ₁ hCoeff
    calc
      W = (1 - a - lam * u) * s + (1 - a - lam * u) * β + a * β - 1 := by
        unfold W k
        linear_combination hζEq + hE
      _ ≤ (5 / 8) * s - lam * u := by
        have hSum := add_le_add (add_le_add hB hBound) hM
        linarith only [hSum]
      _ ≤ _ := by linarith only [hLamU]
  have hProd : -(5 / 8 : ℝ) * max 0 (s - 3 / 20) ≤ W * (q - 2) := by
    have hMax : 0 ≤ max 0 (s - 3 / 20) := le_max_left _ _
    by_cases hq : 2 ≤ q
    · have hPos : 0 ≤ W := by
        have hζ₀ : (2 : ℝ) ≤ ζ := hq.trans hq₁
        have h := mul_le_mul hk hζ₀ (by norm_num : (0 : ℝ) ≤ 2) (by linarith only [hk])
        unfold W
        linarith only [h]
      exact (mul_nonpos_of_nonpos_of_nonneg (by norm_num : -(5 / 8 : ℝ) ≤ 0) hMax).trans
        (mul_nonneg hPos (sub_nonneg.mpr hq))
    · have hQ : 0 ≤ 2 - q := sub_nonneg.mpr (le_of_not_ge hq)
      have hQ₁ : 2 - q ≤ 1 := by linarith only [hq₀]
      have hW' : W ≤ (5 / 8 : ℝ) * max 0 (s - 3 / 20) :=
        hWt.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num))
      have h := mul_le_mul hW' hQ₁ hQ (mul_nonneg (by norm_num) hMax)
      linarith only [h]
  have hLoss : -(5 / 21 : ℝ) < Y * (W * (q - 2)) := by
    have h₁ := mul_le_mul_of_nonneg_left hProd hY₀.le
    have h₂ := mul_le_mul_of_nonneg_right hY (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 8)
      (le_max_left 0 (s - 3 / 20)))
    have h₃ := fixedDual_fr1_exp (s := s)
    nlinarith only [h₁,h₂,h₃]
  have hS := mul_lt_mul_of_pos_right hLoss hDen
  have hT := mul_lt_mul_of_pos_left
    (show (1 - X) / 3 < middleA0 u s - lam * (1 - Y) +
      Y * (balancedRight u s - lam * u * s) * (q - 2) by
      rw [hW]
      nlinarith only [hBase,hS,hDen]) hδ
  rw [← hF] at hT
  exact (by dsimp only [δ,X] at hT; linarith only [hT] :
    (1 - u) * (1 - Real.exp (-s)) / 3 < balancedUnitReturn u (2 * u - 1) s lam).trans_le hFA

theorem fixedDual_density_gt {u m r s mu : ℝ} (huL : 7 / 8 ≤ u) (hu₁ : u < 1)
    (hmL : 2 * u - 1 ≤ m) (hmu : m ≤ u) (hr : 0 < r) (hrm : r ≤ m)
    (hBracket : m - r ≤ (4 / 5) * (1 - u)) (hs : 0 < s) (hmuU : mu ≤ 3553 / 200000) :
    (1 - u) * (1 - Real.exp (-s)) / 30 <
      adjacentNativeResponse u m s - (89 / 500) * jointSourceResponse u m r s -
        mu * fourthSourceResponse u m r s := by
  let δ := 1 - u
  let X := Real.exp (-s)
  let Y := Real.exp (-s * u)
  let ζ := returnZeta s
  let q := returnQ u s
  let M := scaledExpTail s m - scaledExpTail s 1
  let g := middleRightDensity u s
  let lam : ℝ := 89 / 500
  have hm := hr.trans_le hrm
  have hu := hm.trans_le hmu
  have hδ : 0 < δ := sub_pos.mpr hu₁
  have hδU : δ ≤ 1 / 8 := by unfold δ; linarith only [huL]
  have hDen : 0 < 1 - X := expHead_den_pos hs
  have hY₀ : 0 < Y := Real.exp_pos _
  have hA := (polyA_pos (mul_pos hu hs)).le
  have hm₁ := hmu.trans hu₁.le
  have hM₀ : 0 ≤ M :=
    sub_nonneg.mpr ((scaledExpTail_strictAnti hs).antitoneOn hm (mem_Ioi.mpr zero_lt_one) hm₁)
  have hM : M ≤ (1 - m) / 2 := by
    have h := (scaledExpTail_secant hs hm hm₁).2
    have hC := mul_le_mul_of_nonneg_left (boseC_lt_half (mul_pos hs hm)).le (sub_nonneg.mpr hm₁)
    linarith only [h,hC]
  have hg : -δ * s ≤ g := by
    have h := balancedRight_pos (u := u) hs
    unfold g middleRightDensity middleZ δ
    unfold balancedRight at h
    nlinarith only [h]
  have hLoss : -(1 - m) / 2 * (δ * s * Y) ≤ M * (Y * g + lam * polyA (u * s)) := by
    have h₁ := mul_le_mul_of_nonneg_left hg (mul_nonneg hM₀ hY₀.le)
    have h₂ := mul_le_mul_of_nonneg_right hM (mul_nonneg (mul_nonneg hδ.le hs.le) hY₀.le)
    have h₃ := mul_nonneg hM₀ (mul_nonneg (show 0 ≤ lam by norm_num [lam]) hA)
    calc
      _ ≤ -(M * (δ * s * Y)) := by
        rw [neg_div]
        simpa only [neg_mul] using neg_le_neg h₂
      _ ≤ M * (Y * g + lam * polyA (u * s)) := by
        linarith only [show -(M * (δ * s * Y)) ≤ M * Y * g by convert h₁ using 1 <;> ring,h₃]
  obtain ⟨hq₀,hq₁⟩ := returnQ_bounds hu.le hu₁ hs
  have hζ₁ : 1 ≤ ζ := hq₀.trans hq₁
  have hζE : ζ = expHeadFactor s := by unfold ζ returnZeta expHeadFactor; rfl
  have hζD : (1 - X) * ζ = s := by
    change (1 - X) * (s / (1 - X)) = s
    rw [mul_comm,div_mul_cancel₀ _ hDen.ne']
  have hG : -(δ ^ 2 * s * Y * (ζ - 1 / 2)) ≤ jointCorrection u m s lam := by
    have hq' := mul_le_mul_of_nonneg_left hq₁ hδ.le
    have h := mul_le_mul_of_nonneg_left
      (show δ * (1 / 2 - ζ) ≤ (1 - m) / 2 - δ * q by
        have hmδ := sub_le_sub_left hmu 1
        change δ ≤ 1 - m at hmδ
        change δ * q ≤ δ * ζ at hq'
        linarith only [hq',hmδ])
      (mul_nonneg (mul_nonneg hδ.le hs.le) hY₀.le)
    change _ ≤ δ * s * Y * (1 - m - δ * q) + M * (Y * g + lam * polyA (u * s))
    nlinarith only [h,hLoss]
  have hF : Y * ζ * (ζ - 1 / 2) < 1 := by
    have hY : Y ≤ Real.exp (-(7 / 8) * s) := Real.exp_le_exp.mpr (by
      nlinarith only [mul_le_mul_of_nonneg_right huL hs.le])
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hY (show 0 ≤ ζ by linarith only [hζ₁]))
      (show 0 ≤ ζ - 1 / 2 by linarith only [hζ₁])
    exact h.trans_lt (hζE.symm ▸ fixedDual_frequency_lt_one hs)
  have hCor : -δ * (1 - X) / 8 < jointCorrection u m s lam := by
    have h₁ := mul_lt_mul_of_pos_left hF hδ
    have h₂ : δ * (Y * ζ * (ζ - 1 / 2)) < 1 / 8 := by linarith only [h₁,hδU]
    have h := mul_lt_mul_of_pos_left h₂ (mul_pos hδ hDen)
    have hEq : δ * (1 - X) * (δ * (Y * ζ * (ζ - 1 / 2))) =
        δ ^ 2 * s * Y * (ζ - 1 / 2) := by
      linear_combination δ ^ 2 * Y * (ζ - 1 / 2) * hζD
    rw [hEq] at h
    linarith only [h,hG]
  have hK : lam * polyA (u * s) * jointRetainedGap m r s ≤
      lam * (4 / 5) * δ * (1 - X) := by
    have hX : Real.exp (-s) ≤ Real.exp (-(u * s)) := Real.exp_le_exp.mpr (by
      nlinarith only [mul_le_mul_of_nonneg_right hu₁.le hs.le])
    have hA' : polyA (u * s) ≤ 1 - X := by
      unfold polyA X
      linarith only [hX,mul_nonneg (mul_nonneg hu.le hs.le) (Real.exp_pos (-(u * s))).le]
    have hGap := adjacentBoseGap_bounds hs hr hrm
    have hE : Real.exp (-s * m) ≤ 1 := Real.exp_le_one_iff.mpr (by
      nlinarith only [mul_nonneg hs.le hm.le])
    have hK' := mul_le_mul hE (hGap.2.trans hBracket) hGap.1 zero_le_one
    have hAK := mul_le_mul hA' hK' (mul_nonneg (Real.exp_pos _).le hGap.1) hDen.le
    have h := mul_le_mul_of_nonneg_left hAK (show 0 ≤ lam by norm_num [lam])
    unfold jointRetainedGap
    nlinarith only [h]
  have hH := (jointFourth_price hm hmu hu₁ hmL hr hrm hs hBracket).1
  have hH' := mul_le_mul hmuU hH (fourthSourceResponse_pos hm hmu hu₁ hr hrm hs).le
    (by norm_num : (0 : ℝ) ≤ 3553 / 200000)
  have hEq := jointReturn_identity (m := m) (r := r) (lam := lam) hu hu₁ hs
  have hB := fixedDual_balanced huL hu₁ hmL hs
  change δ * (1 - X) / 3 < balancedUnitReturn u m s lam at hB
  change δ * (1 - X) / 30 < _
  rw [show (89 / 500 : ℝ) = lam by rfl,hEq]
  norm_num [lam] at hK ⊢
  nlinarith only [hB,hCor,hK,hH',mul_pos hδ hDen]

end ACS12.GammaMeasure

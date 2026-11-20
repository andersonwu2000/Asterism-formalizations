import ACS12.JointBoseBounds
import ACS12.OuterReturnShape

/-! The balanced unit return and its complete DD11–12 frequency margin. -/
namespace ACS12.GammaMeasure

open CenteredCircle.AllN Set

noncomputable def returnZeta (s : ℝ) : ℝ := s / (1 - Real.exp (-s))

noncomputable def returnQ (u s : ℝ) : ℝ :=
  (1 - Real.exp (-(1 - u) * s)) / ((1 - u) * (1 - Real.exp (-s)))

theorem returnZeta_eq {s : ℝ} (hs : 0 < s) : returnZeta s = s + expTailFactor s := by
  unfold returnZeta
  rw [BoseShape.expTail_eq_decay hs]
  field_simp [(expHead_den_pos hs).ne']
  ring

theorem returnQ_bounds {u s : ℝ} (hu : 0 ≤ u) (hu₁ : u < 1) (hs : 0 < s) :
    1 ≤ returnQ u s ∧ returnQ u s ≤ returnZeta s := by
  let δ := 1 - u
  have hδ : 0 < δ := sub_pos.mpr hu₁
  have hDen := expHead_den_pos hs
  have hConv := convexOn_exp.2 (show (0 : ℝ) ∈ univ from mem_univ _)
    (show -s ∈ univ from mem_univ _) hu hδ.le (by dsimp only [δ]; ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hConv
  constructor
  · apply (le_div_iff₀ (mul_pos hδ hDen)).mpr
    change 1 * (δ * (1 - Real.exp (-s))) ≤ 1 - Real.exp (-δ * s)
    rw [show -δ * s = δ * -s by ring]
    nlinarith only [hConv]
  · unfold returnQ returnZeta
    apply (div_le_div_iff₀ (mul_pos hδ hDen) hDen).mpr
    exact mul_le_mul_of_nonneg_right
      (by nlinarith only [Real.add_one_le_exp (-δ * s)] : 1 - Real.exp (-δ * s) ≤ s * δ) hDen.le |>.trans_eq (by ring)

theorem returnQ_identity {u s : ℝ} (hu₁ : u < 1) (hs : 0 < s) :
    (1 - u) * returnQ u s * Real.exp (-s * u) =
      Real.exp (-s * u) - scaledExpTail s 1 * (1 - Real.exp (-s * u)) := by
  have hE : Real.exp (-(1 - u) * s) * Real.exp (-s * u) = Real.exp (-s) := by
    rw [← Real.exp_add, show -(1 - u) * s + -s * u = -s by ring]
  have hβ := scaledExpTail_bridge hs zero_lt_one
  simp only [mul_one] at hβ
  unfold returnQ
  calc
    _ = ((1 - Real.exp (-(1 - u) * s)) * Real.exp (-s * u)) / (1 - Real.exp (-s)) := by
      field_simp [(sub_pos.mpr hu₁).ne', (expHead_den_pos hs).ne']
    _ = _ := by
      apply (div_eq_iff (expHead_den_pos hs).ne').mpr
      linear_combination -hE - (1 - Real.exp (-s * u)) * hβ

private theorem expTail_small_le {s : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1) :
    expTailFactor s ≤ 1 - s / 3 := by
  have hE := Real.quadratic_le_exp_of_nonneg hs.le
  have hDen := expTail_den_pos hs
  have hc : 0 ≤ 1 - s / 3 := by linarith only [hs₁]
  have hMul := mul_le_mul_of_nonneg_left (show s + s ^ 2 / 2 ≤ Real.exp s - 1 by linarith only [hE]) hc
  have hPoly : s ≤ (1 - s / 3) * (s + s ^ 2 / 2) := by
    have h := mul_le_mul_of_nonneg_right hs₁ (sq_nonneg s)
    nlinarith only [h]
  exact (div_le_iff₀ hDen).mpr (hPoly.trans hMul)

private theorem expTail_two_lt : expTailFactor 2 < 1 / 3 := by
  have hE : (7 : ℝ) < Real.exp 2 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) 6
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith only [h]
  apply (div_lt_iff₀ (expTail_den_pos (by norm_num : (0 : ℝ) < 2))).mpr
  linarith only [hE]

private theorem expTail_mid_le {s : ℝ} (h₁ : 1 ≤ s) (h₂ : s ≤ 2) :
    expTailFactor s ≤ 13 / 15 - (4 / 15) * s := by
  have hE : expTailFactor 1 ≤ 3 / 5 := by
    apply (div_le_iff₀ (expTail_den_pos zero_lt_one)).mpr
    linarith only [Real.exp_one_gt_d9]
  have h := LowScalar.expTail_convex.2
    (show (1 : ℝ) ∈ Ioi 0 by norm_num) (show (2 : ℝ) ∈ Ioi 0 by norm_num)
    (show 0 ≤ 2 - s from sub_nonneg.mpr h₂) (show 0 ≤ s - 1 from sub_nonneg.mpr h₁)
    (show 2 - s + (s - 1) = 1 by ring)
  have hX : (2 - s) • (1 : ℝ) + (s - 1) • (2 : ℝ) = s := by simp only [smul_eq_mul]; ring
  rw [hX] at h
  simp only [smul_eq_mul] at h
  have h₁' := mul_le_mul_of_nonneg_left hE (sub_nonneg.mpr h₂)
  have h₂' := mul_le_mul_of_nonneg_left expTail_two_lt.le (sub_nonneg.mpr h₁)
  nlinarith only [h, h₁', h₂']

private theorem middlePrice_mid_le {s : ℝ} (h₁ : 1 ≤ s) (h₂ : s ≤ 2) :
    2 * Real.exp (-(7 / 8) * s) * max 0 ((719 / 2250) * s - 12353 / 36000) ≤ 14917 / 144000 := by
  let f (x : ℝ) := Real.exp (-(7 / 8) * x) * ((719 / 2250) * x - 12353 / 36000)
  let F (x : ℝ) := Real.exp (-(7 / 8) * x) *
    ((719 / 2250) - (7 / 8) * ((719 / 2250) * x - 12353 / 36000))
  have hd (x : ℝ) : HasDerivAt f (F x) x := by
    have h := hasDerivAt_id x
    convert ((h.const_mul (-(7/8))).exp).mul ((h.const_mul (719/2250)).sub_const (12353/36000)) using 1
    simp only [F, id_eq, mul_one]
    ring
  have hm : MonotoneOn f (Icc 1 2) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun x _ => (hd x).continuousAt.continuousWithinAt
    · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Icc (1 : ℝ) 2 := interior_subset hx
      rw [(hd x).deriv]
      exact mul_nonneg (Real.exp_pos _).le (by linarith only [hx'.2])
  have h := hm ⟨h₁,h₂⟩ (show (2 : ℝ) ∈ Icc 1 2 by norm_num) h₂
  have hE : Real.exp (-(7 / 4)) < 7 / 40 := by
    have he : (40 / 7 : ℝ) < Real.exp (7 / 4) := by
      have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 4) 7
      norm_num [Finset.sum_range_succ, Nat.factorial] at h
      linarith only [h]
    rw [Real.exp_neg, inv_eq_one_div, div_lt_iff₀ (Real.exp_pos _)]
    linarith only [he]
  rcases le_total ((719 / 2250 : ℝ) * s - 12353 / 36000) 0 with hNeg | hPos
  · rw [max_eq_left hNeg, mul_zero]
    norm_num
  · rw [max_eq_right hPos]
    dsimp only [f] at h
    norm_num at h
    rw [show -(7 / 8 * s) = -(7 / 8) * s by ring] at h
    nlinarith only [h, hE]

private theorem middlePrice_high_lt {s : ℝ} :
    2 * Real.exp (-(7 / 8) * s) * max 0 ((313 / 600) * s - 5381 / 7200) < 626 / 4725 := by
  let k : ℝ := 7 / 8
  let a : ℝ := 313 / 600
  let c : ℝ := 5381 / 7200
  let t := k * (s - c / a)
  have hE : Real.exp (- (1 + k * c / a)) < 1 / 9 := by
    have hExp : (9 : ℝ) < Real.exp (9 / 4) := by
      have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 4) 7
      norm_num [Finset.sum_range_succ, Nat.factorial] at h
      linarith only [h]
    have h₁ : Real.exp (-(1 + k * c / a)) ≤ Real.exp (-(9 / 4)) := by
      apply Real.exp_le_exp.mpr
      norm_num [k, c, a]
    rw [Real.exp_neg, inv_eq_one_div, div_lt_iff₀ (Real.exp_pos _)] at ⊢
    have h₂ := Real.exp_le_exp.mp h₁
    have h₃ : (9 / 4 : ℝ) ≤ 1 + k * c / a := by norm_num [k, c, a]
    linarith only [hExp.trans_le (Real.exp_le_exp.mpr h₃)]
  change 2 * Real.exp (-k * s) * max 0 (a * s - c) < _
  rcases le_total (a * s - c) 0 with hNeg | hPos
  · rw [max_eq_left hNeg, mul_zero]
    norm_num
  · rw [max_eq_right hPos]
    have hL : t ≤ Real.exp (t - 1) := by linarith only [Real.add_one_le_exp (t - 1)]
    have hF : a * s - c = (a / k) * t := by dsimp only [t, a, k, c]; ring
    have hR : -k * s + (t - 1) = -(1 + k * c / a) := by dsimp only [t, a, k, c]; ring
    have h := mul_le_mul_of_nonneg_left hL (show 0 ≤ 2 * (a / k) * Real.exp (-k * s) by positivity)
    rw [hF]
    calc
      _ ≤ 2 * (a / k) * Real.exp (-(1 + k * c / a)) := by
        rw [← hR, Real.exp_add]
        nlinarith only [h]
      _ < _ := by norm_num [a,k] at *; linarith only [hE]

noncomputable def balancedRight (u s : ℝ) : ℝ :=
  (1 - middleA u) * s - middleA0 u s

noncomputable def balancedUnitReturn (u m s lam : ℝ) : ℝ :=
  let X := Real.exp (-s)
  let Y := Real.exp (-s * u)
  let B := s * scaledExpTail s 1 * (1 - Y)
  X * (u - Y) * (1 + middleA u * s) - B + m * Y * balancedRight u s +
    lam * ((u - m) * Y - m * u * s * Y + u * B) + (1 - u) - lam * (u - m)

theorem balancedRight_lower {u s : ℝ} (hs : 0 < s) :
    (1 / 2 - middleA u) * s * (1 - Real.exp (-s)) < balancedRight u s := by
  have h := BoseShape.expHeadFactor_gt_one_add_half hs
  have hD := expHead_den_pos hs
  change 1 + s / 2 < s / (1 - Real.exp (-s)) at h
  have hP := (lt_div_iff₀ hD).mp h
  unfold balancedRight middleA0
  nlinarith only [hP]

theorem balancedRight_pos {u s : ℝ} (hs : 0 < s) : 0 < balancedRight u s :=
  (mul_pos (mul_pos (by linarith only [middleA_le u]) hs) (expHead_den_pos hs)).trans (balancedRight_lower hs)

private theorem balancedUnit_at_lowMass {u s lam : ℝ} (hu₁ : u < 1) (hs : 0 < s) :
    balancedUnitReturn u (3 * u - 2) s lam =
      (1 - u) * middleA0 u s - 2 * (1 - u) * lam * (1 - Real.exp (-s * u)) +
        (1 - u) * Real.exp (-s * u) * (balancedRight u s - lam * u * s) * (returnQ u s - 3) := by
  have hq := returnQ_identity hu₁ hs
  have hβ := scaledExpTail_bridge hs zero_lt_one
  simp only [mul_one] at hβ
  unfold balancedUnitReturn balancedRight middleA0
  linear_combination
    -(s * (1 - middleA u + middleA u * Real.exp (-s) - lam * u) - 1 + Real.exp (-s)) * hq +
    (1 + middleA u * s) * (1 - Real.exp (-s * u)) * hβ

private theorem balancedUnit_mono_mass {u m s lam : ℝ} (hu : 0 < u) (hs : 0 < s)
    (hlam : 0 ≤ lam) (hm : 3 * u - 2 ≤ m) :
    balancedUnitReturn u (3 * u - 2) s lam ≤ balancedUnitReturn u m s lam := by
  have hA := (polyA_pos (mul_pos hu hs)).le
  have hEq : polyA (u * s) = 1 - (1 + u * s) * Real.exp (-s * u) := by
    unfold polyA
    rw [show -(u * s) = -s * u by ring]
  have hP := add_nonneg (mul_nonneg (Real.exp_pos (-s * u)).le (balancedRight_pos (u := u) hs).le)
    (mul_nonneg hlam hA)
  have h := mul_nonneg (sub_nonneg.mpr hm) hP
  rw [hEq] at h
  unfold balancedUnitReturn
  linear_combination h

private theorem balancedUnit_anti_lambda {u s lam t : ℝ} (hu : 0 < u) (hu₁ : u < 1) (hs : 0 < s)
    (hlt : lam ≤ t) :
    balancedUnitReturn u (3 * u - 2) s t ≤ balancedUnitReturn u (3 * u - 2) s lam := by
  let Y := Real.exp (-s * u)
  have hq := (returnQ_bounds hu.le hu₁ hs).1
  have hY : Real.exp (u * s) * Y = 1 := by
    dsimp only [Y]
    rw [← Real.exp_add, show u * s + -s * u = 0 by ring, Real.exp_zero]
  have hExp := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (u * s)) (Real.exp_pos (-s * u)).le
  change (u * s + 1) * Y ≤ Real.exp (u * s) * Y at hExp
  rw [hY] at hExp
  have hC : 0 ≤ 2 * (1 - Y) + Y * u * s * (returnQ u s - 3) := by
    have h₁ := mul_nonneg (mul_nonneg (show 0 ≤ Y from (Real.exp_pos _).le) (mul_nonneg hu.le hs.le))
      (sub_nonneg.mpr hq)
    change 0 ≤ Y * (u * s) * (returnQ u s - 1) at h₁
    nlinarith only [h₁, hExp]
  have h := mul_nonneg (sub_nonneg.mpr hlt) (mul_nonneg (sub_nonneg.mpr hu₁.le) hC)
  rw [balancedUnit_at_lowMass hu₁ hs, balancedUnit_at_lowMass hu₁ hs]
  dsimp only [Y] at h
  linear_combination h

theorem balancedUnitReturn_bounds {u m s lam : ℝ} (huL : 7 / 8 ≤ u) (hu₁ : u < 1)
    (hs : 0 < s) (hm : 3 * u - 2 ≤ m) (hlam : 0 ≤ lam) (hlamU : lam ≤ 83 / 300) :
    (199 / 1000) * (1 - u) * (1 - Real.exp (-s)) < balancedUnitReturn u m s lam ∧
      (s ≤ 2 / 3 → (31 / 150) * (1 - u) * (1 - Real.exp (-s)) ≤ balancedUnitReturn u m s lam) := by
  let a := middleA u
  let δ := 1 - u
  let X := Real.exp (-s)
  let Y := Real.exp (-s * u)
  let T : ℝ := 83 / 300
  let β := expTailFactor s
  let ζ := returnZeta s
  let q := returnQ u s
  let h := 1 - a * (1 - X) - T * u
  let g := h * ζ - 1
  let b := (313 / 600) * s + (1819 / 2400) * β - 1
  have hu : 0 < u := by linarith only [huL]
  have hδ : 0 < δ := sub_pos.mpr hu₁
  have hX := Real.exp_pos (-s)
  have hX₁ : 0 < 1 - X := expHead_den_pos hs
  have hXY : X ≤ Y := Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left hu₁.le hs.le])
  have hY : 0 < Y := Real.exp_pos _
  have hYL : Y ≤ Real.exp (-(7 / 8) * s) :=
    Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_right huL hs.le])
  have hY₁ : Y ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [mul_pos hs hu])
  have hA : a ≤ 6 / 25 := middleA_le u
  have hAL : 189 / 800 ≤ a := by
    unfold a middleA
    have h := pow_le_pow_left₀ (sub_nonneg.mpr hu₁.le) (show 1 - u ≤ 1 / 8 by linarith only [huL]) 2
    nlinarith only [h]
  obtain ⟨hq₀, hq₁⟩ := returnQ_bounds hu.le hu₁ hs
  have hζ : ζ = s + β := returnZeta_eq hs
  have hβ : 0 ≤ β := (BoseShape.expTail_bounds hs).1
  have hβX : ζ * X = β := by
    unfold ζ X β returnZeta
    rw [BoseShape.expTail_eq_decay hs]
    ring
  have hh : 29 / 60 ≤ h := by
    have hA' := mul_le_mul_of_nonneg_left (show 1 - X ≤ 1 by linarith only [hX]) (middleA_pos hu hu₁.le).le
    have hT := mul_le_mul_of_nonneg_left hu₁.le (show 0 ≤ T by norm_num [T])
    dsimp only [h,T] at *
    linarith only [hA, hA', hT]
  have hgb : g ≤ b := by
    have he : h * ζ = (1 - T * u - a) * s + (1 - T * u) * β := by
      dsimp only [h]
      linear_combination (1 - a - T * u) * hζ + a * hβX
    have hC₁ : 1 - T * u - a ≤ 313 / 600 := by dsimp only [T]; linarith only [huL, hAL]
    have hC₂ : 1 - T * u ≤ 1819 / 2400 := by dsimp only [T]; linarith only [huL]
    unfold g b
    rw [he]
    exact sub_le_sub_right (add_le_add (mul_le_mul_of_nonneg_right hC₁ hs.le)
      (mul_le_mul_of_nonneg_right hC₂ hβ)) 1
  have hProd : -(2 * Y * max 0 b) ≤ Y * g * (q - 3) := by
    by_cases hq₃ : q ≤ 3
    · have h1 := mul_le_mul_of_nonneg_left (show g ≤ max 0 b from hgb.trans (le_max_right _ _))
        (sub_nonneg.mpr hq₃)
      have h2 := mul_le_mul_of_nonneg_right (show 3 - q ≤ 2 by linarith only [hq₀]) (le_max_left 0 b)
      have h := mul_le_mul_of_nonneg_left (h1.trans h2) hY.le
      nlinarith only [h]
    · have hq₃' : 3 ≤ q := (lt_of_not_ge hq₃).le
      have hg₀ : 0 ≤ g := by
        have hx : (3 : ℝ) ≤ ζ := hq₃'.trans hq₁
        have hh' := mul_le_mul hh hx (by norm_num : (0 : ℝ) ≤ 3) (by linarith only [hh])
        dsimp only [g]
        nlinarith only [hh']
      exact (neg_nonpos.mpr (mul_nonneg (mul_nonneg (by norm_num) hY.le) (le_max_left _ _))).trans
        (mul_nonneg (mul_nonneg hY.le hg₀) (sub_nonneg.mpr hq₃'))
  have hUnit := (balancedUnit_anti_lambda hu hu₁ hs hlamU).trans
    (balancedUnit_mono_mass hu hs hlam hm)
  have hVal : balancedUnitReturn u (3 * u - 2) s T =
      δ * (1 - X) * (1 - a * β - 2 * T * ((1 - Y) / (1 - X)) + Y * g * (q - 3)) := by
    rw [balancedUnit_at_lowMass hu₁ hs]
    have hβE : (1 - X) * β = s * X := by
      rw [← hβX]
      change (1 - X) * ((s / (1 - X)) * X) = s * X
      field_simp [hX₁.ne']
    have hζE : (1 - X) * ζ = s := by
      change (1 - X) * (s / (1 - X)) = s
      field_simp [hX₁.ne']
    have hYE : (1 - X) * ((1 - Y) / (1 - X)) = 1 - Y := by
      rw [mul_comm, div_mul_cancel₀ _ hX₁.ne']
    change δ * (1 - (1 + a * s) * X) - 2 * δ * T * (1 - Y) +
      δ * Y * ((1 - a) * s - (1 - (1 + a * s) * X) - T * u * s) * (q - 3) = _
    unfold g h
    linear_combination
      (δ * a) * hβE + δ * 2 * T * hYE - δ * Y * (q - 3) * (1 - a * (1 - X) - T * u) * hζE
  have hBase : 67 / 150 - (6 / 25) * β ≤ 1 - a * β - 2 * T * ((1 - Y) / (1 - X)) := by
    have hR := (div_le_one hX₁).mpr (sub_le_sub_left hXY 1)
    have hTa := mul_le_mul_of_nonneg_left hR (show 0 ≤ 2 * T by norm_num [T])
    have hB := mul_le_mul_of_nonneg_right hA hβ
    dsimp only [T] at hTa
    nlinarith only [hTa, hB]
  have hLower :
      δ * (1 - X) * (67 / 150 - (6 / 25) * β - 2 * Y * max 0 b) ≤ balancedUnitReturn u m s lam := by
    rw [hVal] at hUnit
    apply le_trans _ hUnit
    apply mul_le_mul_of_nonneg_left _ (mul_pos hδ hX₁).le
    linarith only [hBase,hProd]
  have hSmall (hs₁ : s ≤ 1) (hb : b ≤ 0) :
      (31 / 150 : ℝ) ≤ 67 / 150 - (6 / 25) * β - 2 * Y * max 0 b := by
    rw [max_eq_left hb, mul_zero, sub_zero]
    linarith only [(BoseShape.expTail_bounds hs).2]
  have hSmallB (hs₁ : s ≤ 1) : b ≤ -(581 / 2400) + (1937 / 7200) * s := by
    dsimp only [b,β]
    linarith only [expTail_small_le hs hs₁]
  have hStrong (hs₂ : s ≤ 2 / 3) : (31 / 150 : ℝ) ≤ 67 / 150 - (6 / 25) * β - 2 * Y * max 0 b :=
    hSmall (by linarith only [hs₂]) (by linarith only [hSmallB (by linarith only [hs₂]), hs₂])
  have hWhole : (199 / 1000 : ℝ) < 67 / 150 - (6 / 25) * β - 2 * Y * max 0 b := by
    by_cases hs₁ : s ≤ 1
    · by_cases hb : b ≤ 0
      · exact (by norm_num : (199 / 1000 : ℝ) < 31 / 150).trans_le (hSmall hs₁ hb)
      · have hsL : (8 / 9 : ℝ) < s := by linarith only [lt_of_not_ge hb, hSmallB hs₁]
        have hB : β ≤ 19 / 27 := by
          have h := expTail_small_le hs hs₁
          dsimp only [β]
          linarith only [h, hsL]
        rw [max_eq_right (lt_of_not_ge hb).le]
        have hCost := mul_le_mul_of_nonneg_right hY₁ (lt_of_not_ge hb).le
        linarith only [hCost, hB, hSmallB hs₁, hs₁]
    · have hs₁' : 1 ≤ s := (lt_of_not_ge hs₁).le
      by_cases hs₂ : s ≤ 2
      · have hβ₀ := expTail_mid_le hs₁' hs₂
        have hB : β ≤ 3 / 5 := by dsimp only [β]; linarith only [hβ₀, hs₁']
        have hb : b ≤ (719 / 2250) * s - 12353 / 36000 := by
          dsimp only [b,β]
          linarith only [hβ₀]
        have hP := mul_le_mul (mul_le_mul_of_nonneg_left hYL (by norm_num : (0 : ℝ) ≤ 2))
          (max_le_max le_rfl hb) (le_max_left 0 b) (by positivity)
        linarith only [hB, hP, middlePrice_mid_le hs₁' hs₂]
      · have hs₂' : 2 ≤ s := (lt_of_not_ge hs₂).le
        have hB : β ≤ 1 / 3 := ((strictAntiOn_expTailFactor.antitoneOn
          (show (2 : ℝ) ∈ Ioi 0 by norm_num) hs hs₂').trans expTail_two_lt.le)
        have hb : b ≤ (313 / 600) * s - 5381 / 7200 := by
          dsimp only [b]
          linarith only [hB]
        have hP := mul_le_mul (mul_le_mul_of_nonneg_left hYL (by norm_num : (0 : ℝ) ≤ 2))
          (max_le_max le_rfl hb) (le_max_left 0 b) (by positivity)
        linarith only [hB, hP, middlePrice_high_lt (s := s)]
  constructor
  · have h' := (mul_lt_mul_of_pos_left hWhole (mul_pos hδ hX₁)).trans_le hLower
    nlinarith only [h']
  · intro hs₂
    have h' := (mul_le_mul_of_nonneg_left (hStrong hs₂) (mul_pos hδ hX₁).le).trans hLower
    nlinarith only [h']

end ACS12.GammaMeasure

import ACS12.PureAdjacentUpperTail
import ACS12.PureAdjacentEndpointData
import ACS12.AdjacentCapMass

/-! The complete p = 9/5 cubic source bound, including both infinite tails. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN Set
open scoped BigOperators

private theorem upperTail_lt : powerTail (19 / 5) 7 < 1 / 500 := by
  have h := powerTail_B2 (q := 19 / 5) (m := 7) (by norm_num) (by decide)
  have h1 : (7 : ℝ) ^ (-(14 / 5 : ℝ)) < 431 / 100000 := by
    convert fifth_rpow_upper (k := 14) (b := 7) (x := 431 / 100000)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  have h2 : (7 : ℝ) ^ (-(19 / 5 : ℝ)) < 615 / 1000000 := by
    convert fifth_rpow_upper (k := 19) (b := 7) (x := 615 / 1000000)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  have h3 : (7 : ℝ) ^ (-(24 / 5 : ℝ)) < 88 / 1000000 := by
    convert fifth_rpow_upper (k := 24) (b := 7) (x := 88 / 1000000)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  norm_num only [Nat.cast_ofNat, show (1 : ℝ) - 19 / 5 = -(14 / 5) by norm_num,
    show (19 / 5 : ℝ) + 1 = 24 / 5 by norm_num,
    show (19 / 5 : ℝ) - 1 = 14 / 5 by norm_num] at h
  linarith only [h, h1, h2, h3]

private theorem pureA_upper_summable {τ : ℝ} (hτ : 0 < τ) :
    Summable (fun j : ℕ => τ * purePeanoA (9 / 5) 1 (((j : ℝ) + 1) * τ)) := by
  let p : ℝ := 9 / 5
  have hp : 1 ≤ p := by norm_num [p]
  have hp₂ : p ≤ 2 := by norm_num [p]
  have hθ : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  obtain ⟨_, _, hB⟩ := lawPeanoDensity_quadratic_bound hp hp₂ zero_lt_one hθ zero_lt_one .a
  have hM := lawPeanoDensity_measurable (θ := 0) (h := 1) (zero_lt_one.trans_le hp) zero_lt_one .a
  have hS := (hasSum_signedTail (t := 0) hM hB le_rfl hτ).summable.mul_left τ
  apply hS.congr
  intro j
  change τ * lawPeanoKernel p 1 0 1 .a (0 + τ + (j : ℝ) * τ) = _
  rw [show 0 + τ + (j : ℝ) * τ = ((j : ℝ) + 1) * τ by ring,
    (lawPeanoKernel_zero hp hp₂ zero_lt_one zero_lt_one (by positivity)).1]

private theorem pureAStack_upperPrefix {τ : ℝ} (hτ : 0 < τ) :
    pureAStack (9 / 5) τ ≤ aPrefixUpper τ + (63 / 25) * τ ^ (-(14 / 5 : ℝ)) * powerTail (19 / 5) 7 := by
  let f (j : ℕ) := τ * purePeanoA (9 / 5) 1 (((j : ℝ) + 1) * τ)
  have hS : Summable f := pureA_upper_summable hτ
  have hF : pureAStack (9 / 5) τ = ∑' j : ℕ, f j := by
    unfold pureAStack samplingHead
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    rw [show τ + (j : ℝ) * τ = ((j : ℝ) + 1) * τ by ring]
  have hSplit := hS.sum_add_tsum_nat_add 6
  have hP (j : ℕ) :
      f (j + 6) ≤ ((63 / 25) * τ ^ (-(14 / 5 : ℝ))) * (((7 : ℝ) + j) ^ (-(19 / 5 : ℝ))) := by
    let x := (7 : ℝ) + j
    have hx : 0 < x := by dsimp only [x]; positivity
    have hA := purePeano_quadratic_upper (p := 9 / 5) (by norm_num) (by norm_num) zero_lt_one
      (mul_pos hx hτ) .a
    rw [(lawPeanoKernel_zero (p := 9 / 5) (by norm_num) (by norm_num) zero_lt_one zero_lt_one
      (mul_pos hx hτ)).1] at hA
    have h := mul_le_mul_of_nonneg_left hA hτ.le
    have hE : (((j + 6 : ℕ) : ℝ) + 1) = x := by dsimp only [x]; push_cast; ring
    have ht : τ * τ ^ (-(19 / 5 : ℝ)) = τ ^ (-(14 / 5 : ℝ)) := by
      rw [show -(19 / 5 : ℝ) = -(14 / 5 : ℝ) - 1 by norm_num,
        Real.rpow_sub_one hτ.ne', mul_div_cancel₀ _ hτ.ne']
    change τ * purePeanoA (9 / 5) 1 ((((j + 6 : ℕ) : ℝ) + 1) * τ) ≤ _
    rw [hE]
    refine h.trans_eq ?_
    rw [show -(9 / 5 + 2 : ℝ) = -(19 / 5 : ℝ) by norm_num, Real.mul_rpow hx.le hτ.le]
    linear_combination (63 / 25) * x ^ (-(19 / 5 : ℝ)) * ht
  let c := (63 / 25) * τ ^ (-(14 / 5 : ℝ))
  have hT : Summable (fun j : ℕ => c * (((7 : ℝ) + j) ^ (-(19 / 5 : ℝ)))) := by
    simpa only [Nat.cast_ofNat] using
      (powerTail_summable (q := 19 / 5) (by norm_num) 7).mul_left c
  have h := ((summable_nat_add_iff 6).mpr hS).tsum_le_tsum hP hT
  have hQ : (∑' j : ℕ, c * (((7 : ℝ) + j) ^ (-(19 / 5 : ℝ)))) =
      c * powerTail (19 / 5) 7 := by
    rw [tsum_mul_left]
    rfl
  change (∑' j : ℕ, f (j + 6)) ≤ (∑' j : ℕ, c * (((7 : ℝ) + j) ^ (-(19 / 5 : ℝ)))) at h
  rw [hQ] at h
  have hPfx : (∑ j ∈ Finset.range 6, f j) = aPrefixUpper τ := rfl
  rw [hF, ← hSplit, hPfx]
  exact add_le_add_right h (aPrefixUpper τ)

private theorem upperA_zero_lt : pureAStack (9 / 5) (5 / 7) < 1 := by
  have h := pureAStack_upperPrefix (τ := 5 / 7) (by norm_num)
  have h1 : (5 / 7 : ℝ) ^ (-(14 / 5 : ℝ)) < 13 / 5 := by
    convert fifth_rpow_upper (k := 14) (b := 5 / 7) (x := 13 / 5)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  have h2 := mul_le_mul h1.le upperTail_lt.le
    (powerTail_pos (q := 19 / 5) (by norm_num) (by decide : (0 : ℕ) < 7)).le
    (by norm_num : (0 : ℝ) ≤ 13 / 5)
  nlinarith only [h, h2, aPrefixUpper_zero_lt]

private theorem upperA_edge_lt : pureAStack (9 / 5) (23 / 25) < 641 / 1000 := by
  have h := pureAStack_upperPrefix (τ := 23 / 25) (by norm_num)
  have h1 : (23 / 25 : ℝ) ^ (-(14 / 5 : ℝ)) < 13 / 10 := by
    convert fifth_rpow_upper (k := 14) (b := 23 / 25) (x := 13 / 10)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  have h2 := mul_le_mul h1.le upperTail_lt.le
    (powerTail_pos (q := 19 / 5) (by norm_num) (by decide : (0 : ℕ) < 7)).le
    (by norm_num : (0 : ℝ) ≤ 13 / 10)
  nlinarith only [h, h2, aPrefixUpper_edge_lt]

private theorem upperB_edge_lt : pureBStack (9 / 5) (7 / 8) < 231 / 250 := by
  let f (j : ℕ) := purePeanoB (9 / 5) (7 / 8) ((j : ℝ) + 1)
  have hS : Summable f := pureBStack_samples_summable (by norm_num) (by norm_num) (by norm_num)
  have hSplit := hS.sum_add_tsum_nat_add 6
  have hT (j : ℕ) : f (j + 6) ≤ (63 / 25) * (((7 : ℝ) + j) ^ (-(19 / 5 : ℝ))) := by
    let x := (7 : ℝ) + j
    have hx : 0 < x := by dsimp only [x]; positivity
    have hu : (0 : ℝ) < 7 / 8 := by norm_num
    have h := purePeano_quadratic_upper (p := 9 / 5) (by norm_num) (by norm_num) hu hx .b
    rw [(lawPeanoKernel_zero (p := 9 / 5) (by norm_num) (by norm_num) zero_lt_one hu hx).2] at h
    have hE : (((j + 6 : ℕ) : ℝ) + 1) = x := by dsimp only [x]; push_cast; ring
    dsimp only [f]
    rw [hE]
    norm_num only [show -(9 / 5 + 2 : ℝ) = -(19 / 5 : ℝ) by norm_num] at h
    have h0 := Real.rpow_nonneg hx.le (-(19 / 5 : ℝ))
    linarith only [h, h0]
  have hM : Summable (fun j : ℕ => (63 / 25) * (((7 : ℝ) + j) ^ (-(19 / 5 : ℝ)))) := by
    simpa only [Nat.cast_ofNat] using
      (powerTail_summable (q := 19 / 5) (by norm_num) 7).mul_left (63 / 25)
  have h := ((summable_nat_add_iff 6).mpr hS).tsum_le_tsum hT hM
  rw [tsum_mul_left] at h
  change (∑' j : ℕ, f (j + 6)) ≤ (63 / 25) * powerTail (19 / 5) 7 at h
  have hF : (∑' j : ℕ, f j) < 5131 / 5000 := by
    change bPrefixUpper + ∑' j : ℕ, f (j + 6) = _ at hSplit
    linarith only [h, hSplit, upperTail_lt, bPrefixUpper_edge_lt]
  have hR : (7 / 8 : ℝ) ^ (4 / 5 : ℝ) < 9 / 10 := by
    apply (Real.rpow_lt_rpow_iff (by positivity) (by norm_num) (z := 5) (by norm_num)).mp
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 7 / 8),
      show (4 / 5 : ℝ) * 5 = (4 : ℕ) by norm_num, show (5 : ℝ) = (5 : ℕ) by norm_num,
      Real.rpow_natCast, Real.rpow_natCast]
    norm_num
  have hE : pureBStack (9 / 5) (7 / 8) = (7 / 8 : ℝ) ^ (4 / 5 : ℝ) * ∑' j : ℕ, f j := by
    unfold pureBStack samplingTail f
    simp only [show (9 / 5 : ℝ) - 1 = 4 / 5 by norm_num, Nat.cast_add, Nat.cast_one, mul_one, one_mul, zero_add]
  rw [hE]
  calc
    _ < (7 / 8 : ℝ) ^ (4 / 5 : ℝ) * (5131 / 5000) :=
      mul_lt_mul_of_pos_left hF (by positivity)
    _ ≤ (9 / 10) * (5131 / 5000) := mul_le_mul_of_nonneg_right hR.le (by norm_num)
    _ < _ := by norm_num

theorem pureAdjacentCap_upper_neg {L u : ℝ} (hL : 0 < L) (hu : 0 < u) (hu' : u ≤ 7 / 8) :
    adjacentDiagonal (9 / 5) L 0 u (adjacentCap (9 / 5) u) < 0 := by
  let U : ℝ := 7 / 8
  let p : ℝ := 9 / 5
  let τ := adjacentCap p u / u
  let b := (u / U) ^ 2
  let a := 1 - b
  have hp : 1 ≤ p := by norm_num [p]
  have hp₂ : p ≤ 2 := by norm_num [p]
  have hm := adjacentCap_pos (p := p) le_rfl hu
  have hb : 0 ≤ b := sq_nonneg _
  have ha : 0 ≤ a := by
    have hU : 0 < U := by norm_num [U]
    have h := pow_le_pow_left₀ (div_nonneg hu.le hU.le) ((div_le_one hU).mpr hu') 2
    exact sub_nonneg.mpr (by simpa only [one_pow] using h)
  have hab : a + b = 1 := by dsimp only [a]; ring
  have hτ : τ = a * (5 / 7) + b * (23 / 25) := by
    dsimp only [τ, a, b, adjacentCap, p, U]
    rw [mul_div_cancel_left₀ _ hu.ne']
    ring
  have hA := (pureAStack_convex hp hp₂).2 (show (5 / 7 : ℝ) ∈ Ioi 0 by norm_num)
    (show (23 / 25 : ℝ) ∈ Ioi 0 by norm_num) ha hb hab
  simp only [smul_eq_mul, ← hτ] at hA
  have hB := pureBStack_upperArc hu hu'
  have h1 : pureAStack p (5 / 7) + 1 - (p + 1) * (5 / 7) < 0 := by
    dsimp only [p]
    linarith only [upperA_zero_lt]
  have h2 : pureAStack p (23 / 25) + pureBStack p U + 1 - (p + 1) * (23 / 25) < 0 := by
    dsimp only [p, U]
    linarith only [upperA_edge_lt, upperB_edge_lt]
  have hb' : 0 < b := sq_pos_of_pos (div_pos hu (by norm_num [U]))
  have hNeg := add_neg_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos ha h1.le) (mul_neg_of_pos_of_neg hb' h2)
  have hS : u ^ (p - 1) * adjacentDiagonal p L 0 u (adjacentCap p u) =
      pureAStack p τ + pureBStack p u + 1 - (p + 1) * τ :=
    pureAdjacent_normalized hp hp₂ hL hu hm
  have hE : u ^ (p - 1) * adjacentDiagonal p L 0 u (adjacentCap p u) < 0 := by
    change pureBStack p u ≤ b * pureBStack p U at hB
    have hT : (p + 1) * τ = a * ((p + 1) * (5 / 7)) + b * ((p + 1) * (23 / 25)) := by rw [hτ]; ring
    rw [hT] at hS
    calc
      _ = pureAStack p τ + pureBStack p u + 1 -
          (a * ((p + 1) * (5 / 7)) + b * ((p + 1) * (23 / 25))) := hS
      _ ≤ (a * pureAStack p (5 / 7) + b * pureAStack p (23 / 25)) + b * pureBStack p U + 1 -
          (a * ((p + 1) * (5 / 7)) + b * ((p + 1) * (23 / 25))) :=
        sub_le_sub_right (add_le_add_left (add_le_add hA hB) 1) _
      _ = a * (pureAStack p (5 / 7) + 1 - (p + 1) * (5 / 7)) +
          b * (pureAStack p (23 / 25) + pureBStack p U + 1 - (p + 1) * (23 / 25)) := by
        linear_combination -hab
      _ < 0 := hNeg
  apply lt_of_mul_lt_mul_left _ (Real.rpow_nonneg hu.le (p - 1))
  simpa only [mul_zero] using hE

end ACS12.GammaMeasure

import ACS12.PureNativeExponentGeometry

/-! Whole upper-gap bounds and monotonicity of native curvature in the exponent. -/

namespace ACS12.GammaMeasure

open Set

theorem nativeS_upper_band {u : ℝ} (hu : 3 / 4 ≤ u) (hu' : u ≤ 7 / 8) :
    7 / 10 ≤ nativeS u ∧ nativeS u ≤ 73 / 100 := by
  unfold nativeS
  constructor <;> linarith only [hu, hu']

theorem nativeA_upper_band {u : ℝ} (hu : 3 / 4 ≤ u) (hu' : u ≤ 7 / 8) :
    0 ≤ nativeA u ∧ nativeA u ≤ 13 / 100 := by
  have hu₀ := (by norm_num : (0 : ℝ) < 3 / 4).trans_le hu
  have hu₁ := hu'.trans (by norm_num : (7 / 8 : ℝ) ≤ 1)
  unfold nativeA
  refine ⟨div_nonneg (middleA_pos hu₀ hu₁).le (by positivity), ?_⟩
  apply (div_le_iff₀ (by positivity : 0 < 1 + u)).mpr
  unfold middleA
  nlinarith only [sq_nonneg (u - 35 / 48)]

theorem nativeT_upper_band {u : ℝ} (hu : 3 / 4 ≤ u) (hu' : u ≤ 7 / 8) :
    559 / 1000 < nativeT u ∧ nativeT u < 629 / 1000 := by
  have hL := Real.sum_range_le_log_div (x := 3 / 11) (by norm_num) (by norm_num) 4
  have hU := Real.log_div_le_sum_range_add (x := 7 / 23) (by norm_num) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at hL hU
  unfold nativeT
  have hA : Real.log (7 / 4 : ℝ) ≤ Real.log (1 + u) := Real.log_le_log (by norm_num) (by linarith only [hu])
  have hB : Real.log (1 + u) ≤ Real.log (15 / 8 : ℝ) := Real.log_le_log (by linarith only [hu]) (by linarith only [hu'])
  constructor <;> linarith only [hL, hU, hA, hB]

theorem nativeL_upper_band {u : ℝ} (hu : 3 / 4 ≤ u) (hu' : u ≤ 7 / 8) :
    0 ≤ nativeL u ∧ nativeL u ≤ 288 / 1000 := by
  have hu₀ := (by norm_num : (0 : ℝ) < 3 / 4).trans_le hu
  have hu₁ := hu'.trans (by norm_num : (7 / 8 : ℝ) ≤ 1)
  exact ⟨nativeL_nonneg hu₀ hu₁,
    ((nativeL_mono_rev (show (3 / 4 : ℝ) ∈ Ioi 0 by norm_num) hu₀ hu).trans_lt nativeL_threeFourths_bounds.2).le⟩

theorem pureNativeBandDD_exponent_antitone {u : ℝ} (hu : 3 / 4 ≤ u) (hu' : u ≤ 7 / 8) :
    AntitoneOn (pureNativeBandDD u) (Icc 1 (9 / 5)) := by
  have hu₀ := (by norm_num : (0 : ℝ) < 3 / 4).trans_le hu
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · exact fun p _ => (pureNativeBandDD_deriv (p := p) hu₀).continuousAt.continuousWithinAt
  · exact fun p _ => (pureNativeBandDD_deriv (p := p) hu₀).differentiableAt.differentiableWithinAt
  intro p hp
  have hp' : p ∈ Icc (1 : ℝ) (9 / 5) := interior_subset hp
  rw [(pureNativeBandDD_deriv (p := p) hu₀).deriv]
  let τ := adjacentRatio u p
  let s := nativeS u
  let l := nativeL u
  let A := nativeA u
  let t := nativeT u
  let q := τ * l
  let Y := p * s - 1
  obtain ⟨hs, hs'⟩ := nativeS_upper_band hu hu'
  obtain ⟨hA, hA'⟩ := nativeA_upper_band hu hu'
  obtain ⟨ht, _⟩ := nativeT_upper_band hu hu'
  obtain ⟨hl, hl'⟩ := nativeL_upper_band hu hu'
  obtain ⟨hq, hq'⟩ := nativeCapLog_upper_band hp'.1 hp'.2 hu hu'
  change 0 ≤ l at hl
  change l ≤ 288 / 1000 at hl'
  change 1228 / 10000 < q at hq
  change q < 284 / 1000 at hq'
  have hτ := adjacentRatio_pos (u := u) hp'.2
  have hY : -(3 / 10) ≤ Y := by
    have h := mul_le_mul hp'.1 hs (by norm_num) (zero_le_one.trans hp'.1)
    dsimp only [Y, s]
    linarith only [h]
  have hY' := mul_le_mul_of_nonneg_right hY hl
  have hC := mul_le_mul_of_nonneg_right hY' (show 0 ≤ 9 / 20 - q by linarith only [hq'])
  have hD := mul_le_mul hl' (show 9 / 20 - q ≤ 3272 / 10000 by linarith only [hq])
    (show 0 ≤ 9 / 20 - q by linarith only [hq']) (by norm_num : (0 : ℝ) ≤ 288 / 1000)
  have hS := mul_le_mul (show (7 / 10 : ℝ) ≤ s from hs)
    (show (48 / 1000 : ℝ) ≤ 9 / 10 - 3 * q by linarith only [hq'])
    (by norm_num) (show 0 ≤ s by linarith only [show 7 / 10 ≤ s from hs])
  have hUnshifted : 0 ≤ s * (9 / 10 - 3 * q) + Y * l * (9 / 20 - q) := by
    nlinarith only [hC, hD, hS]
  have hShift1 : 0 ≤ (1 + p * A) * t ^ 2 - 2 * A * t := by
    have hTA := nativeT_gt_twoA hu₀
    change 2 * A < t at hTA
    have ht₀ : 0 ≤ t := (by norm_num : (0 : ℝ) ≤ 559 / 1000).trans ht.le
    have h₁ := mul_nonneg (mul_nonneg (zero_le_one.trans hp'.1) hA) (sq_nonneg t)
    have h₂ := mul_le_mul_of_nonneg_right hTA.le ht₀
    nlinarith only [h₁, h₂]
  have hShift2 : 0 ≤ ((1 + p * A) * t - 3 * A) * t ^ 2 := by
    have ht₀ : 0 ≤ t := (by norm_num : (0 : ℝ) ≤ 559 / 1000).trans ht.le
    have h₁ := mul_nonneg (mul_nonneg (zero_le_one.trans hp'.1) hA) ht₀
    apply mul_nonneg _ (sq_nonneg t)
    change 559 / 1000 < t at ht
    change A ≤ 13 / 100 at hA'
    nlinarith only [h₁, ht, hA']
  have hN := mul_nonneg (mul_nonneg (Real.rpow_nonneg hu₀.le (-p)) hl) hUnshifted
  have hR := mul_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ 1 + u) (-p))
    (add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 20) hShift1) (mul_nonneg hτ.le hShift2))
  dsimp only [τ, s, l, A, t, q, Y] at hN hR
  unfold pureNativeG3 pureNativeG2
  nlinarith only [hN, hR]

end ACS12.GammaMeasure

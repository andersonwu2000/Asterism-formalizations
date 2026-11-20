import ACS12.PureNativeUpperMotion

/-! Directed spatial curvature prices for the complete upper native value. -/

namespace ACS12.GammaMeasure

open Set

private theorem upper_ratio_bounds {u : ℝ} (hu : 3 / 4 ≤ u) (hu' : u ≤ 7 / 8) :
    865 / 1000 ≤ upperNativeRatio u ∧ upperNativeRatio u ≤ 23 / 25 ∧
      0 ≤ upperNativeRatioD u ∧ upperNativeRatioD u ≤ 471 / 1000 := by
  have h₀ : 0 ≤ u := (by norm_num : (0 : ℝ) ≤ 3 / 4).trans hu
  have h₁ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 4) hu 2
  have h₂ := pow_le_pow_left₀ h₀ hu' 2
  unfold upperNativeRatio upperNativeRatioD adjacentRatio
  exact ⟨by linarith only [h₁], by linarith only [h₂], by positivity, by linarith only [hu']⟩

private theorem upper_Y_bounds {u : ℝ} (hu : 3 / 4 ≤ u) (hu' : u ≤ 7 / 8) :
    0 ≤ upperNativeY u ∧ upperNativeY u ≤ 314 / 1000 := by
  obtain ⟨hS, hS'⟩ := nativeS_upper_band hu hu'
  unfold upperNativeY
  exact ⟨by linarith only [hS], by linarith only [hS']⟩

private theorem upper_QD_le {u : ℝ} (hu : 3 / 4 ≤ u) (hu' : u ≤ 7 / 8) :
    upperNativeQD u ≤ -(85 / 100) := by
  have hu₀ := (by norm_num : (0 : ℝ) < 3 / 4).trans_le hu
  obtain ⟨hR, _, _, hD⟩ := upper_ratio_bounds hu hu'
  obtain ⟨hL, hL'⟩ := nativeL_upper_band hu hu'
  have h₁ := mul_le_mul hD hL' hL (by norm_num : (0 : ℝ) ≤ 471 / 1000)
  have h₂' : (988 / 1000 : ℝ) ≤ upperNativeRatio u / u := by
    apply (le_div_iff₀ hu₀).mpr
    linarith only [hR, hu']
  unfold upperNativeQD
  linarith only [h₁, h₂']

private theorem upper_H_lower {u : ℝ} (hu : 3 / 4 ≤ u) (hu' : u ≤ 7 / 8) :
    -(56 / 1000) ≤ upperNativeH u := by
  let s := nativeS u
  let Y := upperNativeY u
  let l := nativeL u
  let q := upperNativeQ u
  obtain ⟨hs, hs'⟩ := nativeS_upper_band hu hu'
  obtain ⟨hY, hY'⟩ := upper_Y_bounds hu hu'
  obtain ⟨hl, hl'⟩ := nativeL_upper_band hu hu'
  obtain ⟨hq, hq'⟩ := nativeCapLog_upper_band (by norm_num : (1 : ℝ) ≤ 9 / 5) le_rfl hu hu'
  change 1228 / 10000 < q at hq
  change q < 284 / 1000 at hq'
  have h₁ := mul_le_mul_of_nonneg_left (show -(544 / 10000 : ℝ) ≤ 2 * q - 3 / 10 by linarith only [hq])
    (show 0 ≤ s by linarith only [hs])
  have h₂ := mul_le_mul_of_nonpos_left hs' (show -(544 / 10000 : ℝ) ≤ 0 by norm_num)
  have h₃ := mul_le_mul hY' hl' hl (by norm_num : (0 : ℝ) ≤ 314 / 1000)
  have h₄ := mul_le_mul_of_nonpos_right h₃ (show q - 3 / 10 ≤ 0 by linarith only [hq'])
  have h₅ := mul_le_mul_of_nonneg_left (show -(1772 / 10000 : ℝ) ≤ q - 3 / 10 by linarith only [hq])
    (show 0 ≤ (314 / 1000 : ℝ) * (288 / 1000) by norm_num)
  change -(56 / 1000) ≤ s * (2 * q - 3 / 10) + Y * l * (q - 3 / 10)
  dsimp only [s, Y, l] at *
  nlinarith only [h₁, h₂, h₄, h₅]

private theorem upper_HD_le {u : ℝ} (hu : 3 / 4 ≤ u) (hu' : u ≤ 7 / 8) :
    upperNativeHD u ≤ -(105 / 100) := by
  let q := upperNativeQ u
  let s := nativeS u
  let Y := upperNativeY u
  let l := nativeL u
  have hu₀ := (by norm_num : (0 : ℝ) < 3 / 4).trans_le hu
  obtain ⟨hs, _⟩ := nativeS_upper_band hu hu'
  obtain ⟨hY, hY'⟩ := upper_Y_bounds hu hu'
  obtain ⟨hl, _⟩ := nativeL_upper_band hu hu'
  obtain ⟨hq, hq'⟩ := nativeCapLog_upper_band (by norm_num : (1 : ℝ) ≤ 9 / 5) le_rfl hu hu'
  change 1228 / 10000 < q at hq
  change q < 284 / 1000 at hq'
  have h₁ : (6 / 25) * (2 * q - 3 / 10) ≤ 6432 / 100000 := by linarith only [hq']
  have h₂ : (54 / 125) * l * (q - 3 / 10) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) hl) (by linarith only [hq'])
  have hYdiv : Y / u ≤ (314 / 1000) / (3 / 4) :=
    (div_le_div_of_nonneg_right hY' hu₀.le).trans
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hu)
  have h₃ : -(Y / u) * (q - 3 / 10) ≤ 742 / 10000 := by
    have h := mul_le_mul hYdiv (show 3 / 10 - q ≤ 1772 / 10000 by linarith only [hq])
      (show 0 ≤ 3 / 10 - q by linarith only [hq']) (by norm_num : (0 : ℝ) ≤ (314 / 1000) / (3 / 4))
    nlinarith only [h]
  have h₄ : upperNativeQD u * (2 * s + Y * l) ≤ -(119 / 100) := by
    have hB : (14 / 10 : ℝ) ≤ 2 * s + Y * l := by
      change 7 / 10 ≤ s at hs
      linarith only [hs, mul_nonneg hY hl]
    have hQd := upper_QD_le hu hu'
    have hM := mul_le_mul_of_nonneg_right hQd (show 0 ≤ 2 * s + Y * l by linarith only [hB])
    have hN := mul_le_mul_of_nonpos_left hB (show -(85 / 100 : ℝ) ≤ 0 by norm_num)
    linarith only [hM, hN]
  change (6 / 25) * (2 * q - 3 / 10) + (54 / 125) * l * (q - 3 / 10) -
    (Y / u) * (q - 3 / 10) + upperNativeQD u * (2 * s + Y * l) ≤ _
  linarith only [h₁, h₂, h₃, h₄]

private theorem upper_unshiftedD_le {u : ℝ} (hu : 3 / 4 ≤ u) (hu' : u ≤ 7 / 8) :
    upperNativeUnshiftedD u ≤ -(9 / 10) := by
  have hu₀ := (by norm_num : (0 : ℝ) < 3 / 4).trans_le hu
  have hu₁ := hu'.trans (by norm_num : (7 / 8 : ℝ) ≤ 1)
  have hH := upper_H_lower hu hu'
  have hHd := upper_HD_le hu hu'
  have hN : -(9 / 5) * upperNativeH u / u ≤ (9 / 5) * (56 / 1000) / (3 / 4) := by
    have hP : -(9 / 5) * upperNativeH u ≤ (9 / 5) * (56 / 1000) := by linarith only [hH]
    exact (div_le_div_of_nonneg_right hP hu₀.le).trans
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hu)
  have hP : 1 ≤ u ^ (-(9 : ℝ) / 5) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu₀ hu₁ (by norm_num)
  have hB : upperNativeHD u - (9 / 5) * upperNativeH u / u ≤ -(9 / 10) := by
    have hE : -(9 / 5) * upperNativeH u / u = -((9 / 5) * upperNativeH u / u) := by ring
    rw [hE] at hN
    linarith only [hN, hHd]
  unfold upperNativeUnshiftedD
  exact (mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg hu₀.le _)).trans
    (by
      have h := mul_le_mul_of_nonpos_right hP (show -(9 / 10 : ℝ) ≤ 0 by norm_num)
      simpa only [one_mul] using h)

private theorem nativeAD_bounds {u : ℝ} (hu : 3 / 4 ≤ u) (hu' : u ≤ 7 / 8) :
    -(41 / 1000) ≤ nativeAD u ∧ nativeAD u ≤ 0 := by
  have hu₀ : 0 ≤ u := (by norm_num : (0 : ℝ) ≤ 3 / 4).trans hu
  have hY : 0 < 1 + u := by positivity
  have hS₁ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 4) hu 2
  have hS₂ := pow_le_pow_left₀ hu₀ hu' 2
  have hS₃ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 4)
    (show (7 / 4 : ℝ) ≤ 1 + u by linarith only [hu]) 2
  unfold nativeAD
  constructor
  · apply (le_div_iff₀ (sq_pos_of_pos hY)).mpr
    nlinarith only [hS₂, hS₃, hu']
  · exact div_nonpos_of_nonpos_of_nonneg (by nlinarith only [hS₁, hu]) (sq_nonneg _)

private theorem upper_shiftedD_le {u : ℝ} (hu : 3 / 4 ≤ u) (hu' : u ≤ 7 / 8) :
    upperNativeShiftedD u ≤ 1 / 2 := by
  let A := nativeA u
  let t := nativeT u
  let y := 1 + u
  let R := upperNativeRatio u
  let K := 1 + (9 / 5) * A
  have hu₀ := (by norm_num : (0 : ℝ) < 3 / 4).trans_le hu
  have hy : 0 < y := by dsimp only [y]; positivity
  have hy' : 7 / 4 ≤ y := by dsimp only [y]; linarith only [hu]
  have hInv : 1 / y ≤ 4 / 7 := (div_le_iff₀ hy).mpr (by linarith only [hy'])
  obtain ⟨hA, hA'⟩ := nativeA_upper_band hu hu'
  obtain ⟨ht, ht'⟩ := nativeT_upper_band hu hu'
  obtain ⟨hR, hR', hRD, hRD'⟩ := upper_ratio_bounds hu hu'
  obtain ⟨hD, hD'⟩ := nativeAD_bounds hu hu'
  change 559 / 1000 < t at ht
  change t < 629 / 1000 at ht'
  have ht₀ : 0 ≤ t := (by norm_num : (0 : ℝ) ≤ 559 / 1000).trans ht.le
  have hK : 1 ≤ K := by dsimp only [K, A]; linarith only [hA]
  have hK' : K ≤ 31 / 25 := by dsimp only [K, A]; linarith only [hA']
  have hE : 0 ≤ upperNativeE u := by
    have h := mul_le_mul_of_nonneg_right hK (sq_nonneg t)
    have h' := mul_le_mul_of_nonneg_right (nativeT_gt_twoA hu₀).le ht₀
    change 0 ≤ K * t ^ 2 - 2 * A * t
    nlinarith only [h, h']
  have hE' : upperNativeE u ≤ 1 / 2 := by
    have h := mul_le_mul hK' (pow_le_pow_left₀ ht₀ ht'.le 2) (sq_nonneg t) (by norm_num)
    change K * t ^ 2 - 2 * A * t ≤ 1 / 2
    nlinarith only [h, mul_nonneg (show 0 ≤ A from hA) ht₀]
  have hF : 0 ≤ upperNativeF u := by
    have h := mul_le_mul_of_nonneg_right hK ht₀
    have h' := nativeT_gt_twoA hu₀
    change 0 ≤ K * t - A
    change 2 * A < t at h'
    linarith only [h, h', (show 0 ≤ A from hA)]
  have hEd : upperNativeED u ≤ 95 / 100 := by
    have h₁ := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ (9 / 5) * t ^ 2 by positivity) hD'
    have h₂ := mul_le_mul_of_nonpos_left hD (show -(2 * t) ≤ 0 by linarith only [ht₀])
    have h₃ := mul_le_mul_of_nonneg_left ht'.le (show 0 ≤ (2 : ℝ) * (41 / 1000) by norm_num)
    have hM : K * t ≤ (31 / 25) * (629 / 1000) := mul_le_mul hK' ht'.le ht₀ (by norm_num)
    have hN : (2 * K * t - 2 * A) / y ≤ (2 * (31 / 25) * (629 / 1000)) * (4 / 7) := by
      have hL : 2 * K * t - 2 * A ≤ 2 * (31 / 25) * (629 / 1000) := by
        linarith only [hM, (show 0 ≤ A from hA)]
      exact (div_le_div_of_nonneg_right hL hy.le).trans
        (by
          have h := mul_le_mul_of_nonneg_left hInv (show 0 ≤ (2 : ℝ) * (31 / 25) * (629 / 1000) by norm_num)
          nlinarith only [h, show (2 * (31 / 25) * (629 / 1000)) / y =
            (2 * (31 / 25) * (629 / 1000)) * (1 / y) by ring])
    change ((9 / 5) * t ^ 2 - 2 * t) * nativeAD u + (2 * K * t - 2 * A) / y ≤ _
    nlinarith only [h₁, h₂, h₃, hN]
  have hFd : upperNativeFD u ≤ 71 / 100 := by
    have h₁ := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ (9 / 5) * t - 1 by linarith only [ht]) hD'
    have h₂ : K / y ≤ (31 / 25) * (4 / 7) := by
      calc
        _ ≤ (31 / 25) / y := div_le_div_of_nonneg_right hK' hy.le
        _ = (31 / 25) * (1 / y) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hInv (by norm_num)
    change ((9 / 5) * t - 1) * nativeAD u + K / y ≤ _
    linarith only [h₁, h₂]
  have hB₁ := mul_le_mul hRD' hE' hE (by norm_num : (0 : ℝ) ≤ 471 / 1000)
  have hB₂ := (mul_le_mul_of_nonneg_left hEd (show 0 ≤ R by linarith only [hR])).trans
    (mul_le_mul_of_nonneg_right hR' (by norm_num : (0 : ℝ) ≤ 95 / 100))
  have hB₃ := mul_le_mul_of_nonneg_left hFd (by norm_num : (0 : ℝ) ≤ 3 / 10)
  have hB₄ : 0 ≤ (9 / 5) * (R * upperNativeE u + (3 / 10) * upperNativeF u) / y := by
    have hR₀ : 0 ≤ R := by linarith only [hR]
    positivity
  have hB : upperNativeRatioD u * upperNativeE u + R * upperNativeED u + (3 / 10) * upperNativeFD u -
      (9 / 5) * (R * upperNativeE u + (3 / 10) * upperNativeF u) / y ≤ 133 / 100 := by
    linarith only [hB₁, hB₂, hB₃, hB₄]
  have hPow : y ^ (-(9 : ℝ) / 5) ≤ 366 / 1000 := by
    have h := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 7 / 4) hy' (by norm_num : -(9 : ℝ) / 5 ≤ 0)
    exact h.trans (fifth_rpow_upper (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
  unfold upperNativeShiftedD
  change y ^ (-(9 : ℝ) / 5) * _ ≤ _
  exact ((mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg hy.le _)).trans
    (mul_le_mul_of_nonneg_right hPow (by norm_num : (0 : ℝ) ≤ 133 / 100))).trans (by norm_num)

theorem pureNativeBandDD_upper_spatial_antitone :
    AntitoneOn (fun u => pureNativeBandDD u (9 / 5)) (Icc (3 / 4) (7 / 8)) := by
  have hD (u : ℝ) (hu : u ∈ Icc (3 / 4 : ℝ) (7 / 8)) :
      HasDerivAt (fun x => pureNativeBandDD x (9 / 5)) (upperNativeUnshiftedD u + upperNativeShiftedD u) u := by
    have hu₀ := (by norm_num : (0 : ℝ) < 3 / 4).trans_le hu.1
    simpa only [pureNativeBandDD_upper_eq, Pi.add_apply] using
      (upperNativeUnshifted_deriv hu₀).add (upperNativeShifted_deriv hu₀)
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · exact fun u hu => (hD u hu).continuousAt.continuousWithinAt
  · exact fun u hu => (hD u (interior_subset hu)).differentiableAt.differentiableWithinAt
  · intro u hu
    have hU : u ∈ Icc (3 / 4 : ℝ) (7 / 8) := interior_subset hu
    rw [(hD u hU).deriv]
    linarith only [upper_unshiftedD_le hU.1 hU.2, upper_shiftedD_le hU.1 hU.2]

end ACS12.GammaMeasure

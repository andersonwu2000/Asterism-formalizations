import ACS12.JointFarMomentPrice
import ACS12.JointFarLogGuards

/-! Uniform W42 curvature for the licensed adjacent source envelope. -/
namespace ACS12.GammaMeasure

private theorem adjacentRight_second_ge {p : ℝ} (hP : p ≤ 9 / 5) :
    -(284 / 1000 : ℝ) ≤ farPolyPowerDD 0 (-3 / 4) (1 / 8) (7 / 8) p := by
  let J := -Real.log (7 / 8)
  let r := (7 / 8 : ℝ) ^ (-p)
  have hJ : J = Real.log (8 / 7) := by
    unfold J
    rw [← Real.log_inv,show (7 / 8 : ℝ)⁻¹ = 8 / 7 by norm_num]
  have hJL : 0 ≤ J := by rw [hJ]; linarith only [farLog_eight_sevenths.1]
  have hJU : J ≤ 1336 / 10000 := by rw [hJ]; exact farLog_eight_sevenths.2.le
  have hJ₂ := pow_le_pow_left₀ hJL hJU 2
  have hr : r ≤ 1272 / 1000 := by
    have h := Real.rpow_le_rpow_of_exponent_ge (by norm_num : 0 < (7 / 8 : ℝ))
      (by norm_num : (7 / 8 : ℝ) ≤ 1) (neg_le_neg hP)
    exact h.trans (by simpa only [neg_div] using
      (fifth_rpow_upper (b := 7 / 8) (x := 1272 / 1000) (k := 9) (by norm_num) (by norm_num) (by norm_num)).le)
  have hA : -(49 / 40 : ℝ) ≤ 1 / 8 - 3 * p / 4 := by linarith only [hP]
  have hA' := (mul_le_mul_of_nonpos_left hJ₂ (by norm_num : -(49 / 40 : ℝ) ≤ 0)).trans
    (mul_le_mul_of_nonneg_right hA (sq_nonneg J))
  have hB : -(223 / 1000 : ℝ) ≤ -(3 / 2) * J + (1 / 8 - 3 * p / 4) * J ^ 2 := by
    linarith only [hJU,hA']
  have hC := (mul_le_mul_of_nonpos_left hr (by norm_num : -(223 / 1000 : ℝ) ≤ 0)).trans
    (mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 8) _))
  have hE : farPolyPowerDD 0 (-3 / 4) (1 / 8) (7 / 8) p =
      (-(3 / 2) * J + (1 / 8 - 3 * p / 4) * J ^ 2) * r := by unfold farPolyPowerDD J r; ring
  rw [hE]
  exact (by norm_num : -(284 / 1000 : ℝ) ≤ -(223 / 1000) * (1272 / 1000)).trans hC

theorem farAdjacent_second_gt {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    -(324 / 1000 : ℝ) < farAdjacentJet 2 p := by
  let L := -Real.log (3 / 4)
  let t := p - 1
  let s := (3 / 4 : ℝ) ^ (-t)
  let Z := pureZ p
  let Z' := pureZPrime p
  let Z'' := pureZSecond p
  have ht : 0 ≤ t := sub_nonneg.mpr hp
  have htU : t ≤ 4 / 5 := by unfold t; linarith only [hP]
  have hL : L = Real.log (4 / 3) := by
    unfold L
    rw [← Real.log_inv,show (3 / 4 : ℝ)⁻¹ = 4 / 3 by norm_num]
  have hLL : (287 / 1000 : ℝ) ≤ L := by rw [hL]; exact farLog_four_thirds.1.le
  have hLU : L ≤ 288 / 1000 := by rw [hL]; exact farLog_four_thirds.2.le
  have hL₀ : 0 ≤ L := (by norm_num : (0 : ℝ) ≤ 287 / 1000).trans hLL
  have hL₂L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 287 / 1000) hLL 2
  have hL₂U := pow_le_pow_left₀ hL₀ hLU 2
  have hsL : 1 + (287 / 1000) * t ≤ s := by
    have hE : s = Real.exp (L * t) := by
      unfold s L
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3 / 4)]
      congr 1
      ring
    rw [hE]
    linarith only [Real.add_one_le_exp (L * t),mul_le_mul_of_nonneg_right hLL ht]
  have hs₁ : 1 ≤ s := (le_add_of_nonneg_right (mul_nonneg (by norm_num) ht)).trans hsL
  have hs₀ := zero_le_one.trans hs₁
  have hsU : s ≤ 12588 / 10000 := by
    change (3 / 4 : ℝ) ^ (-(p - 1)) ≤ _
    rw [show -(p - 1) = 1 - p by ring]
    exact (jointLowerMassScale_le hP).le
  have hZ₂ := pureZ_second_bounds hp hP
  change (37 / 500 : ℝ) < Z'' ∧ Z'' ≤ 1 / 8 at hZ₂
  have hZ₂₀ : 0 ≤ Z'' := (by norm_num : (0 : ℝ) ≤ 37 / 500).trans hZ₂.1.le
  have hA : -(32375 / 1000000 : ℝ) ≤ (1 - s) * Z'' := by
    have h := mul_le_mul (show s - 1 ≤ 2588 / 10000 by linarith only [hsU]) hZ₂.2 hZ₂₀
      (by norm_num : (0 : ℝ) ≤ 2588 / 10000)
    linarith only [h]
  have hD : (292 / 1000 : ℝ) - t / 8 ≤ 1 - Z' := by
    unfold Z' t
    linarith only [(pureZPrime_bounds hp hP).2]
  have hD₀ : 0 ≤ (292 / 1000 : ℝ) - t / 8 := by linarith only [htU]
  have hB : (1354 / 10000 : ℝ) ≤ 2 * L * s * (1 - Z') := by
    have h := mul_le_mul hsL hD hD₀ hs₀
    have h' := mul_le_mul hLL h (mul_nonneg (by positivity : 0 ≤ 1 + (287 / 1000) * t) hD₀) hL₀
    have hPoly : (1354 / 10000 : ℝ) ≤
        2 * (287 / 1000) * ((1 + (287 / 1000) * t) * (292 / 1000 - t / 8)) := by
      nlinarith only [htU,mul_nonneg ht (sub_nonneg.mpr htU)]
    nlinarith only [h',hPoly]
  have hC : (292 / 10000 : ℝ) ≤ s * L ^ 2 * (p + 1 - Z + 1063 / 1296000) := by
    have hV : (355 / 1000 : ℝ) ≤ p + 1 - Z + 1063 / 1296000 := by
      unfold Z
      linarith only [hp,(pureZ_band_bounds hp hP).2]
    have hS := mul_le_mul hs₁ hL₂L (by norm_num : (0 : ℝ) ≤ (287 / 1000) ^ 2) hs₀
    have h := mul_le_mul hS hV (by norm_num : (0 : ℝ) ≤ 355 / 1000) (by positivity)
    exact (by norm_num : (292 / 10000 : ℝ) ≤ 1 * (287 / 1000) ^ 2 * (355 / 1000)).trans h
  have hM₂₀ := farM2Jet_zero_nonneg hp
  have hM₂₁ : -(12 / 100 : ℝ) ≤ farM2Jet 1 p := by
    change _ ≤ pureQPrime p - (2 * p + 1)
    linarith only [(pureQPrime_bounds hp hP).1,hP]
  have hM₂₂ : -(4 / 10 : ℝ) ≤ farM2Jet 2 p := by
    change _ ≤ pureQSecond p - 2
    linarith only [pureQSecond_gt hp hP]
  have hD₂ : -(941 / 10000 : ℝ) ≤ (13 * s / 72 + 1 / 128) * farM2Jet 2 p := by
    have hU : 13 * s / 72 + 1 / 128 ≤ 2352 / 10000 := by linarith only [hsU]
    have h := (mul_le_mul_of_nonpos_right hU (by norm_num : -(4 / 10 : ℝ) ≤ 0)).trans
      (mul_le_mul_of_nonneg_left hM₂₂ (by positivity : 0 ≤ 13 * s / 72 + 1 / 128))
    exact (by norm_num : -(941 / 10000 : ℝ) ≤ (2352 / 10000) * -(4 / 10)).trans h
  have hD₁ : -(1584 / 100000 : ℝ) ≤ (26 * s * L / 72) * farM2Jet 1 p := by
    have hSL := mul_le_mul hsU hLU hL₀ (by norm_num : (0 : ℝ) ≤ 12588 / 10000)
    have hU : 26 * s * L / 72 ≤ 132 / 1000 := by linarith only [hSL]
    have h := (mul_le_mul_of_nonpos_right hU (by norm_num : -(12 / 100 : ℝ) ≤ 0)).trans
      (mul_le_mul_of_nonneg_left hM₂₁ (by positivity : 0 ≤ 26 * s * L / 72))
    exact (by norm_num : -(1584 / 100000 : ℝ) ≤ (132 / 1000) * -(12 / 100)).trans h
  have hD₀' : 0 ≤ (13 * s * L ^ 2 / 72) * farM2Jet 0 p := by positivity
  obtain ⟨hM₀,hM₁,hM₂⟩ := farM3Jet_bounds hp hP
  have hE : (s / 72) * (farM3Jet 2 p + 2 * L * farM3Jet 1 p + L ^ 2 * farM3Jet 0 p) ≤ 60 / 1000 := by
    have h₁ := (mul_le_mul_of_nonneg_left hM₁ (by positivity : 0 ≤ 2 * L)).trans
      (mul_le_mul_of_nonneg_right (show 2 * L ≤ 2 * (288 / 1000) by linarith only [hLU])
        (by norm_num : (0 : ℝ) ≤ 19 / 10))
    have h₀ := (mul_le_mul_of_nonneg_left hM₀ (sq_nonneg L)).trans
      (mul_le_mul_of_nonneg_right hL₂U (by norm_num : (0 : ℝ) ≤ 8 / 5))
    let K : ℝ := 11 / 5 + 2 * (288 / 1000) * (19 / 10) + (288 / 1000) ^ 2 * (8 / 5)
    have hK : farM3Jet 2 p + 2 * L * farM3Jet 1 p + L ^ 2 * farM3Jet 0 p ≤ K := by
      unfold K
      linarith only [h₁,h₀,hM₂]
    exact ((mul_le_mul_of_nonneg_left hK (by positivity)).trans
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hsU (by norm_num)) (by norm_num [K]))).trans
        (by norm_num [K])
  rw [farAdjacentJet_second]
  change _ < (1 - s) * Z'' + 2 * L * s * (1 - Z') + s * L ^ 2 * (p + 1 - Z + 1063 / 1296000) +
        (13 * s / 72 + 1 / 128) * farM2Jet 2 p + (26 * s * L / 72) * farM2Jet 1 p +
        (13 * s * L ^ 2 / 72) * farM2Jet 0 p -
        (s / 72) * (farM3Jet 2 p + 2 * L * farM3Jet 1 p + L ^ 2 * farM3Jet 0 p) +
        farPolyPowerDD 0 (-3 / 4) (1 / 8) (7 / 8) p
  linarith only [hA,hB,hC,hD₂,hD₁,hD₀',hE,adjacentRight_second_ge hP]

end ACS12.GammaMeasure

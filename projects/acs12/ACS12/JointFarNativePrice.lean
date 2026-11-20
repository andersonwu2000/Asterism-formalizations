import ACS12.JointFarNativeJet
import ACS12.JointFarIntegralPrice

/-! Directed uniform curvature for the finite-power terms of the native envelope. -/
namespace ACS12.GammaMeasure

private theorem farBasePow_le_inv {x p : ℝ} (hx : 1 < x) (hp : 1 ≤ p) :
    x ^ (-p) ≤ x⁻¹ := by
  rw [← Real.rpow_neg_one]
  exact (Real.rpow_le_rpow_left_iff hx).mpr (by linarith only [hp])

private theorem farBasePow_ge_fifth {x p v : ℝ} (hx : 1 < x) (hpP : p ≤ 9 / 5) (hv : 0 ≤ v)
    (h : v ^ 5 < (x ^ (9 : ℕ))⁻¹) : v < x ^ (-p) :=
  (far_fifth_rpow_lower (k := 9) (zero_lt_one.trans hx) hv h).trans_le
    ((Real.rpow_le_rpow_left_iff hx).mpr (by linarith only [hpP]))

private theorem farNative_at_u_second {p : ℝ} (hp : 1 ≤ p) (hpP : p ≤ 9 / 5) :
    (308 / 1000 : ℝ) <
      farPolyPowerDD 0 (73 / 100) (-1) (7 / 8) p + farPolyPowerDD 0 (63 / 500) 1 (15 / 8) p := by
  let l := Real.log (8 / 7)
  let k := Real.log (15 / 8)
  let A := 73 / 100 * p - 1
  let B := 1 + 63 / 500 * p
  have hL := farLog_eight_sevenths
  have hK := farLog_fifteen_eighths
  have hL₀ : 0 ≤ l := by linarith only [hL.1]
  have hK₀ : 0 ≤ k := by linarith only [hK.1]
  have hA : -(27 / 100 : ℝ) ≤ A := by unfold A; linarith only [hp]
  have hB : (563 / 500 : ℝ) ≤ B := by unfold B; linarith only [hp]
  have hL₂ := pow_le_pow_left₀ hL₀ hL.2.le 2
  have hK₂ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 628 / 1000) hK.1.le 2
  have h₁ : (19 / 100 : ℝ) < 2 * (73 / 100) * l + l ^ 2 * A := by
    have hL' : -(27 / 100 : ℝ) * (1336 / 10000) ^ 2 ≤ A * l ^ 2 :=
      (mul_le_mul_of_nonpos_left hL₂ (by norm_num)).trans (mul_le_mul_of_nonneg_right hA (sq_nonneg l))
    linarith only [hL',hL.1]
  have h₂ : (285 / 1000 : ℝ) < -2 * (63 / 500) * k + k ^ 2 * B := by
    have hK' := mul_le_mul hB hK₂ (by norm_num : (0 : ℝ) ≤ (628 / 1000) ^ 2) (by linarith only [hB] : 0 ≤ B)
    linarith only [hK',hK.2]
  have hU : (8 / 7 : ℝ) ≤ (7 / 8 : ℝ) ^ (-p) := by
    rw [show (8 / 7 : ℝ) = (7 / 8 : ℝ) ^ (-(1 : ℝ)) by norm_num [Real.rpow_neg_one]]
    exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith only [hp])
  have hV : (322 / 1000 : ℝ) < (15 / 8 : ℝ) ^ (-p) :=
    farBasePow_ge_fifth (by norm_num) hpP (by norm_num) (by norm_num)
  have hU' := mul_le_mul h₁.le hU (by norm_num : (0 : ℝ) ≤ 8 / 7)
    (by linarith only [h₁] : 0 ≤ 2 * (73 / 100) * l + l ^ 2 * A)
  have hV' := mul_le_mul h₂.le hV.le (by norm_num : (0 : ℝ) ≤ 322 / 1000)
    (by linarith only [h₂] : 0 ≤ -2 * (63 / 500) * k + k ^ 2 * B)
  unfold farPolyPowerDD
  have hLog : Real.log (7 / 8) = -l := by
    unfold l
    rw [show (7 / 8 : ℝ) = (8 / 7 : ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [hLog]
  unfold A at hU'
  unfold B k at hV'
  norm_num
  nlinarith only [hU',hV']

private theorem farNative_at_x_second {p : ℝ} (hp : 1 ≤ p) (hpP : p ≤ 9 / 5) :
    -(108 / 1000 : ℝ) <
      farPolyPowerDD 0 (511 / 1300) (-1) (13 / 8) p + farPolyPowerDD 0 (9 / 100) 1 (21 / 8) p := by
  let x : ℝ := 13 / 8
  let y : ℝ := 21 / 8
  let lx := Real.log x
  let ly := Real.log y
  let A := (511 / 1300) * p - 1
  let B := 1 + (9 / 100) * p
  let C := -2 * (511 / 1300) * lx + lx ^ 2 * A
  let D := -2 * (9 / 100) * ly + ly ^ 2 * B
  let r := (21 / 13 : ℝ) ^ (-p)
  have hL := farLog_thirteen_eighths
  have hK := farLog_twentyone_eighths
  have hL₀ : 0 ≤ lx := by linarith only [hL.1]
  have hA : (511 / 1300 : ℝ) - 1 ≤ A := by unfold A; linarith only [hp]
  have hB : (109 / 100 : ℝ) ≤ B := by unfold B; linarith only [hp]
  have hL₂ := pow_le_pow_left₀ hL₀ hL.2.le 2
  have hK₂ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 965 / 1000) hK.1.le 2
  have hC : -(526 / 1000 : ℝ) ≤ C := by
    have hL' : ((511 / 1300 : ℝ) - 1) * (486 / 1000) ^ 2 ≤ A * lx ^ 2 :=
      (mul_le_mul_of_nonpos_left hL₂ (by norm_num)).trans (mul_le_mul_of_nonneg_right hA (sq_nonneg lx))
    unfold C
    linarith only [hL',hL.2]
  have hD : (84 / 100 : ℝ) ≤ D := by
    have hK' := mul_le_mul hB hK₂ (by norm_num : (0 : ℝ) ≤ (965 / 1000) ^ 2) (by linarith only [hB] : 0 ≤ B)
    unfold D
    linarith only [hK',hK.2]
  have hr : (42 / 100 : ℝ) < r := farBasePow_ge_fifth (by norm_num) hpP (by norm_num) (by norm_num)
  have hR : y ^ (-p) = x ^ (-p) * r := by
    have hr' : r = y ^ (-p) / x ^ (-p) := by
      unfold r
      rw [show (21 / 13 : ℝ) = y / x by norm_num [x,y]]
      exact Real.div_rpow (show 0 ≤ y by norm_num [y]) (show 0 ≤ x by norm_num [x]) (-p)
    rw [hr']
    field_simp [(Real.rpow_pos_of_pos (by norm_num [x] : 0 < x) (-p)).ne']
  have hRx := mul_le_mul hr.le hD (by norm_num : (0 : ℝ) ≤ 84 / 100) (by linarith only [hr] : 0 ≤ r)
  have hCD : -(1732 / 10000 : ℝ) ≤ C + r * D := by linarith only [hC,hRx]
  have hX : x ^ (-p) ≤ 8 / 13 := by
    simpa only [x,show (13 / 8 : ℝ)⁻¹ = 8 / 13 by norm_num] using
      farBasePow_le_inv (x := 13 / 8) (by norm_num) hp
  have hP : 0 ≤ x ^ (-p) := Real.rpow_nonneg (by norm_num [x]) _
  have h := (mul_le_mul_of_nonpos_right hX (by norm_num : -(1732 / 10000 : ℝ) ≤ 0)).trans
    (mul_le_mul_of_nonneg_left hCD hP)
  have he : farPolyPowerDD 0 (511 / 1300) (-1) x p + farPolyPowerDD 0 (9 / 100) 1 y p =
      x ^ (-p) * (C + r * D) := by
    unfold farPolyPowerDD C D A B lx ly
    rw [hR]
    ring
  change _ < farPolyPowerDD 0 (511 / 1300) (-1) x p + farPolyPowerDD 0 (9 / 100) 1 y p
  rw [he]
  linarith only [h]

private theorem farNative_slope_second {p : ℝ} (hp : 1 ≤ p) (hpP : p ≤ 9 / 5) :
    -(24 / 100 : ℝ) <
      farPolyPowerDD (1022 / 4225) (1022 / 4225 - 8 / 13) 0 (13 / 8) p +
        farPolyPowerDD (6 / 175) (6 / 175 + 8 / 21) 0 (21 / 8) p := by
  let a : ℝ := 1022 / 4225
  let b : ℝ := a - 8 / 13
  let c : ℝ := 6 / 175
  let d : ℝ := c + 8 / 21
  let x : ℝ := 13 / 8
  let y : ℝ := 21 / 8
  let lx := Real.log x
  let ly := Real.log y
  have hL := farLog_thirteen_eighths
  have hK := farLog_twentyone_eighths
  have hx₀ : 0 ≤ lx := by linarith only [hL.1]
  have hy₀ : 0 ≤ ly := by linarith only [hK.1]
  have h₁ : -(132 / 1000 : ℝ) ≤ a * p ^ 2 + b * p := by
    have h := mul_nonneg (sub_nonneg.mpr hp) (show 0 ≤ a * (p + 1) + b by
      unfold a b; linarith only [hp])
    unfold a b at h ⊢
    nlinarith only [h]
  have h₂ : 2 * a * p + b ≤ 50 / 100 := by unfold a b; linarith only [hpP]
  have h₃ : (449 / 1000 : ℝ) ≤ c * p ^ 2 + d * p := by
    have h := mul_nonneg (sub_nonneg.mpr hp) (show 0 ≤ c * (p + 1) + d by unfold c d; positivity)
    unfold c d at h ⊢
    nlinarith only [h]
  have h₄ : 2 * c * p + d ≤ 54 / 100 := by unfold c d; linarith only [hpP]
  have hD₁ : 0 ≤ 2 * a * p + b := by unfold a b; linarith only [hp]
  have hX := mul_le_mul hL.2.le h₂ hD₁ (by norm_num : (0 : ℝ) ≤ 486 / 1000)
  have hD₂ : 0 ≤ 2 * c * p + d := by unfold c d; linarith only [hp]
  have hY := mul_le_mul hK.2.le h₄ hD₂ (by norm_num : (0 : ℝ) ≤ 966 / 1000)
  have hX₂ : -(132 / 1000 : ℝ) * (486 / 1000) ^ 2 ≤ lx ^ 2 * (a * p ^ 2 + b * p) := by
    have h := pow_le_pow_left₀ hx₀ hL.2.le 2
    have h' := (mul_le_mul_of_nonpos_left h (show -(132 / 1000 : ℝ) ≤ 0 by norm_num)).trans
      (mul_le_mul_of_nonneg_right h₁ (sq_nonneg lx))
    simpa only [mul_comm lx] using h'.trans_eq (mul_comm _ _)
  have hY₂ : (449 / 1000 : ℝ) * (965 / 1000) ^ 2 ≤ ly ^ 2 * (c * p ^ 2 + d * p) := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 965 / 1000) hK.1.le 2
    simpa only [mul_comm (ly ^ 2),mul_comm ((965 / 1000 : ℝ) ^ 2)] using
      mul_le_mul h₃ h (by norm_num : (0 : ℝ) ≤ (965 / 1000) ^ 2) ((by norm_num : (0 : ℝ) ≤ 449 / 1000).trans h₃)
  have hX₃ : -(34 / 1000 : ℝ) ≤ 2 * a - 2 * lx * (2 * a * p + b) + lx ^ 2 * (a * p ^ 2 + b * p) := by
    unfold a
    linarith only [hX,hX₂]
  have hY₃ : -(557 / 1000 : ℝ) ≤ 2 * c - 2 * ly * (2 * c * p + d) + ly ^ 2 * (c * p ^ 2 + d * p) := by
    unfold c
    linarith only [hY,hY₂]
  have hXP : x ^ (-p) ≤ 8 / 13 := by
    simpa only [x,show (13 / 8 : ℝ)⁻¹ = 8 / 13 by norm_num] using
      farBasePow_le_inv (x := 13 / 8) (by norm_num) hp
  have hYP : y ^ (-p) ≤ 8 / 21 := by
    simpa only [y,show (21 / 8 : ℝ)⁻¹ = 8 / 21 by norm_num] using
      farBasePow_le_inv (x := 21 / 8) (by norm_num) hp
  have hF := (mul_le_mul_of_nonpos_left hXP (by norm_num : -(34 / 1000 : ℝ) ≤ 0)).trans
    (mul_le_mul_of_nonneg_right hX₃ (Real.rpow_nonneg (by norm_num [x]) _))
  have hG := (mul_le_mul_of_nonpos_left hYP (by norm_num : -(557 / 1000 : ℝ) ≤ 0)).trans
    (mul_le_mul_of_nonneg_right hY₃ (Real.rpow_nonneg (by norm_num [y]) _))
  change _ < farPolyPowerDD a b 0 x p + farPolyPowerDD c d 0 y p
  unfold farPolyPowerDD
  change _ < (2 * a - 2 * lx * (2 * a * p + b) + lx ^ 2 * (a * p ^ 2 + b * p + 0)) * x ^ (-p) +
    (2 * c - 2 * ly * (2 * c * p + d) + ly ^ 2 * (c * p ^ 2 + d * p + 0)) * y ^ (-p)
  simp only [add_zero]
  linarith only [hF,hG]

theorem farNative_second_gt {p : ℝ} (hp : 1 ≤ p) (hpP : p ≤ 9 / 5) :
    -(46 / 1000 : ℝ) < farNativeJet 2 p := by
  have hZ := (pureZ_second_bounds hp hpP).2
  change pureZSecond p ≤ 1 / 8 at hZ
  rw [farNativeJet_second]
  linarith only [hZ,farNative_at_u_second hp hpP,farIntegralTerm_second_gt hp hpP,
    farNative_at_x_second hp hpP,farNative_slope_second hp hpP]

end ACS12.GammaMeasure

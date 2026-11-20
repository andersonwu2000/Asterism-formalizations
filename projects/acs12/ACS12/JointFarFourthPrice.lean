import ACS12.JointFarSourceJet
import ACS12.JointFarIntegralPrice

/-! Uniform W43 curvature for the licensed fourth-source envelope. -/
namespace ACS12.GammaMeasure

open Set

private theorem farFourth_right_first_le {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    farFourthRightJet 1 p ≤ 33 / 100 := by
  let t := p - 1
  have ht : 0 ≤ t := sub_nonneg.mpr hp
  have htU : t ≤ 4 / 5 := by unfold t; linarith only [hP]
  have hSq := mul_le_mul_of_nonneg_right htU ht
  have hR : (28717 / 100000 : ℝ) ≤ (2 : ℝ) ^ (-p) :=
    (far_fifth_rpow_lower (b := 2) (x := 28717 / 100000) (k := 9)
      (by norm_num) (by norm_num) (by norm_num)).le.trans
        ((Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr (by linarith only [hP]))
  have hL : (69 / 100 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hE := mul_le_mul hL hR (by norm_num : (0 : ℝ) ≤ 28717 / 100000)
    ((by norm_num : (0 : ℝ) ≤ 69 / 100).trans hL)
  have hP' := (purePPrime_bounds hp hP).2
  have hQ' := (pureQPrime_bounds hp hP).1
  change purePPrime p < 1645 / 1000 + (729 / 500) * t + (1 / 8) * t ^ 2 at hP'
  change (16 / 5 : ℝ) + (8 / 5) * t < pureQPrime p at hQ'
  change 2 + purePPrime p - pureQPrime p + (-Real.log 2) ^ (1 : ℕ) * (2 : ℝ) ^ (-p) ≤ _
  simp only [pow_one]
  nlinarith only [hSq,ht,hP',hQ',hE]

private theorem farFourth_right_second_le {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    farFourthRightJet 2 p ≤ 357 / 1000 := by
  have hE : (2 : ℝ) ^ (-p) ≤ 1 / 2 := by
    have h := (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr (neg_le_neg hp)
    norm_num [Real.rpow_neg_one] at h
    exact h
  have hLog : (Real.log 2) ^ 2 ≤ (694 / 1000 : ℝ) ^ 2 := by
    apply pow_le_pow_left₀ (Real.log_nonneg (by norm_num))
    linarith only [Real.log_two_lt_d9]
  have hB := mul_le_mul hLog hE (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
    (by norm_num : (0 : ℝ) ≤ (694 / 1000) ^ 2)
  change purePSecond p - pureQSecond p + (-Real.log 2) ^ (2 : ℕ) * (2 : ℝ) ^ (-p) ≤ _
  rw [neg_sq]
  linarith only [hB,(purePSecond_bounds hp hP).2,pureQSecond_gt hp hP]

private theorem farFourth_right_value_le {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    farFourthRightJet 0 p ≤ 1 / 2 := by
  let f (q : ℝ) := farFourthRightJet 0 q - (33 / 100) * (q - 1)
  have hD (q : ℝ) (hq : q ∈ Icc 1 (9 / 5)) :
      HasDerivAt f (farFourthRightJet 1 q - 33 / 100) q := by
    simpa only [f,mul_one] using (farFourthRightJet_deriv (k := 0) (by decide)
      (zero_lt_one.trans_le hq.1)).sub (((hasDerivAt_id q).sub_const 1).const_mul (33 / 100))
  have hM : AntitoneOn f (Icc 1 (9 / 5)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · exact fun q hq => (hD q hq).continuousAt.continuousWithinAt
    · exact fun q hq => (hD q (interior_subset hq)).differentiableAt.differentiableWithinAt
    · intro q hq
      have hq' : q ∈ Icc (1 : ℝ) (9 / 5) := interior_subset hq
      rw [(hD q hq').deriv]
      exact sub_nonpos.mpr (farFourth_right_first_le hq'.1 hq'.2)
  have h₀ : farFourthRightJet 0 1 ≤ 1 / 10 := by
    norm_num [farFourthRightJet,farPowerJet,pureP,pureQ,Real.rpow_neg_one]
    linarith only [powerTail_three_bounds.1]
  have h := hM (show (1 : ℝ) ∈ Icc 1 (9 / 5) by norm_num) ⟨hp,hP⟩ hp
  unfold f at h
  linarith only [h,h₀,hP]

private theorem farFourth_base_upper {b p c : ℝ} (hb : 0 < b) (hb' : b ≤ 1) (hP : p ≤ 9 / 5)
    (hc : 0 ≤ c) (h : (b ^ (19 : ℕ))⁻¹ < c ^ (5 : ℕ)) : b ^ (-(p + 2)) ≤ c := by
  have h₁ := Real.rpow_le_rpow_of_exponent_ge hb hb' (show -(19 : ℝ) / 5 ≤ -(p + 2) by linarith only [hP])
  exact h₁.trans (fifth_rpow_upper (k := 19) hb hc h).le

theorem farFourth_second_gt {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    -(52 / 100 : ℝ) < farFourthJet 2 p := by
  let L := -Real.log (13 / 16)
  let J := -Real.log (15 / 16)
  have hL : L = Real.log (16 / 13) := by
    unfold L
    rw [← Real.log_inv,show (13 / 16 : ℝ)⁻¹ = 16 / 13 by norm_num]
  have hJ : J = Real.log (16 / 15) := by
    unfold J
    rw [← Real.log_inv,show (15 / 16 : ℝ)⁻¹ = 16 / 15 by norm_num]
  have hL₀ : 0 ≤ L := by rw [hL]; linarith only [farLog_sixteen_thirteenths.1]
  have hJ₀ : 0 ≤ J := by rw [hJ]; linarith only [farLog_sixteen_fifteenths.1]
  have hL' : L ≤ 208 / 1000 := by rw [hL]; exact farLog_sixteen_thirteenths.2.le
  have hJ' : J ≤ 65 / 1000 := by rw [hJ]; exact farLog_sixteen_fifteenths.2.le
  have hL₂ := pow_le_pow_left₀ hL₀ hL' 2
  have hJ₂ := pow_le_pow_left₀ hJ₀ hJ' 2
  have ht : 0 ≤ p - 1 := sub_nonneg.mpr hp
  have htU : p - 1 ≤ 4 / 5 := by linarith only [hP]
  have ht₂ := pow_le_pow_left₀ ht htU 2
  have hP₀ : 1 + pureP p ≤ 28 / 10 := by
    rw [pureP_eq]
    have hZ : pureZ p ≤ 2245 / 1000 := by linarith only [(pureZ_band_bounds hp hP).2,htU]
    have h := mul_le_mul htU hZ (by
      linarith only [(pureZ_band_bounds hp hP).1,ht]) (by norm_num : (0 : ℝ) ≤ 4 / 5)
    linarith only [h]
  have hP₁ : purePPrime p ≤ 2892 / 1000 := by linarith only [(purePPrime_bounds hp hP).2,htU,ht₂]
  let A : ℝ := 429 / 250 + 2 * (208 / 1000) * (2892 / 1000) + (208 / 1000) ^ 2 * (28 / 10)
  let B : ℝ := 357 / 1000 + 2 * (65 / 1000) * (33 / 100) + (65 / 1000) ^ 2 * (1 / 2)
  have hA : purePSecond p + 2 * L * purePPrime p + L ^ 2 * (1 + pureP p) ≤ A := by
    have h₁ := (mul_le_mul_of_nonneg_left hP₁ (by positivity : 0 ≤ 2 * L)).trans
      (mul_le_mul_of_nonneg_right (show 2 * L ≤ 2 * (208 / 1000) by linarith only [hL'])
        (by norm_num : (0 : ℝ) ≤ 2892 / 1000))
    have h₀ := (mul_le_mul_of_nonneg_left hP₀ (sq_nonneg L)).trans
      (mul_le_mul_of_nonneg_right hL₂ (by norm_num : (0 : ℝ) ≤ 28 / 10))
    unfold A
    linarith only [h₁,h₀,(purePSecond_bounds hp hP).2]
  have hB : farFourthRightJet 2 p + 2 * J * farFourthRightJet 1 p + J ^ 2 * farFourthRightJet 0 p ≤ B := by
    have h₁ := (mul_le_mul_of_nonneg_left (farFourth_right_first_le hp hP) (by positivity : 0 ≤ 2 * J)).trans
      (mul_le_mul_of_nonneg_right (show 2 * J ≤ 2 * (65 / 1000) by linarith only [hJ'])
        (by norm_num : (0 : ℝ) ≤ 33 / 100))
    have h₀ := (mul_le_mul_of_nonneg_left (farFourth_right_value_le hp hP) (sq_nonneg J)).trans
      (mul_le_mul_of_nonneg_right hJ₂ (by norm_num : (0 : ℝ) ≤ 1 / 2))
    unfold B
    linarith only [h₁,h₀,farFourth_right_second_le hp hP]
  have hX := farFourth_base_upper (b := 13 / 16) (c := 221 / 100) (by norm_num) (by norm_num) hP
    (by norm_num) (by norm_num)
  have hY := farFourth_base_upper (b := 15 / 16) (c := 128 / 100) (by norm_num) (by norm_num) hP
    (by norm_num) (by norm_num)
  have hAX := (mul_le_mul_of_nonneg_left hA (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 13 / 16) _)).trans
    (mul_le_mul_of_nonneg_right hX (by norm_num [A]))
  have hBY := (mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 15 / 16) _)).trans
    (mul_le_mul_of_nonneg_right hY (by norm_num [B]))
  rw [farFourthJet_second]
  rw [show (Real.log (13 / 16)) ^ 2 = L ^ 2 by unfold L; ring,
    show (Real.log (15 / 16)) ^ 2 = J ^ 2 by unfold J; ring]
  change _ < -(9 / 128) * ((13 / 16 : ℝ) ^ (-(p + 2)) * (purePSecond p + 2 * L * purePPrime p +
    L ^ 2 * (1 + pureP p)) + (15 / 16 : ℝ) ^ (-(p + 2)) * (farFourthRightJet 2 p +
    2 * J * farFourthRightJet 1 p + J ^ 2 * farFourthRightJet 0 p))
  norm_num [A,B] at hAX hBY
  rw [show -(2 : ℝ) + -p = -(p + 2) by ring] at hAX hBY
  linarith only [hAX,hBY]

end ACS12.GammaMeasure

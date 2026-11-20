import ACS12.JointSharpGapEndpoint

/-! The unchanged W37–40 far envelopes and their complete endpoint values. -/
namespace ACS12.GammaMeasure

open Set MeasureTheory

noncomputable def farG (p x : ℝ) : ℝ :=
  x ^ (-p) * (p * (511 / 800) / x - 1) +
    (x + 1) ^ (-p) * (1 + p * (189 / 800) / (x + 1))

noncomputable def farGx (p x : ℝ) : ℝ :=
  x ^ (-p) * (p / x - p * (p + 1) * (511 / 800) / x ^ 2) +
    (x + 1) ^ (-p) * (-p / (x + 1) - p * (p + 1) * (189 / 800) / (x + 1) ^ 2)

noncomputable def farGIntegral (p : ℝ) : ℝ :=
  (511 / 800) * (13 / 8 : ℝ) ^ (-p) + (189 / 800) * (21 / 8 : ℝ) ^ (-p) -
    ∫ x : ℝ in (13 / 8 : ℝ)..(21 / 8), x ^ (-p)

noncomputable def jointFarNative (p : ℝ) : ℝ :=
  (7 / 8) * (1 + (189 / 800) * p - pureZ p) + (3 / 4) * farG p (7 / 8) + farGIntegral p +
    (3 / 8) * farG p (13 / 8) - (3 / 64) * farGx p (13 / 8)

private noncomputable def farM₂ (p : ℝ) : ℝ := pureQ p - p * (p + 1)
private noncomputable def farM₃ (p : ℝ) : ℝ := pureR p - p * (p + 1) * (p + 2)

noncomputable def jointFarAdjacent (p : ℝ) : ℝ :=
  (4 / 3 : ℝ) ^ (p - 1) * (p + 1 - pureZ p + 13 * farM₂ p / 72 - farM₃ p / 72 + 1063 / 1296000) +
    pureZ p - 1 - p / 8 + (1 / 8 - 3 * p / 4) * (8 / 7 : ℝ) ^ p + farM₂ p / 128 + 1 / 2048

noncomputable def jointFarFourth (p : ℝ) : ℝ :=
  -(9 / 128) * ((1 + pureP p) * (13 / 16 : ℝ) ^ (-p - 2) +
    (2 * p + pureP p - pureQ p + (2 : ℝ) ^ (-p)) * (15 / 16 : ℝ) ^ (-p - 2))

private theorem farLog_lower : (4795 / 10000 : ℝ) < Real.log (21 / 13) := by
  have h := Real.hasSum_log_one_add (a := (8 / 13 : ℝ)) (by norm_num)
  have hS := h.summable.sum_le_tsum (Finset.range 3) (fun j _ => by positivity)
  rw [h.tsum_eq] at hS
  norm_num [Finset.sum_range_succ] at hS
  exact (by norm_num : (4795 / 10000 : ℝ) < _).trans_le hS

private theorem upperFarRpow {x v : ℝ} {k : ℕ} (hx : 0 < x) (hv : 0 ≤ v)
    (h : (x ^ k)⁻¹ < v ^ 5) : x ^ (-(k : ℝ) / 5) < v := by
  apply lt_of_pow_lt_pow_left₀ 5 hv
  rw [← Real.rpow_mul_natCast hx.le,show -(k : ℝ) / 5 * ↑(5 : ℕ) = -(k : ℝ) by norm_num,
    Real.rpow_neg hx.le,Real.rpow_natCast]
  exact h

private theorem lowerFarRpow {x v : ℝ} {k : ℕ} (hx : 0 < x)
    (h : v ^ 5 < (x ^ k)⁻¹) : v < x ^ (-(k : ℝ) / 5) := by
  apply lt_of_pow_lt_pow_left₀ 5 (Real.rpow_nonneg hx.le _)
  rw [← Real.rpow_mul_natCast hx.le,show -(k : ℝ) / 5 * ↑(5 : ℕ) = -(k : ℝ) by norm_num,
    Real.rpow_neg hx.le,Real.rpow_natCast]
  exact h

theorem jointFarNative_one_lt : jointFarNative 1 < -(115 / 1000 : ℝ) := by
  have hI : (∫ x : ℝ in (13 / 8 : ℝ)..(21 / 8), x ^ (-(1 : ℝ))) = Real.log (21 / 13) := by
    simp only [Real.rpow_neg_one]
    rw [integral_inv_of_pos (by norm_num) (by norm_num)]
    norm_num
  unfold jointFarNative farGIntegral farG farGx
  rw [hI,pureZ_one_eq]
  norm_num [Real.rpow_neg_one]
  have hPi := Real.pi_gt_d4
  have hPi₂ := pow_lt_pow_left₀ hPi (by norm_num) (by decide : 2 ≠ 0)
  linarith only [farLog_lower,hPi₂]

theorem jointFarNative_endpoint_lt : jointFarNative (9 / 5) < -(42376 / 1000000 : ℝ) := by
  have hI : (∫ x : ℝ in (13 / 8 : ℝ)..(21 / 8), x ^ (-(9 / 5 : ℝ))) =
      ((13 / 8 : ℝ) ^ (-(9 / 5) : ℝ) * (13 / 8) - (21 / 8 : ℝ) ^ (-(9 / 5) : ℝ) * (21 / 8)) /
        (4 / 5) := by
    rw [integral_rpow (Or.inr ⟨by norm_num,by rw [uIcc_of_le (by norm_num)]; norm_num⟩),
      show -(9 / 5 : ℝ) + 1 = -(9 / 5) + 1 by rfl]
    simp only [Real.rpow_add_one (by norm_num : (13 / 8 : ℝ) ≠ 0),Real.rpow_add_one (by norm_num : (21 / 8 : ℝ) ≠ 0)]
    ring
  have hA : (7 / 8 : ℝ) ^ (-(9 : ℝ) / 5) < 1271703 / 1000000 :=
    upperFarRpow (k := 9) (by norm_num) (by norm_num) (by norm_num)
  have hB : (15 / 8 : ℝ) ^ (-(9 : ℝ) / 5) < 322551 / 1000000 :=
    upperFarRpow (k := 9) (by norm_num) (by norm_num) (by norm_num)
  have hC : (417314 / 1000000 : ℝ) < (13 / 8 : ℝ) ^ (-(9 : ℝ) / 5) :=
    lowerFarRpow (k := 9) (by norm_num) (by norm_num)
  have hD : (21 / 8 : ℝ) ^ (-(9 : ℝ) / 5) < 176023 / 1000000 :=
    upperFarRpow (k := 9) (by norm_num) (by norm_num) (by norm_num)
  have hE : jointFarNative (9 / 5) =
      39907 / 32000 - (7 / 8) * pureZ (9 / 5) + (471 / 2000) * (7 / 8 : ℝ) ^ (-(9 : ℝ) / 5) +
        (9201 / 10000) * (15 / 8 : ℝ) ^ (-(9 : ℝ) / 5) - (5059687 / 3380000) * (13 / 8 : ℝ) ^ (-(9 : ℝ) / 5) +
        (559089 / 140000) * (21 / 8 : ℝ) ^ (-(9 : ℝ) / 5) := by
    unfold jointFarNative farGIntegral farG farGx
    rw [hI]
    norm_num only [show (7 / 8 : ℝ) + 1 = 15 / 8 by norm_num,
      show (13 / 8 : ℝ) + 1 = 21 / 8 by norm_num,neg_div]
    ring
  rw [hE]
  linarith only [hA,hB,hC,hD,pureZ_upperEndpoint_lower]

theorem jointFarAdjacent_one_lt : jointFarAdjacent 1 < 232 / 1000 := by
  have hQ : pureQ 1 < 24042 / 10000 := by
    unfold pureQ
    norm_num
    linarith only [powerTail_three_bounds.2]
  have hR : (648 / 100 : ℝ) < pureR 1 := by
    unfold pureR
    norm_num
    linarith only [powerTail_four_gt]
  unfold jointFarAdjacent farM₂ farM₃
  norm_num [Real.rpow_zero,Real.rpow_one]
  linarith only [hQ,hR]

theorem jointFarFourth_one_lt : jointFarFourth 1 < -(13 / 100 : ℝ) := by
  have hQ : pureQ 1 < 24042 / 10000 := by
    unfold pureQ
    norm_num
    linarith only [powerTail_three_bounds.2]
  unfold jointFarFourth pureP
  norm_num [Real.rpow_neg_one,Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 13 / 16),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 15 / 16),Real.rpow_ofNat]
  linarith only [hQ]

theorem jointFarFourth_endpoint_lt : jointFarFourth (9 / 5) < -(4438 / 10000 : ℝ) := by
  let p : ℝ := 9 / 5
  obtain ⟨hPL,hPU,hQL,hQU⟩ := jointPure_endpoint_moments
  have hL : (219 / 100 : ℝ) < (13 / 16 : ℝ) ^ (-(19 : ℝ) / 5) :=
    lowerFarRpow (k := 19) (by norm_num) (by norm_num)
  have hL' : (5 / 4 : ℝ) < (15 / 16 : ℝ) ^ (-(19 : ℝ) / 5) :=
    lowerFarRpow (k := 19) (by norm_num) (by norm_num)
  have hX : (28717 / 100000 : ℝ) < (2 : ℝ) ^ (-(9 : ℝ) / 5) :=
    lowerFarRpow (k := 9) (by norm_num) (by norm_num)
  have hI : (279572464 / 100000000 : ℝ) < 1 + pureP p := by unfold p; linarith only [hPL]
  have hI' : (151440 / 1000000 : ℝ) < 2 * p + pureP p - pureQ p + (2 : ℝ) ^ (-p) := by
    unfold p
    simp only [neg_div] at hX ⊢
    linarith only [hPL,hQU,hX]
  have h₁ := mul_le_mul hI.le hL.le (by norm_num : (0 : ℝ) ≤ 219 / 100)
    (by linarith only [hI] : 0 ≤ 1 + pureP p)
  have h₂ := mul_le_mul hI'.le hL'.le (by norm_num : (0 : ℝ) ≤ 5 / 4)
    ((by norm_num : (0 : ℝ) ≤ 151440 / 1000000).trans hI'.le)
  change jointFarFourth p < _
  unfold jointFarFourth
  rw [show -p - 2 = -(19 : ℝ) / 5 by unfold p; norm_num]
  linarith only [h₁,h₂]


theorem jointFarAdjacent_endpoint_lt : jointFarAdjacent (9 / 5) < 26363 / 100000 := by
  let p : ℝ := 9 / 5
  let s := (4 / 3 : ℝ) ^ (p - 1)
  let r := (8 / 7 : ℝ) ^ p
  let Z₀ : ℝ := 22446558 / 10000000
  let Q₁ : ℝ := 5531453306 / 1000000000
  let R₀ : ℝ := 199783662 / 10000000
  let A := p + 1 - Z₀ + 13 * (Q₁ - p * (p + 1)) / 72 -
    (R₀ - p * (p + 1) * (p + 2)) / 72 + 1063 / 1296000
  have hZ : Z₀ < pureZ p := pureZ_upperEndpoint_lower
  have hQ : pureQ p < Q₁ := jointPure_endpoint_moments.2.2.2
  have hR : R₀ < pureR p := by
    have h := powerTail_four_point_eight_lower
    unfold R₀ p pureR
    norm_num [show (9 / 5 : ℝ) + 3 = 24 / 5 by norm_num]
    linarith only [h]
  have hS₀ : 1 ≤ s := Real.one_le_rpow (by norm_num) (by norm_num [p])
  have hS : s < 12588 / 10000 := by
    unfold s p
    apply lt_of_pow_lt_pow_left₀ 5 (by norm_num)
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 4 / 3),
      show (9 / 5 - 1 : ℝ) * ↑(5 : ℕ) = ↑(4 : ℕ) by norm_num,Real.rpow_natCast]
    norm_num
  have hr : (1271702 / 1000000 : ℝ) < r := by
    unfold r p
    have h := lowerFarRpow (x := 7 / 8) (v := 1271702 / 1000000) (k := 9) (by norm_num) (by norm_num)
    have hE : (8 / 7 : ℝ) ^ (9 / 5 : ℝ) = (7 / 8 : ℝ) ^ (-(9 : ℝ) / 5) := by
      rw [show (8 / 7 : ℝ) = (7 / 8 : ℝ)⁻¹ by norm_num,Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 7 / 8),
        ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 7 / 8),neg_div]
    rw [hE]
    exact h
  have hA : 0 ≤ A := by norm_num [A,p,Z₀,Q₁,R₀]
  have hM : s * (p + 1 - pureZ p + 13 * farM₂ p / 72 - farM₃ p / 72 + 1063 / 1296000) + pureZ p ≤
      s * A + Z₀ := by
    apply sub_nonneg.mp
    have hEq : s * A + Z₀ -
        (s * (p + 1 - pureZ p + 13 * farM₂ p / 72 - farM₃ p / 72 + 1063 / 1296000) + pureZ p) =
          (s - 1) * (pureZ p - Z₀) + (13 * s / 72) * (Q₁ - pureQ p) +
            (s / 72) * (pureR p - R₀) := by unfold A farM₂ farM₃; ring
    rw [hEq]
    have h₁ : 0 ≤ s := zero_le_one.trans hS₀
    exact add_nonneg (add_nonneg (mul_nonneg (sub_nonneg.mpr hS₀) (sub_nonneg.mpr hZ.le))
      (mul_nonneg (by positivity) (sub_nonneg.mpr hQ.le))) (mul_nonneg (by positivity) (sub_nonneg.mpr hR.le))
  have hA' := mul_le_mul_of_nonneg_right hS.le hA
  have hM₂ : farM₂ p ≤ Q₁ - p * (p + 1) := sub_le_sub_right hQ.le _
  change s * (p + 1 - pureZ p + 13 * farM₂ p / 72 - farM₃ p / 72 + 1063 / 1296000) + pureZ p -
    1 - p / 8 + (1 / 8 - 3 * p / 4) * r + farM₂ p / 128 + 1 / 2048 < _
  norm_num [A,p,Z₀,Q₁,R₀] at hA' hM hM₂ ⊢
  linarith only [hM,hA',hM₂,hr]

end ACS12.GammaMeasure

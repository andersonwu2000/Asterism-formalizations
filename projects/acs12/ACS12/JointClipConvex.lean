import ACS12.JointClipCut

/-! Convexity of the single joint clipping price in G26. -/
namespace ACS12.GammaMeasure

open Set

private noncomputable def clipLogWeight (p : ℝ) : ℝ :=
  -p * Real.log (jointClipAlpha p) - (p + 1) * Real.log (p + 1)

private noncomputable def clipDecay (p : ℝ) : ℝ := Real.exp (clipLogWeight p)

private noncomputable def clipRate (p : ℝ) : ℝ :=
  Real.log (jointClipAlpha p) + Real.log (p + 1) + 1 + p / (p + 27)

private noncomputable def clipRateD (p : ℝ) : ℝ :=
  1 / (p + 27) + 1 / (p + 1) + 27 / (p + 27) ^ 2

private noncomputable def clipCorrection (p : ℝ) : ℝ :=
  1 + 8 * p / ((p + 2) * (p + 27))

private noncomputable def clipCorrectionD (p : ℝ) : ℝ :=
  8 * (54 - p ^ 2) / ((p + 2) * (p + 27)) ^ 2

private noncomputable def clipCorrectionDD (p : ℝ) : ℝ :=
  -16 * p / ((p + 2) * (p + 27)) ^ 2 -
    16 * (54 - p ^ 2) * (2 * p + 29) / ((p + 2) * (p + 27)) ^ 3

private theorem clipDecay_hasDerivAt {p : ℝ} (hp : 0 < p) :
    HasDerivAt clipDecay (-clipDecay p * clipRate p) p := by
  have h := hasDerivAt_id p
  have hA : 0 < jointClipAlpha p := by unfold jointClipAlpha; positivity
  have h₁ := ((h.add_const 27).div_const 16).log hA.ne'
  have h₂ := (h.add_const 1).log (show p + 1 ≠ 0 by positivity)
  have hD : HasDerivAt clipLogWeight (-clipRate p) p := by
    convert (h.neg.mul h₁).sub ((h.add_const 1).mul h₂) using 1
    simp only [clipRate, jointClipAlpha, id_eq, Pi.neg_apply, one_mul]
    field_simp [(show p + 1 ≠ 0 by positivity), (show p + 27 ≠ 0 by positivity)]
    ring
  convert hD.exp using 1
  unfold clipDecay
  ring

private theorem clipRate_hasDerivAt {p : ℝ} (hp : 0 < p) :
    HasDerivAt clipRate (clipRateD p) p := by
  have h := hasDerivAt_id p
  have hA : 0 < jointClipAlpha p := by unfold jointClipAlpha; positivity
  have h₁ := ((h.add_const 27).div_const 16).log hA.ne'
  have h₂ := (h.add_const 1).log (show p + 1 ≠ 0 by positivity)
  have h₃ := h.div (h.add_const 27) (show p + 27 ≠ 0 by positivity)
  convert ((h₁.add h₂).const_add 1).add h₃ using 1
  · funext x
    simp only [clipRate, jointClipAlpha, Pi.add_apply, Pi.div_apply, id_eq]
    ring
  · simp only [clipRateD, id_eq, one_mul, mul_one]
    field_simp [(show p + 1 ≠ 0 by positivity), (show p + 27 ≠ 0 by positivity)]
    ring

private theorem clipCorrection_hasDerivAt {p : ℝ} (hp : 0 < p) :
    HasDerivAt clipCorrection (clipCorrectionD p) p := by
  have h := hasDerivAt_id p
  have hD := (h.add_const 2).mul (h.add_const 27)
  have h₀ : (p + 2) * (p + 27) ≠ 0 := by positivity
  convert (((h.const_mul 8).div hD h₀).const_add 1) using 1
  simp only [clipCorrectionD, id_eq, Pi.mul_apply, one_mul, mul_one]
  field_simp [h₀, (show p + 2 ≠ 0 by positivity), (show p + 27 ≠ 0 by positivity)]
  ring

private theorem clipCorrectionD_hasDerivAt {p : ℝ} (hp : 0 < p) :
    HasDerivAt clipCorrectionD (clipCorrectionDD p) p := by
  have h := hasDerivAt_id p
  have hD := ((h.add_const 2).mul (h.add_const 27)).pow 2
  have hN := (((h.pow 2).const_sub 54).const_mul 8)
  have h₀ : ((p + 2) * (p + 27)) ^ 2 ≠ 0 := by positivity
  convert hN.div hD h₀ using 1
  simp only [clipCorrectionDD, id_eq, Pi.mul_apply, Pi.pow_apply, one_mul, mul_one,
    show (2 - 1 : ℕ) = 1 by decide, pow_one]
  field_simp [(show p + 2 ≠ 0 by positivity), (show p + 27 ≠ 0 by positivity)]
  ring

private theorem clipRate_bounds {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    2 < clipRate p ∧ clipRate p < 3 ∧ clipRateD p < 3 / 5 := by
  have hA₀ : 0 < jointClipAlpha p := by unfold jointClipAlpha; positivity
  have hP₁ : 0 < p + 1 := by positivity
  have hA₁ : 7 / 4 ≤ jointClipAlpha p := by unfold jointClipAlpha; linarith only [hp]
  have hA₂ : jointClipAlpha p ≤ 9 / 5 := by unfold jointClipAlpha; linarith only [hP]
  have hA := mul_le_mul hA₁ (show 2 ≤ p + 1 by linarith only [hp]) (by norm_num) hA₀.le
  have hB := mul_le_mul hA₂ (show p + 1 ≤ 14 / 5 by linarith only [hP]) hP₁.le
    (by norm_num : (0 : ℝ) ≤ 9 / 5)
  have hlog₁ : 1 < Real.log (jointClipAlpha p * (p + 1)) := by
    apply (Real.lt_log_iff_exp_lt (mul_pos hA₀ hP₁)).mpr
    linarith only [Real.exp_one_lt_d9,hA]
  have hlog₂ : Real.log (jointClipAlpha p * (p + 1)) < 19 / 10 := by
    apply (Real.log_lt_iff_lt_exp (mul_pos hA₀ hP₁)).mpr
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 19 / 10) 5
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith only [h,hB]
  rw [Real.log_mul hA₀.ne' hP₁.ne'] at hlog₁ hlog₂
  have hR₀ : 0 ≤ p / (p + 27) := by positivity
  have hR₁ : p / (p + 27) ≤ 1 / 10 := by
    apply (div_le_iff₀ (show 0 < p + 27 by positivity)).mpr
    linarith only [hP]
  have hL := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 28)
    (show 28 ≤ p + 27 by linarith only [hp])
  have hM := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
    (show 2 ≤ p + 1 by linarith only [hp])
  have hN := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 27) (by norm_num : (0 : ℝ) < 28 ^ 2)
    (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 28) (show 28 ≤ p + 27 by linarith only [hp]) 2)
  unfold clipRate clipRateD
  exact ⟨by linarith only [hlog₁,hR₀], by linarith only [hlog₂,hR₁], by linarith only [hL,hM,hN]⟩

private theorem clipCorrection_bounds {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    1 ≤ clipCorrection p ∧ clipCorrectionD p ≤ 3 / 10 ∧ -(3 / 5) ≤ clipCorrectionDD p := by
  let D := (p + 2) * (p + 27)
  have hD : 84 ≤ D := by
    have h := mul_le_mul (show 3 ≤ p + 2 by linarith only [hp]) (show 28 ≤ p + 27 by linarith only [hp])
      (by norm_num : (0 : ℝ) ≤ 28) (show 0 ≤ p + 2 by positivity)
    simpa only [D, show (3 : ℝ) * 28 = 84 by norm_num] using h
  have hB : 0 ≤ 54 - p ^ 2 := by
    have h := pow_le_pow_left₀ (zero_le_one.trans hp) hP 2
    nlinarith only [h]
  have hD₂ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 84) hD 2
  have hD₃ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 84) hD 3
  constructor
  · unfold clipCorrection
    exact le_add_of_nonneg_right (by positivity)
  · constructor
    · change 8 * (54 - p ^ 2) / D ^ 2 ≤ _
      have h := div_le_div_of_nonneg_left (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hB)
        (by norm_num : (0 : ℝ) < 84 ^ 2) hD₂
      have h₂ := div_le_div_of_nonneg_right (show 8 * (54 - p ^ 2) ≤ 432 by nlinarith only [sq_nonneg p])
        (by norm_num : (0 : ℝ) ≤ 84 ^ 2)
      exact (h.trans h₂).trans (by norm_num)
    · change _ ≤ -16 * p / D ^ 2 - 16 * (54 - p ^ 2) * (2 * p + 29) / D ^ 3
      have h₁ : 16 * p / D ^ 2 ≤ 32 / (84 : ℝ) ^ 2 :=
        (div_le_div_of_nonneg_left (by positivity : 0 ≤ 16 * p) (by norm_num : (0 : ℝ) < 84 ^ 2) hD₂).trans
          (div_le_div_of_nonneg_right (by linarith only [hP]) (by norm_num))
      have hC := mul_le_mul (show 54 - p ^ 2 ≤ 54 by linarith only [sq_nonneg p])
        (show 2 * p + 29 ≤ 33 by linarith only [hP]) (by positivity : 0 ≤ 2 * p + 29) (by norm_num)
      have h₂ : 16 * (54 - p ^ 2) * (2 * p + 29) / D ^ 3 ≤ (16 * 54 * 33) / (84 : ℝ) ^ 3 :=
        (div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg (by norm_num) hB) (by positivity))
          (by norm_num : (0 : ℝ) < 84 ^ 3) hD₃).trans
          (div_le_div_of_nonneg_right (by nlinarith only [hC]) (by norm_num))
      norm_num at h₁ h₂
      simp only [neg_mul, neg_div]
      linarith only [h₁,h₂]

theorem jointClipPrice_convex : ConvexOn ℝ (Icc 1 (9 / 5)) jointClipPrice := by
  let f (p : ℝ) := clipDecay p * clipCorrection p
  let fD (p : ℝ) := clipDecay p * (clipCorrectionD p - clipRate p * clipCorrection p)
  let fDD (p : ℝ) := clipDecay p * (clipCorrection p * (clipRate p ^ 2 - clipRateD p) -
    2 * clipRate p * clipCorrectionD p + clipCorrectionDD p)
  have hEq (p : ℝ) (hp : p ∈ Icc (1 : ℝ) (9 / 5)) : jointClipPrice p = f p := by
    have hp₀ := zero_lt_one.trans_le hp.1
    have hA : 0 < jointClipAlpha p := by unfold jointClipAlpha; positivity
    have hB : 0 < p + 1 := by positivity
    unfold jointClipPrice jointClipCut f clipDecay clipLogWeight clipCorrection
    rw [Real.mul_rpow hA.le hB.le, mul_div_assoc, ← Real.rpow_sub_one hB.ne']
    have hE : Real.exp (-p * Real.log (jointClipAlpha p) - (p + 1) * Real.log (p + 1)) =
        jointClipAlpha p ^ (-p) * (p + 1) ^ (-p - 1) := by
      rw [Real.rpow_def_of_pos hA, Real.rpow_def_of_pos hB, ← Real.exp_add]
      congr 1
      ring
    rw [hE]
    unfold jointClipAlpha
    field_simp [(show p + 2 ≠ 0 by positivity), (show p + 27 ≠ 0 by positivity)]
    ring
  have hd (p : ℝ) (hp : 0 < p) : HasDerivAt f (fD p) p := by
    convert (clipDecay_hasDerivAt hp).mul (clipCorrection_hasDerivAt hp) using 1
    unfold fD
    ring
  have hdd (p : ℝ) (hp : 0 < p) : HasDerivAt fD (fDD p) p := by
    convert (clipDecay_hasDerivAt hp).mul ((clipCorrectionD_hasDerivAt hp).sub
      ((clipRate_hasDerivAt hp).mul (clipCorrection_hasDerivAt hp))) using 1
    simp only [fDD, Pi.sub_apply, Pi.mul_apply]
    ring
  have hC : ConvexOn ℝ (Icc 1 (9 / 5)) f := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (D := Icc (1 : ℝ) (9 / 5)) (f' := fD) (f'' := fDD) (convex_Icc _ _)
      (fun p hp => (hd p (zero_lt_one.trans_le hp.1)).continuousAt.continuousWithinAt)
      (fun p hp => (hd p (zero_lt_one.trans_le (show p ∈ Icc (1 : ℝ) (9 / 5) from interior_subset hp).1)).hasDerivWithinAt)
      (fun p hp => (hdd p (zero_lt_one.trans_le (show p ∈ Icc (1 : ℝ) (9 / 5) from interior_subset hp).1)).hasDerivWithinAt)
    intro p hp
    have hp' : p ∈ Icc (1 : ℝ) (9 / 5) := interior_subset hp
    obtain ⟨hL,hU,hD⟩ := clipRate_bounds hp'.1 hp'.2
    obtain ⟨h₀,h₁,h₂⟩ := clipCorrection_bounds hp'.1 hp'.2
    have hR : 17 / 5 ≤ clipRate p ^ 2 - clipRateD p := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hL.le 2
      nlinarith only [h,hD]
    have hP := mul_le_mul h₀ hR (by norm_num : (0 : ℝ) ≤ 17 / 5) (by linarith only [h₀])
    have hQ := mul_le_mul_of_nonneg_left h₁ (show 0 ≤ 2 * clipRate p by linarith only [hL])
    change 0 ≤ clipDecay p * _
    apply mul_nonneg (Real.exp_pos (clipLogWeight p)).le
    nlinarith only [hP,hQ,hU,h₂]
  refine ⟨convex_Icc _ _, fun x hx y hy a b ha hb hab => ?_⟩
  rw [hEq x hx, hEq y hy, hEq _ (hC.1 hx hy ha hb hab)]
  exact hC.2 hx hy ha hb hab

end ACS12.GammaMeasure

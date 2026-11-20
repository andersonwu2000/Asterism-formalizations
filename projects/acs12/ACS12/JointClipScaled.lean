import ACS12.JointClipCut

/-! One complete clipping price, with an explicit cutoff scaling quadratically in the gap. -/
namespace ACS12.GammaMeasure

open CenteredCircle.AllN Set

private theorem jointClipCut_scaled_neg {p u : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (huL : 7 / 8 ≤ u) (hu₁ : u < 1) :
    let C := jointClipCut p / (8 * (1 - u))
    (1 - u) * C ^ 2 - (1 / 2 - middleA u) * (p + 1) * C +
      (1 / 6 - middleA u / 2) * (p + 1) * (p + 2) < 0 := by
  let δ := 1 - u
  let d : ℝ := 1 / 8
  let C₀ := jointClipCut p
  let v := C₀ * d
  let C := v / δ
  have hδ : 0 < δ := sub_pos.mpr hu₁
  have hδU : δ ≤ d := by dsimp only [δ,d]; linarith only [huL]
  have hC₀ : 0 < C₀ := jointClipCut_pos hp
  have hv : 0 < v := mul_pos hC₀ (by norm_num [d])
  have hC : 0 < C := div_pos hv hδ
  have hP₀ : 0 < p + 1 := by linarith only [hp]
  have hP₁ : 0 < p + 2 := by linarith only [hp]
  have hvU : v ≤ 63 / 100 := by
    have h := mul_le_mul (show jointClipAlpha p ≤ 9 / 5 by unfold jointClipAlpha; linarith only [hP])
      (show p + 1 ≤ 14 / 5 by linarith only [hP]) hP₀.le (by norm_num : (0 : ℝ) ≤ 9 / 5)
    change jointClipCut p ≤ _ at h
    dsimp only [v,d,C₀]
    linarith only [h]
  let G (x : ℝ) := v - (13 / 50 + (6 / 25) * x ^ 2) * (p + 1) +
    ((7 / 150 + (3 / 25) * x ^ 2) * (p + 1) * (p + 2)) * x / v
  have hGap : G δ ≤ G d := by
    let B := (7 / 150 + (3 / 25) * (d ^ 2 + d * δ + δ ^ 2)) * (p + 2) -
      v * (6 / 25) * (d + δ)
    have hB : 0 ≤ B := by
      have h₁ := mul_le_mul_of_nonneg_right (show (7 / 150 : ℝ) ≤ 7 / 150 + (3 / 25) * (d ^ 2 + d * δ + δ ^ 2)
        by dsimp only [d]; nlinarith only [hδ, sq_nonneg δ]) hP₁.le
      have h₂ := mul_le_mul hvU (show d + δ ≤ 1 / 4 by dsimp only [d] at *; linarith only [hδU])
        (by dsimp only [d]; positivity) (by norm_num : (0 : ℝ) ≤ 63 / 100)
      dsimp only [B]
      nlinarith only [h₁,h₂,hp]
    have hE : (G d - G δ) * v = (d - δ) * (p + 1) * B := by
      dsimp only [G,B]
      field_simp [hv.ne']
      ring
    have h := mul_nonneg (mul_nonneg (sub_nonneg.mpr hδU) hP₀.le) hB
    rw [← hE] at h
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_left h hv)
  have hFar := jointClipCut_quadratic_neg (u := 7 / 8) hp hP le_rfl (by norm_num)
  have hFarE : G d * C₀ =
      (1 - 7 / 8) * jointClipCut p ^ 2 - (1 / 2 - middleA (7 / 8)) * (p + 1) * jointClipCut p +
        (1 / 6 - middleA (7 / 8) / 2) * (p + 1) * (p + 2) := by
    dsimp only [G, v, C₀, d, middleA]
    have hC' : jointClipCut p ≠ 0 := hC₀.ne'
    field_simp [hC']
    ring
  have hNeg : G δ < 0 := hGap.trans_lt (neg_of_mul_neg_left (hFarE.symm ▸ hFar) hC₀.le)
  have hA : middleA u = (6 / 25) * (1 - δ ^ 2) := by unfold middleA; dsimp only [δ]; ring
  have hE : G δ * C =
      δ * C ^ 2 - (1 / 2 - middleA u) * (p + 1) * C +
        (1 / 6 - middleA u / 2) * (p + 1) * (p + 2) := by
    rw [hA]
    dsimp only [G,C]
    field_simp [hδ.ne', hv.ne']
    ring
  have hEq : C = C₀ / (8 * δ) := by dsimp only [C,v,d]; ring
  change δ * (C₀ / (8 * δ)) ^ 2 - _ + _ < 0
  rw [← hEq, ← hE]
  exact mul_neg_of_neg_of_pos hNeg hC

theorem jointPureClip_tail_le {p L u t q : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) (hL : 0 < L)
    (huL : 7 / 8 ≤ u) (hu₁ : u < 1) (ht : 0 ≤ t) (hq : 0 < q) (hq₁ : q ≤ 1) :
    samplingTail (lawRightNegative p L 0 u) t q ≤ 8 * (1 - u) ^ 2 * jointClipPrice p := by
  let δ := 1 - u
  let a := 8 * δ
  let C₀ := jointClipCut p
  let C := C₀ / a
  have hδ : 0 < δ := sub_pos.mpr hu₁
  have ha : 0 < a := mul_pos (by norm_num) hδ
  have ha₁ : a ≤ 1 := by dsimp only [a,δ]; linarith only [huL]
  have hC₀ : 0 < C₀ := jointClipCut_pos hp
  have hC : 0 < C := div_pos hC₀ ha
  have hp₀ := zero_lt_one.trans_le hp
  have hp₂ := hP.trans (by norm_num : (9 / 5 : ℝ) ≤ 2)
  have hu : 0 < u := (by norm_num : (0 : ℝ) < 7 / 8).trans_le huL
  have hTail := pureRightNegative_tail_le_of_cut hp hp₂ hL hu hu₁.le ht hq hC
    (jointClipCut_scaled_neg hp hP huL hu₁)
  have hPow {b : ℝ} (hb : 1 ≤ b) : C ^ (-b) ≤ a * C₀ ^ (-b) := by
    have hA : a ^ b ≤ a := by
      simpa only [Real.rpow_one] using (Real.rpow_le_rpow_of_exponent_ge ha ha₁ hb)
    have hE : C ^ (-b) = a ^ b * C₀ ^ (-b) := by
      unfold C
      rw [Real.div_rpow hC₀.le ha.le, Real.rpow_neg ha.le]
      field_simp [(Real.rpow_pos_of_pos ha b).ne']
    rw [hE]
    exact mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg hC₀.le _)
  have h1 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hPow hp) hδ.le)
    (show 0 ≤ p + 1 by positivity)
  have h2 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hPow (show 1 ≤ p + 1 by linarith only [hp])) (mul_nonneg hp₀.le hδ.le))
    (show 0 ≤ 2 * (p + 2) by positivity)
  have hq' := mul_le_of_le_one_left (show 0 ≤ p * δ * C ^ (-(p + 1)) / (2 * (p + 2)) by positivity) hq₁
  have hPrice : δ * (a * C₀ ^ (-p)) / (p + 1) + p * δ * (a * C₀ ^ (-(p + 1))) / (2 * (p + 2)) =
      8 * δ ^ 2 * jointClipPrice p := by
    unfold jointClipPrice
    change _ = 8 * δ ^ 2 * (C₀ ^ (-p) / (p + 1) * (1 + p / (2 * jointClipAlpha p * (p + 2))))
    rw [show -(p + 1) = -p - 1 by ring, Real.rpow_sub_one hC₀.ne']
    dsimp only [a, C₀, jointClipCut]
    have hA : 0 < jointClipAlpha p := by unfold jointClipAlpha; positivity
    field_simp [hA.ne', (show p + 1 ≠ 0 by positivity), (show p + 2 ≠ 0 by positivity)]
  change samplingTail (lawRightNegative p L 0 u) t q ≤
    δ * C ^ (-p) / (p + 1) + q * (p * δ * C ^ (-(p + 1)) / (2 * (p + 2))) at hTail
  change samplingTail (lawRightNegative p L 0 u) t q ≤ 8 * δ ^ 2 * jointClipPrice p
  nlinarith only [hTail,h1,h2,hq',hPrice]

end ACS12.GammaMeasure

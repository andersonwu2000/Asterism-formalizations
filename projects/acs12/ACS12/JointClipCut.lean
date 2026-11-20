import ACS12.PureClipPrice

/-! The smooth complete C2 cutoff G25 for the joint terminal value. -/
namespace ACS12.GammaMeasure

noncomputable def jointClipAlpha (p : ℝ) : ℝ := (p + 27) / 16

noncomputable def jointClipCut (p : ℝ) : ℝ := jointClipAlpha p * (p + 1)

theorem jointClipCut_pos {p : ℝ} (hp : 1 ≤ p) : 0 < jointClipCut p := by
  unfold jointClipCut jointClipAlpha
  positivity

theorem jointClipCut_quadratic_neg {p u : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (huL : 7 / 8 ≤ u) (hu₁ : u ≤ 1) :
    (1 - u) * jointClipCut p ^ 2 - (1 / 2 - middleA u) * (p + 1) * jointClipCut p +
      (1 / 6 - middleA u / 2) * (p + 1) * (p + 2) < 0 := by
  let δ := 1 - u
  let A := jointClipAlpha p
  let t := p - 1
  have hδ : 0 ≤ δ := sub_nonneg.mpr hu₁
  have hδU : δ ≤ 1 / 8 := by dsimp only [δ]; linarith only [huL]
  have hA : 7 / 4 ≤ A := by dsimp only [A,jointClipAlpha]; linarith only [hp]
  have hP₀ : 0 < p + 1 := by linarith only [hp]
  have ht₀ : 0 ≤ t := sub_nonneg.mpr hp
  have htU : t ≤ 4 / 5 := by dsimp only [t]; linarith only [hP]
  let B := -(6 / 25) * A * (p + 1) + (3 / 25) * (p + 2)
  let F (x : ℝ) := x * A ^ 2 * (p + 1) - (13 / 50) * A * (p + 1) + (7 / 150) * (p + 2) + x ^ 2 * B
  have hB : 0 ≤ A ^ 2 * (p + 1) + (1 / 8 + δ) * B := by
    have hδ' : 0 ≤ 1 / 8 + δ := by linarith only [hδ]
    have h := mul_le_mul_of_nonneg_right (show 1 / 8 + δ ≤ 1 / 4 by linarith only [hδU])
      (show 0 ≤ (6 / 25) * A * (p + 1) by positivity)
    have h₂ := mul_nonneg hδ' (show 0 ≤ (3 / 25) * (p + 2) by positivity)
    have h₃ := mul_nonneg (mul_nonneg (show 0 ≤ A by linarith only [hA])
      (show 0 ≤ A - 3 / 50 by linarith only [hA])) hP₀.le
    dsimp only [B]
    nlinarith only [h,h₂,h₃]
  have hF : F δ ≤ F (1 / 8) := by
    have h := mul_nonneg (sub_nonneg.mpr hδU) hB
    dsimp only [F]
    linear_combination h
  have hE : F (1 / 8) = t ^ 3 / 2048 + (303 / 25600) * t ^ 2 - (163 / 19200) * t - 19 / 1600 := by
    dsimp only [F,B,A,jointClipAlpha,t]
    ring
  have hNeg : F (1 / 8) < 0 := by
    rw [hE]
    have ht₂ := mul_le_mul_of_nonneg_right htU ht₀
    have ht₃ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht₀ htU 2) ht₀
    nlinarith only [ht₂,ht₃,htU]
  have h := mul_neg_of_neg_of_pos (hF.trans_lt hNeg) hP₀
  have hAeq : middleA u = (6 / 25) * (1 - δ ^ 2) := by unfold middleA; dsimp only [δ]; ring
  rw [hAeq, jointClipCut]
  dsimp only [F,B] at h
  linear_combination h

noncomputable def jointClipPrice (p : ℝ) : ℝ :=
  jointClipCut p ^ (-p) / (p + 1) * (1 + p / (2 * jointClipAlpha p * (p + 2)))

theorem jointClipPrice_one : jointClipPrice 1 = 23 / 147 := by
  norm_num [jointClipPrice,jointClipCut,jointClipAlpha,Real.rpow_neg]

theorem jointClipPrice_endpoint_lt : jointClipPrice (9 / 5) < 28 / 1250 := by
  have hCut : jointClipCut (9 / 5) = 126 / 25 := by norm_num [jointClipCut,jointClipAlpha]
  have hAl : jointClipAlpha (9 / 5) = 9 / 5 := by norm_num [jointClipAlpha]
  unfold jointClipPrice
  rw [hCut,hAl]
  have h : (126 / 25 : ℝ) ^ (-(9 / 5 : ℝ)) < 7448 / 134375 := by
    apply (Real.rpow_lt_rpow_iff (Real.rpow_nonneg (by norm_num) _) (by norm_num)
      (z := (5 : ℝ)) (by norm_num)).mp
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 126 / 25)]
    norm_num [Real.rpow_neg]
  norm_num at ⊢
  linarith only [h]

end ACS12.GammaMeasure

import ACS12.JointGapK

/-! Exact complete linear coefficients in the original source-gap increment. -/
namespace ACS12.GammaMeasure

open Set Filter MeasureTheory CenteredCircle.AllN
open GammaDeficit (lineDensity)

theorem jointGapD_moment {p : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) :
    let f (s : ℝ) := lineDensity p s * (1 - polyA s * (1 - BoseShape.C s))
    IntegrableOn f (Ioi 0) ∧ (∫ s : ℝ in Ioi 0, f s) = jointPureD p := by
  let f (s : ℝ) := lineDensity p s * (1 - polyA s * (1 - BoseShape.C s))
  let X (s : ℝ) := lineDensity p s * Real.exp (-s)
  let Y (s : ℝ) := lineDensity p s * s * Real.exp (-s)
  let Z (s : ℝ) := lineDensity p s * polyA s * BoseShape.C s
  have hp₀ := zero_lt_one.trans_le hp
  obtain ⟨hX,hXE⟩ := lineDensity_moment hp₀ zero_lt_one 0
  obtain ⟨hY,hYE⟩ := lineDensity_moment hp₀ zero_lt_one 1
  obtain ⟨hZ,hZE⟩ := pureBoseA_moment hp hp₂
  simp only [pow_zero,mul_one,Nat.cast_zero,add_zero,pow_one,Nat.cast_one,Real.one_rpow] at hX hY hXE hYE
  rw [div_self (Real.Gamma_pos_of_pos hp₀).ne'] at hXE
  rw [Real.Gamma_add_one hp₀.ne',mul_div_cancel_right₀ _ (Real.Gamma_pos_of_pos hp₀).ne'] at hYE
  change IntegrableOn X (Ioi 0) at hX
  change IntegrableOn Y (Ioi 0) at hY
  change IntegrableOn Z (Ioi 0) at hZ
  have hEq (s : ℝ) : f s = (X s + Y s) + Z s := by
    unfold f X Y Z polyA
    ring
  constructor
  · exact ((hX.add hY).add hZ).congr (Eventually.of_forall fun s => (hEq s).symm)
  · change (∫ s : ℝ in Ioi 0, f s) = jointPureD p
    rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => hEq s)]
    change (∫ s : ℝ in Ioi 0, (X + Y) s + Z s) = _
    rw [integral_add (hX.add hY) hZ]
    change (∫ s : ℝ in Ioi 0, X s + Y s) + _ = _
    rw [integral_add hX hY]
    change (∫ s : ℝ in Ioi 0, X s) + (∫ s : ℝ in Ioi 0, Y s) + (∫ s : ℝ in Ioi 0, Z s) = _
    rw [hXE,hYE,hZE,jointPureD]
    ring

theorem jointGapB_moment {p : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) :
    let f (s : ℝ) := lineDensity p s * Real.exp (-s) * polyA s * (1 - BoseShape.C s)
    IntegrableOn f (Ioi 0) ∧ (∫ s : ℝ in Ioi 0, f s) = jointPureB p := by
  let f (s : ℝ) := lineDensity p s * Real.exp (-s) * polyA s * (1 - BoseShape.C s)
  let A (s : ℝ) := lineDensity p s * polyA s * Real.exp (-s)
  let B (s : ℝ) := lineDensity p s * s ^ 2 * (Real.exp (-s * 2) / (1 - Real.exp (-s)))
  let C (s : ℝ) := lineDensity p s * s * Real.exp (-s * 2)
  let D (s : ℝ) := lineDensity p s * polyB s * Real.exp (-s) * BoseShape.C s
  have hp₀ := zero_lt_one.trans_le hp
  obtain ⟨hA,hAE⟩ := pureA_exp_moment hp hp₂
  obtain ⟨hB,hBE⟩ := lineDensity_bose₂_moment hp₀ (by decide : (0 : ℕ) < 2)
  obtain ⟨hC,hCE⟩ := lineDensity_moment hp₀ (by norm_num : (0 : ℝ) < 2) 1
  have hDE := pureBoseBX_moment hp hp₂
  simp only [pow_one,Nat.cast_one,Nat.cast_ofNat] at hB hBE hC hCE
  rw [Real.Gamma_add_one hp₀.ne',mul_div_cancel_right₀ _ (Real.Gamma_pos_of_pos hp₀).ne',
    show -(p + 1) = -p - 1 by ring,Real.rpow_sub_one (by norm_num : (2 : ℝ) ≠ 0)] at hCE
  have hD : IntegrableOn D (Ioi 0) := by
    have h : IntegrableOn (fun s => lineDensity p s * (polyB s * Real.exp (-s)) * BoseShape.C (s * 1)) (Ioi 0) := by
      apply pureC_integrable_of_linear hp hp₂ zero_lt_one (B := 1) zero_le_one
      · unfold polyB
        fun_prop
      · intro s hs
        have hL := (polyB_pos hs).le
        have hU : polyB s ≤ s := by
          unfold polyB
          linarith only [Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.le)]
        have hX := Real.exp_pos (-s)
        rw [abs_of_nonneg (mul_nonneg hL hX.le),one_mul]
        exact (mul_le_mul_of_nonneg_right hU hX.le).trans
          (mul_le_of_le_one_right hs.le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.le)))
    simpa only [D,mul_one,mul_assoc] using h
  change IntegrableOn A (Ioi 0) at hA
  change IntegrableOn B (Ioi 0) at hB
  change IntegrableOn C (Ioi 0) at hC
  have hEq (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) : f s = ((A s - B s) + C s) + D s := by
    have hP : polyA s + polyB s = s * (1 - Real.exp (-s)) := by unfold polyA polyB; ring
    have hE := boseC_paired_eq (show 0 < s from hs)
    dsimp only [f,A,B,C,D]
    rw [show -s * 2 = -s + -s by ring,Real.exp_add]
    have hAX : (polyA s + polyB s) * BoseShape.C s =
        s * (s * (Real.exp (-s) / (1 - Real.exp (-s))) - Real.exp (-s)) := by
      rw [hP,mul_assoc,hE]
    linear_combination -lineDensity p s * Real.exp (-s) * hAX
  constructor
  · apply (((hA.sub hB).add hC).add hD).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hEq s hs).symm
  · change (∫ s : ℝ in Ioi 0, f s) = jointPureB p
    rw [setIntegral_congr_fun measurableSet_Ioi hEq]
    change (∫ s : ℝ in Ioi 0, (A - B + C) s + D s) = _
    rw [integral_add ((hA.sub hB).add hC) hD]
    change (∫ s : ℝ in Ioi 0, (A - B) s + C s) + _ = _
    rw [integral_add (hA.sub hB) hC]
    change ((∫ s : ℝ in Ioi 0, A s - B s) + _) + _ = _
    rw [integral_sub hA hB]
    change ((∫ s : ℝ in Ioi 0, A s) - (∫ s : ℝ in Ioi 0, B s)) +
      (∫ s : ℝ in Ioi 0, C s) + (∫ s : ℝ in Ioi 0, D s) = _
    rw [hAE,hBE,hCE,hDE,jointPureB,powerTail_shift (q := p + 2) (by linarith only [hp]) 1]
    simp only [Nat.cast_one,Real.one_rpow]
    unfold pureQ
    ring

end ACS12.GammaMeasure

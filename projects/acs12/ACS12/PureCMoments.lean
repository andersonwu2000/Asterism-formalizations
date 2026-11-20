import ACS12.OuterDeficitMoments

/-! The complete pure Bose moments used by the outer pure corner. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaDeficit (lineDensity lineDensity_exp_integral)

noncomputable def pureZ (p : ℝ) : ℝ := p * powerTail (p + 1) 1

noncomputable def pureQ (p : ℝ) : ℝ := p * (p + 1) * powerTail (p + 2) 1

theorem pureIntegral_scale {p t : ℝ} (ht : 0 < t) (f : ℝ → ℝ) :
    (∫ s : ℝ in Ioi 0, lineDensity p s * f (t * s)) =
      t ^ (-p) * ∫ s : ℝ in Ioi 0, lineDensity p s * f s := by
  let g (s : ℝ) := lineDensity p s * f s
  have hEq (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      lineDensity p s * f (t * s) = t ^ (-(p - 1)) * g (s * t) := by
    have hs₀ : 0 < s := hs
    have hρ : lineDensity p (s * t) = t ^ (p - 1) * lineDensity p s := by
      unfold lineDensity
      rw [Real.mul_rpow hs₀.le ht.le]
      ring
    have hPow : t ^ (-(p - 1)) * t ^ (p - 1) = 1 := by
      rw [Real.rpow_neg ht.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos ht _).ne']
    dsimp only [g]
    rw [hρ, show f (s * t) = f (t * s) by rw [mul_comm s t]]
    calc
      _ = (t ^ (-(p - 1)) * t ^ (p - 1)) * (lineDensity p s * f (t * s)) := by rw [hPow, one_mul]
      _ = _ := by ring
  rw [setIntegral_congr_fun measurableSet_Ioi hEq, integral_const_mul,
    integral_comp_mul_right_Ioi g 0 ht, zero_mul, smul_eq_mul, ← mul_assoc]
  have hPow : t ^ (-(p - 1)) * t⁻¹ = t ^ (-p) := by
    rw [← div_eq_mul_inv, ← Real.rpow_sub_one ht.ne', show -(p - 1) - 1 = -p by ring]
  rw [hPow]

theorem boseC_paired_eq {s : ℝ} (hs : 0 < s) :
    (1 - Real.exp (-s)) * BoseShape.C s =
      s * (Real.exp (-s) / (1 - Real.exp (-s))) - Real.exp (-s) := by
  have hd := (expHead_den_pos hs).ne'
  have he := (expTail_den_pos hs).ne'
  rw [Real.exp_neg] at hd ⊢
  unfold BoseShape.C
  field_simp [hd, he, (Real.exp_pos s).ne']
  ring

private theorem pureC_paired_moment {p : ℝ} (hp : 1 ≤ p) (k : ℕ) :
    let f (s : ℝ) := lineDensity p s * s ^ k * (1 - Real.exp (-s)) * BoseShape.C s
    IntegrableOn f (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, f s) =
        (Real.Gamma (p + k + 1) * powerTail (p + k + 1) 1 -
          Real.Gamma (p + k)) / Real.Gamma p := by
  have hp₀ := zero_lt_one.trans_le hp
  have hpK : 0 < p + k := by positivity
  let f (s : ℝ) := lineDensity p s * s ^ k * (1 - Real.exp (-s)) * BoseShape.C s
  let B (s : ℝ) := s ^ (p + k) * (Real.exp (-s * (1 : ℕ)) / (1 - Real.exp (-s)))
  let E (s : ℝ) := s ^ (p + k - 1) * Real.exp (-s)
  have hB : IntegrableOn B (Ioi 0) := boseMoment_integrable hpK (by decide : (0 : ℕ) < 1)
  have hE : IntegrableOn E (Ioi 0) := by
    simpa only [E, one_mul, neg_one_mul] using GammaDeficit.integrable_gamma_exp hpK zero_lt_one
  have hP (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      f s = (Real.Gamma p)⁻¹ * (B s - E s) := by
    have hs₀ : 0 < s := hs
    have hPow : s ^ (p - 1) * s ^ k = s ^ (p + k - 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hs₀]
      congr 1
      ring
    have hStep : s ^ (p + k - 1) * s = s ^ (p + k) := by
      rw [Real.rpow_sub_one hs₀.ne', div_mul_cancel₀ _ hs₀.ne']
    dsimp only [f, B, E, lineDensity]
    rw [mul_assoc (s ^ (p - 1) / Real.Gamma p * s ^ k), boseC_paired_eq hs₀,
      show (s ^ (p - 1) / Real.Gamma p * s ^ k) =
        (s ^ (p - 1) * s ^ k) / Real.Gamma p by ring, hPow]
    simp only [Nat.cast_one, mul_one]
    linear_combination (Real.Gamma p)⁻¹ * (Real.exp (-s) / (1 - Real.exp (-s))) * hStep
  have hExp : (∫ s : ℝ in Ioi 0, E s) = Real.Gamma (p + k) := by
    simpa only [E, one_mul, neg_one_mul, Real.one_rpow, mul_one] using GammaDeficit.gamma_exp_integral hpK zero_lt_one
  refine ⟨((hB.sub hE).const_mul (Real.Gamma p)⁻¹).congr ?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hP s hs).symm
  · change (∫ s : ℝ in Ioi 0, f s) = _
    rw [setIntegral_congr_fun measurableSet_Ioi hP, integral_const_mul, integral_sub hB hE, hExp]
    change (Real.Gamma p)⁻¹ * ((∫ s : ℝ in Ioi 0, B s) - _) = _
    rw [show (∫ s : ℝ in Ioi 0, B s) = Real.Gamma (p + k + 1) * powerTail (p + k + 1) 1 from
      boseMoment_integral hpK (by decide)]
    ring

theorem pureC_difference {p : ℝ} (hp : 1 ≤ p) :
    let f (s : ℝ) := lineDensity p s * (1 - Real.exp (-s)) * BoseShape.C s
    IntegrableOn f (Ioi 0) ∧ (∫ s : ℝ in Ioi 0, f s) = pureZ p - 1 := by
  obtain ⟨hI, hEq⟩ := pureC_paired_moment hp 0
  simp only [Nat.cast_zero, add_zero, pow_zero, mul_one] at hI hEq
  refine ⟨hI, ?_⟩
  rw [hEq, Real.Gamma_add_one (zero_lt_one.trans_le hp).ne', pureZ]
  field_simp [(Real.Gamma_pos_of_pos (zero_lt_one.trans_le hp)).ne']

theorem pureC_slope_difference {p : ℝ} (hp : 1 ≤ p) :
    let f (s : ℝ) := lineDensity p s * s * (1 - Real.exp (-s)) * BoseShape.C s
    IntegrableOn f (Ioi 0) ∧ (∫ s : ℝ in Ioi 0, f s) = pureQ p - p := by
  obtain ⟨hI, hEq⟩ := pureC_paired_moment hp 1
  simp only [Nat.cast_one, pow_one] at hI hEq
  refine ⟨hI, ?_⟩
  rw [hEq, Real.Gamma_add_one (show p + 1 ≠ 0 by positivity),
    Real.Gamma_add_one (zero_lt_one.trans_le hp).ne', pureQ, show p + 1 + 1 = p + 2 by ring]
  field_simp [(Real.Gamma_pos_of_pos (zero_lt_one.trans_le hp)).ne']

theorem pureC_slope {p : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) :
    let f (s : ℝ) := lineDensity p s * s * BoseShape.C s
    IntegrableOn f (Ioi 0) ∧ (∫ s : ℝ in Ioi 0, f s) = p * pureZ p := by
  let g (s : ℝ) := lineDensity p s * polyB s * BoseShape.C s
  have hG : (∫ s : ℝ in Ioi 0, g s) = 1 + (p - 1) * pureZ p := by
    have h := pureBoseB_moment hp hp₂ 0
    simp only [Nat.cast_zero, mul_zero, Real.exp_zero, mul_one, zero_add,
      Real.one_rpow, zero_mul, sub_zero] at h
    unfold pureZ
    dsimp only [g]
    linarith only [h]
  have hI : IntegrableOn g (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [hG]
    have hZ := powerTail_pos (by linarith : 1 < p + 1) (by decide : (0 : ℕ) < 1)
    exact (add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg (sub_nonneg.mpr hp) (mul_nonneg (zero_lt_one.trans_le hp).le hZ.le))).ne'
  obtain ⟨hD, hDE⟩ := pureC_difference hp
  have hF (s : ℝ) : lineDensity p s * s * BoseShape.C s =
      g s + lineDensity p s * (1 - Real.exp (-s)) * BoseShape.C s := by
    unfold g polyB
    ring
  refine ⟨(hI.add hD).congr (Eventually.of_forall fun s => (hF s).symm), ?_⟩
  simp_rw [hF]
  rw [integral_add hI hD, hG, hDE]
  ring

end ACS12.GammaMeasure

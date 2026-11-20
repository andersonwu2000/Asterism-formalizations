import ACS12.JointMomentsPrice

/-! Complete pure A/B slope moments for the fourth-root bracket. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaDeficit (lineDensity lineDensity_exp_integral)

theorem pureBoseA_moment {p : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) :
    IntegrableOn (fun s => lineDensity p s * polyA s * BoseShape.C s) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, lineDensity p s * polyA s * BoseShape.C s) = pureQ p - pureP p - p - 1 := by
  let I (s : ℝ) := lineDensity p s * polyA s * BoseShape.C s
  let J (s : ℝ) := lineDensity p s * polyB s * BoseShape.C s
  let F (s : ℝ) := lineDensity p s * s ^ 2 * (Real.exp (-s) / (1 - Real.exp (-s)))
  let G (s : ℝ) := lineDensity p s * s * Real.exp (-s)
  have hp₀ := zero_lt_one.trans_le hp
  have hΓ := (Real.Gamma_pos_of_pos hp₀).ne'
  have hΓ₂ : Real.Gamma (p + 2) = p * (p + 1) * Real.Gamma p := by
    rw [show p + 2 = (p + 1) + 1 by ring, Real.Gamma_add_one (by positivity : 0 < p + 1).ne',
      Real.Gamma_add_one hp₀.ne']
    ring
  have hF (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      F s = (Real.Gamma p)⁻¹ * (s ^ (p + 1) * (Real.exp (-s * (1 : ℕ)) / (1 - Real.exp (-s)))) := by
    have hs₀ : 0 < s := hs
    dsimp only [F, lineDensity]
    rw [Nat.cast_one, mul_one, ← Real.rpow_two,
      div_mul_eq_mul_div, ← Real.rpow_add hs₀, show p - 1 + 2 = p + 1 by ring]
    ring
  have hFI : IntegrableOn F (Ioi 0) := by
    have hB := (boseMoment_integrable (r := p + 1) (by positivity) (show (0 : ℕ) < 1 by decide)).const_mul
      (Real.Gamma p)⁻¹
    apply hB.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hF s hs).symm
  have hFE : (∫ s : ℝ in Ioi 0, F s) = pureQ p := by
    rw [setIntegral_congr_fun measurableSet_Ioi hF, integral_const_mul,
      boseMoment_integral (by positivity : 0 < p + 1) (show (0 : ℕ) < 1 by decide),
      show p + 1 + 1 = p + 2 by ring, hΓ₂, pureQ]
    field_simp [hΓ]
  have hG (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) : G s = p * (lineDensity (p + 1) s * Real.exp (-s)) := by
    have hs₀ : 0 < s := hs
    dsimp only [G, lineDensity]
    rw [Real.Gamma_add_one hp₀.ne', add_sub_cancel_right,
      Real.rpow_sub_one hs₀.ne']
    field_simp [hs₀.ne', hΓ, hp₀.ne']
  have hGI : IntegrableOn G (Ioi 0) := by
    have h := (GammaDeficit.lineDensity_exp_integrable (by positivity : 0 < p + 1) zero_lt_one).const_mul p
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    simpa only [mul_one] using (hG s hs).symm
  have hGE : (∫ s : ℝ in Ioi 0, G s) = p := by
    rw [setIntegral_congr_fun measurableSet_Ioi hG, integral_const_mul]
    simpa only [mul_one, Real.one_rpow] using congrArg (p * ·)
      (lineDensity_exp_integral (by positivity : 0 < p + 1) zero_lt_one)
  have hJE : (∫ s : ℝ in Ioi 0, J s) = 1 + pureP p := by
    simpa only [J, pureP, Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one, zero_add,
      Nat.zero_add, Real.one_rpow, zero_mul, sub_zero] using pureBoseB_moment hp hp₂ 0
  have hJI : IntegrableOn J (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [hJE]
    have hP := pureP_nonneg hp
    linarith only [hP]
  have hEq (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) : I s = F s - G s - J s := by
    have hs₀ : 0 < s := hs
    have hP : polyA s + polyB s = s * (1 - Real.exp (-s)) := by unfold polyA polyB; ring
    unfold I F G J
    linear_combination lineDensity p s * BoseShape.C s * hP +
      lineDensity p s * s * boseC_paired_eq hs₀
  constructor
  · apply ((hFI.sub hGI).sub hJI).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hEq s hs).symm
  · change (∫ s : ℝ in Ioi 0, I s) = _
    rw [setIntegral_congr_fun measurableSet_Ioi hEq]
    change (∫ s : ℝ in Ioi 0, (F - G) s - J s) = _
    rw [integral_sub (hFI.sub hGI) hJI]
    change ((∫ s : ℝ in Ioi 0, F s - G s) - ∫ s : ℝ in Ioi 0, J s) = _
    rw [integral_sub hFI hGI, hFE, hGE, hJE]
    ring

theorem pureBoseBX_moment {p : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) :
    (∫ s : ℝ in Ioi 0, lineDensity p s * polyB s * Real.exp (-s) * BoseShape.C s) =
      2 * p + pureP p - pureQ p + (2 : ℝ) ^ (-p) := by
  have h := pureBoseB_moment hp hp₂ 1
  norm_num at h
  rw [powerTail_shift (by linarith only [hp]) 1, powerTail_shift (by linarith only [hp]) 1] at h
  norm_num [Real.one_rpow] at h
  simpa only [pureP, pureQ, mul_one] using h.trans (by ring)

end ACS12.GammaMeasure

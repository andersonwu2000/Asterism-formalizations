import ACS12.JointPureBoseMoments
import ACS12.JointBoseBounds
import ACS12.JointLawDifference

/-! Exact scaling and domination for complete pure and actual fourth-root moments. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaDeficit (lineDensity signedDensity)

theorem pureIntegral_integrable_scale {p t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf : IntegrableOn (fun s => lineDensity p s * f s) (Ioi 0)) :
    IntegrableOn (fun s => lineDensity p s * f (t * s)) (Ioi 0) := by
  let g (s : ℝ) := lineDensity p s * f s
  have h := (integrableOn_Ioi_comp_mul_left_iff g 0 ht).mpr (by simpa only [mul_zero] using hf)
  apply (h.const_mul (t ^ (-(p - 1)))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs₀ : 0 < s := hs
  have hD : lineDensity p (t * s) = t ^ (p - 1) * lineDensity p s := by
    unfold lineDensity
    rw [Real.mul_rpow ht.le hs₀.le]
    ring
  have hP : t ^ (-(p - 1)) * t ^ (p - 1) = 1 := by
    rw [← Real.rpow_add ht, neg_add_cancel, Real.rpow_zero]
  change t ^ (-(p - 1)) * (lineDensity p (t * s) * f (t * s)) = _
  rw [hD, ← mul_assoc, ← mul_assoc, hP, one_mul]

theorem lawDensity_le_pure {p L θ s : ℝ} (hp : 1 ≤ p) (hp₂ : p < 2) (hL : 0 < L)
    (hθ : θ ∈ Icc (0 : ℝ) 1) (hs : 0 < s) : lawDensity p L θ s ≤ lineDensity p s := by
  have h := mul_nonneg hθ.1 (signedDensity_pos hp hp₂ hL hs).le
  unfold signedDensity at h
  unfold lawDensity
  nlinarith only [h]

theorem actual_integrable_of_pure {p L θ : ℝ} (hp : 1 ≤ p) (hp₂ : p < 2) (hL : 0 < L)
    (hθ : θ ∈ Icc (0 : ℝ) 1) {f : ℝ → ℝ} (hf : Measurable f) (hpos : ∀ s > 0, 0 ≤ f s)
    (hρ : IntegrableOn (fun s => lineDensity p s * f s) (Ioi 0)) :
    IntegrableOn (fun s => lawDensity p L θ s * f s) (Ioi 0) := by
  have hp₀ := zero_lt_one.trans_le hp
  apply hρ.mono' ((lawDensity_measurable (θ := θ) hp₀ hL).mul hf).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs₀ : 0 < s := hs
  rw [Real.norm_of_nonneg (mul_nonneg (lawDensity_pos hp₀ hL hθ hs₀).le (hpos s hs₀))]
  exact mul_le_mul_of_nonneg_right (lawDensity_le_pure hp hp₂ hL hθ hs₀) (hpos s hs₀)

private theorem pureFourthUnit_moment {p : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) :
    IntegrableOn (fun s => lineDensity p s * fourthD 1 1 s) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, lineDensity p s * fourthD 1 1 s) = pureQ p - pureP p := by
  let E (s : ℝ) := lineDensity p s * Real.exp (-s)
  let F (s : ℝ) := lineDensity p s * s * Real.exp (-s)
  let G (s : ℝ) := lineDensity p s * polyA s * BoseShape.C s
  let h0 : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have hE : IntegrableOn E (Ioi 0) := by
    simpa only [E, lawDensity, sub_zero, one_mul, zero_mul, add_zero, pow_zero, mul_one] using
      lawMoment_integrable hp hp₂ zero_lt_one h0 zero_lt_one 0
  have hF : IntegrableOn F (Ioi 0) := by
    simpa only [F, lawDensity, sub_zero, one_mul, zero_mul, add_zero, pow_one, mul_one] using
      lawMoment_integrable hp hp₂ zero_lt_one h0 zero_lt_one 1
  obtain ⟨hG, hGE⟩ := pureBoseA_moment hp hp₂
  change IntegrableOn G (Ioi 0) at hG
  have hEq (s : ℝ) : lineDensity p s * fourthD 1 1 s = E s + F s + G s := by
    simp only [E, F, G, fourthD, mul_one, one_mul]
    ring
  constructor
  · exact ((hE.add hF).add hG).congr (Eventually.of_forall fun s => (hEq s).symm)
  · rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => hEq s)]
    change (∫ s : ℝ in Ioi 0, (E + F) s + G s) = _
    rw [integral_add (hE.add hF) hG]
    change ((∫ s : ℝ in Ioi 0, E s + F s) + ∫ s : ℝ in Ioi 0, G s) = _
    rw [integral_add hE hF]
    have hp₀ := zero_lt_one.trans_le hp
    have hEE : (∫ s : ℝ in Ioi 0, E s) = lawMoment p 1 0 0 1 := by
      simp only [E, lawMoment, lawDensity, sub_zero, one_mul, zero_mul, add_zero, pow_zero, mul_one]
    have hFE : (∫ s : ℝ in Ioi 0, F s) = lawMoment p 1 0 1 1 := by
      simp only [F, lawMoment, lawDensity, sub_zero, one_mul, zero_mul, add_zero, pow_one, mul_one]
    rw [hEE, hFE, lawMoment_zero_radial hp₀ zero_lt_one, lawMoment_zero_slope hp₀ zero_lt_one, Real.one_rpow, Real.one_rpow]
    change (∫ s : ℝ in Ioi 0, G s) = _ at hGE
    rw [hGE]
    ring

theorem pureFourth_moment {p m : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hm : 0 < m) :
    IntegrableOn (fun s => lineDensity p s * fourthD m m s) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, lineDensity p s * fourthD m m s) = m ^ (-p) * (pureQ p - pureP p) := by
  obtain ⟨hI, hE⟩ := pureFourthUnit_moment hp hp₂
  have hEq (s : ℝ) : fourthD 1 1 (m * s) = fourthD m m s := by
    unfold fourthD
    simp only [mul_one, one_mul, neg_mul]
    ring_nf
  constructor
  · apply (pureIntegral_integrable_scale hm hI).congr
    exact Eventually.of_forall (fun s => congrArg (lineDensity p s * ·) (hEq s))
  · simp_rw [← hEq]
    rw [pureIntegral_scale hm, hE]

end ACS12.GammaMeasure

import ACS12.PressureDebitComparison
import ACS12.PressureLikelihood

/-! Slope elasticity on the closed pressure band, with literal endpoint two. -/
namespace ACS12.Pressure

open Set MeasureTheory
open GammaDeficit (lineDensity lineDensity_exp_integrable lineDensity_exp_integral)
open GammaMeasure (imageDensity imageDensity_pos imageDensity_two imageDensity_div_antitone
  imageDensity_div_lineDensity_strictMono lineDensity_pos
  imagePotential imagePotential_integrable imageSlope imageSlope_integrable imageSelf imageSelf_pos)

theorem imageSlope_elasticity {p L : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hL : 0 < L) :
    p * imagePotential p L 1 ≤ imageSlope p L 1 ∧
    imageSlope p L 1 ≤ 2 * imagePotential p L 1 := by
  let d (s : ℝ) := imageDensity p L s * Real.exp (-s)
  let d₀ (a s : ℝ) := lineDensity a s * Real.exp (-s)
  have hp₀ := zero_lt_one.trans_le hp
  have hI : IntegrableOn d (Ioi 0) := by simpa only [d,mul_one] using imagePotential_integrable hp₀ hL zero_lt_one
  have hT : IntegrableOn (fun s => d s * s) (Ioi 0) := by
    simpa only [d,mul_one,mul_right_comm] using imageSlope_integrable hp₀ hL zero_lt_one
  have hD : (∫ s : ℝ in Ioi 0, d s) = imagePotential p L 1 := by unfold d imagePotential; simp only [mul_one]
  have hDT : (∫ s : ℝ in Ioi 0, d s * s) = imageSlope p L 1 := by
    unfold d imageSlope
    simp only [mul_one,mul_right_comm]
  have hRef {a : ℝ} (ha : 0 < a) :
      IntegrableOn (d₀ a) (Ioi 0) ∧ (∫ s : ℝ in Ioi 0, d₀ a s) = 1 ∧
      IntegrableOn (fun s => d₀ a s * s) (Ioi 0) ∧ (∫ s : ℝ in Ioi 0, d₀ a s * s) = a := by
    have hA : 0 < a + 1 := by positivity
    have hS (s : ℝ) (hs : 0 < s) : d₀ a s * s = a * d₀ (a + 1) s := by
      unfold d₀ lineDensity
      rw [add_sub_cancel_right,Real.Gamma_add_one ha.ne',
        show s ^ a = s ^ (a - 1) * s by rw [← Real.rpow_add_one hs.ne',sub_add_cancel]]
      field_simp [ha.ne',(Real.Gamma_pos_of_pos ha).ne']
    have hJ : IntegrableOn (fun s => d₀ a s * s) (Ioi 0) := by
      have hK : IntegrableOn (d₀ (a + 1)) (Ioi 0) := by
        simpa only [d₀,mul_one] using lineDensity_exp_integrable hA zero_lt_one
      apply (hK.const_mul a).congr
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
      exact (hS s hs).symm
    have hM : (∫ s : ℝ in Ioi 0, d₀ a s * s) = a := by
      rw [setIntegral_congr_fun measurableSet_Ioi (fun s hs => hS s hs),integral_const_mul]
      have hE : (∫ s : ℝ in Ioi 0, d₀ (a + 1) s) = 1 := by
        simpa only [d₀,mul_one,Real.one_rpow] using lineDensity_exp_integral hA zero_lt_one
      rw [hE,mul_one]
    exact ⟨by simpa only [d₀,mul_one] using lineDensity_exp_integrable ha zero_lt_one,
      by simpa only [d₀,mul_one,Real.one_rpow] using lineDensity_exp_integral ha zero_lt_one,
      by simpa only [d₀,mul_right_comm] using hJ,
      by simpa only [d₀,mul_right_comm] using hM⟩
  have hRatio (a s : ℝ) : d s / d₀ a s = imageDensity p L s / lineDensity a s := by
    unfold d d₀
    exact mul_div_mul_right _ _ (Real.exp_pos _).ne'
  have hRatioP : MonotoneOn (fun s => d s / d₀ p s) (Ioi 0) := by
    intro s hs t ht h
    dsimp only
    rw [hRatio,hRatio]
    rcases hp₂.eq_or_lt with rfl | hp₂'
    · have h₂ (x : ℝ) : lineDensity 2 x = x := by norm_num [lineDensity,Real.Gamma_two]
      rw [imageDensity_two hL hs,imageDensity_two hL ht,h₂,h₂,
        div_self (show 0 < s from hs).ne',div_self (show 0 < t from ht).ne']
    · exact (imageDensity_div_lineDensity_strictMono hp hp₂' hL).monotoneOn hs ht h
  have hRatioTwo : AntitoneOn (fun s => d s / d₀ 2 s) (Ioi 0) := by
    intro s hs t ht h
    dsimp only
    rw [hRatio,hRatio]
    have h₂ (x : ℝ) : lineDensity 2 x = x := by norm_num [lineDensity,Real.Gamma_two]
    rw [h₂,h₂]
    exact imageDensity_div_antitone hp₀ hp₂ hL hs ht h
  have hPos {a : ℝ} (ha : 0 < a) (s : ℝ) (hs : 0 < s) : 0 < d₀ a s :=
    mul_pos (lineDensity_pos ha hs) (Real.exp_pos _)
  obtain ⟨h₁,h₂,h₃,h₄⟩ := hRef hp₀
  obtain ⟨h₅,h₆,h₇,h₈⟩ := hRef (by norm_num : (0 : ℝ) < 2)
  have hMono : MonotoneOn (fun s : ℝ => s) (Ioi 0) := by intro s hs t ht h; exact h
  have hP := likelihood_test_mono h₁ hI h₃ hT (hPos hp₀) hRatioP hMono
  have hPosD (s : ℝ) (hs : 0 < s) : 0 < d s :=
    mul_pos (imageDensity_pos hp₀ hL hs) (Real.exp_pos _)
  have hRatioInv : MonotoneOn (fun s => d₀ 2 s / d s) (Ioi 0) := by
    intro s hs t ht h
    dsimp only
    simpa only [inv_div] using (inv_le_inv₀ (div_pos (hPosD s hs) (hPos (a := 2) (by norm_num) s hs))
      (div_pos (hPosD t ht) (hPos (a := 2) (by norm_num) t ht))).mpr (hRatioTwo hs ht h)
  have hTwo := likelihood_test_mono hI h₅ hT h₇ hPosD hRatioInv hMono
  rw [h₂,h₄,hD,hDT,mul_one] at hP
  rw [h₆,h₈,hD,hDT,mul_one] at hTwo
  exact ⟨hP,hTwo⟩

theorem imageSlope_lt_double_corrected {p L : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hL : 0 < L) :
    imageSlope p L 1 < 2 * (imagePotential p L 1 + imageSelf p L) := by
  have h := (imageSlope_elasticity hp hp₂ hL).2
  linarith only [h,imageSelf_pos (zero_lt_one.trans_le hp) hL]

end ACS12.Pressure

import ACS12.OrdinaryGammaOrder
import ACS12.GammaArgumentCore

/-! The normalized Gamma spectral order follows directly from the ordinary beta integral. -/
namespace ACS12.GammaMeasure

theorem gammaNormalizedRatio_nonneg (q x : ℝ) : 0 ≤ gammaNormalizedRatio q x := by
  unfold gammaNormalizedRatio
  positivity

theorem gammaNormalizedRatio_mono {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (x : ℝ) :
    gammaNormalizedRatio s x ≤ gammaNormalizedRatio t x := by
  have ht := hs.trans_le hst
  have h := normalizedGammaModulus_mono (ξ := x) hs hst
  have hZero (q : ℝ) (hq : 0 < q) :
      ‖Complex.Gamma (gammaArgument q 0)‖ = Real.Gamma q := by
    simp only [gammaArgument,Complex.ofReal_zero,zero_mul,add_zero,Complex.Gamma_ofReal,Complex.norm_real]
    exact Real.norm_of_nonneg (Real.Gamma_pos_of_pos hq).le
  have hSq : (‖Complex.Gamma (gammaArgument s x)‖/Real.Gamma s)^2 ≤
      (‖Complex.Gamma (gammaArgument t x)‖/Real.Gamma t)^2 := by
    exact pow_le_pow_left₀ (div_nonneg (norm_nonneg _) (Real.Gamma_pos_of_pos hs).le) h 2
  unfold gammaNormalizedRatio
  rw [hZero s hs,hZero t ht]
  exact div_le_div_of_nonneg_right hSq (sq_nonneg _)

theorem gammaNormalizedRatio_zero {q : ℝ} (hq : 0 < q) :
    gammaNormalizedRatio q 0 = 1 := by
  unfold gammaNormalizedRatio
  rw [div_self (norm_gamma_argument_ne hq 0),div_self (norm_gamma_argument_ne zero_lt_one 0)]
  norm_num

end ACS12.GammaMeasure

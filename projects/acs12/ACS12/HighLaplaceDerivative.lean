import ACS12.GammaSourceElasticity

/-! Differentiability of every complete original source Laplace moment. -/
namespace ACS12.GammaMeasure

open Set Filter MeasureTheory CenteredCircle.AllN

theorem sourceLaplaceMoment_deriv {p L t : ℝ} (hp : 0 < p) (hL : 0 < L) (ht : 0 < t) (j : ℕ) :
    HasDerivAt (sourceLaplaceMoment p L j) (-sourceLaplaceMoment p L (j + 1) t) t := by
  let c := t / 2
  let g (s : ℝ) := imageDensity p L s * s ^ j * Real.exp (-s * c)
  have hc : 0 < c := half_pos ht
  obtain ⟨C,hC,hB⟩ := Pressure.imageDensity_linear_exp_bound hp hL hc
  have hM : Measurable g := by unfold g; exact
    (((continuous_imageDensity hp hL).measurable.mul (measurable_id.pow_const j)).mul (by fun_prop))
  have hBound (s : ℝ) (hs : 0 < s) : |g s| ≤ C * s ^ (j + 1) := by
    have hExp : Real.exp (c * s) * Real.exp (-s * c) = 1 := by
      rw [← Real.exp_add,show c * s + -s * c = 0 by ring,Real.exp_zero]
    have h := mul_le_mul_of_nonneg_right (hB s hs)
      (show 0 ≤ s ^ j * Real.exp (-s * c) by positivity)
    have hg₀ : 0 ≤ g s := by
      unfold g
      exact mul_nonneg (mul_nonneg (imageDensity_pos hp hL hs).le (pow_nonneg hs.le _)) (Real.exp_pos _).le
    rw [abs_of_nonneg hg₀]
    calc
      _ ≤ (C * s * Real.exp (c * s)) * (s ^ j * Real.exp (-s * c)) := by simpa only [g,mul_assoc] using h
      _ = C * s ^ (j + 1) * (Real.exp (c * s) * Real.exp (-s * c)) := by rw [pow_succ]; ring
      _ = _ := by rw [hExp,mul_one]
  have h := hasDerivAt_weighted_laplace g C (j + 1) hM hC hBound
    (show 0 < t - c by unfold c; linarith only [ht])
  have hComp := h.comp t ((hasDerivAt_id t).sub_const c)
  have hFun (u : ℝ) :
      (∫ s : ℝ in Ioi 0, g s * Real.exp (-s * (u - c))) = sourceLaplaceMoment p L j u := by
    unfold sourceLaplaceMoment
    apply integral_congr_ae
    exact Eventually.of_forall fun s => by
      have hE : Real.exp (-s * c) * Real.exp (-s * (u - c)) = Real.exp (-s * u) := by
        rw [← Real.exp_add]
        congr 1
        ring
      dsimp only [g]
      rw [mul_assoc, hE]
  have hVal :
      (∫ s : ℝ in Ioi 0, s * g s * Real.exp (-s * (t - c))) =
        sourceLaplaceMoment p L (j + 1) t := by
    unfold sourceLaplaceMoment
    apply integral_congr_ae
    exact Eventually.of_forall fun s => by
      have hE : Real.exp (-s * c) * Real.exp (-s * (t - c)) = Real.exp (-s * t) := by
        rw [← Real.exp_add]
        congr 1
        ring
      dsimp only [g]
      calc
        _ = imageDensity p L s * s ^ (j + 1) * (Real.exp (-s * c) * Real.exp (-s * (t - c))) := by rw [pow_succ]; ring
        _ = _ := by rw [hE]
  simp only [Function.comp_def,hFun,mul_one,hVal] at hComp
  exact hComp

end ACS12.GammaMeasure

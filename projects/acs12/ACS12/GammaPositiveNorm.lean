import ACS12.OrdinaryGammaTail

/-! The positive-axis Euler integral supplies the uniform bounded-frequency Gamma estimate. -/
namespace ACS12.GammaMeasure
open Set MeasureTheory

theorem norm_Gamma_le_realGamma {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz,Real.Gamma_eq_integral hz]
  unfold Complex.GammaIntegral
  calc
    _ ≤ ∫ x : ℝ in Ioi 0, ‖(Real.exp (-x):ℂ)*(x:ℂ)^(z-1)‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [norm_mul,Complex.norm_of_nonneg (Real.exp_pos _).le,
        Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp

theorem realGamma_compact_bound {a b : ℝ} (ha : 0 < a) :
    ∃ C > 0, ∀ s ∈ Icc a b, Real.Gamma s ≤ C := by
  have hCont : ContinuousOn Real.Gamma (Icc a b) := by
    intro x hx
    exact (Real.differentiableOn_Gamma_Ioi x (ha.trans_le hx.1)).continuousWithinAt.mono
      (fun y hy => ha.trans_le hy.1)
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hCont
  exact ⟨max C 1,lt_of_lt_of_le zero_lt_one (le_max_right C 1),fun s hs =>
    (le_abs_self _).trans ((hC s hs).trans (le_max_left C 1))⟩

end ACS12.GammaMeasure

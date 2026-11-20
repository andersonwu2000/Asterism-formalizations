import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Original Gamma arguments and normalized moduli are shared independently of spectral partial fractions. -/
namespace ACS12.GammaMeasure
set_option backward.isDefEq.respectTransparency false

noncomputable def gammaArgument (q t : ℝ) : ℂ :=
  (q : ℂ) + (t : ℂ) * Complex.I

@[simp] theorem gammaArgument_re (q t : ℝ) : (gammaArgument q t).re = q := by
  simp [gammaArgument, Complex.mul_re]

noncomputable def gammaNormalizedRatio (q x : ℝ) : ℝ :=
  (‖Complex.Gamma (gammaArgument q x)‖ / ‖Complex.Gamma (gammaArgument q 0)‖) ^ 2 /
    (‖Complex.Gamma (gammaArgument 1 x)‖ / ‖Complex.Gamma (gammaArgument 1 0)‖) ^ 2

theorem norm_gamma_argument_ne {q : ℝ} (hq : 0 < q) (x : ℝ) :
    ‖Complex.Gamma (gammaArgument q x)‖ ≠ 0 :=
  norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by simpa only [gammaArgument_re] using hq))

noncomputable def gammaModulusRatio (q x : ℝ) : ℝ :=
  ‖Complex.Gamma (gammaArgument q x)‖ ^ 2 / ‖Complex.Gamma (gammaArgument 1 x)‖ ^ 2

private theorem gamma_argument_zero_norm {q : ℝ} (hq : 0 < q) :
    ‖Complex.Gamma (gammaArgument q 0)‖ = Real.Gamma q := by
  have h : gammaArgument q 0 = (q : ℂ) := by simp [gammaArgument]
  rw [h,Complex.Gamma_ofReal,Complex.norm_real,Real.norm_of_nonneg (Real.Gamma_pos_of_pos hq).le]

theorem gammaModulusRatio_eq_normalized {q : ℝ} (hq : 0 < q) (x : ℝ) :
    gammaModulusRatio q x = Real.Gamma q ^ 2 * gammaNormalizedRatio q x := by
  unfold gammaModulusRatio gammaNormalizedRatio
  rw [gamma_argument_zero_norm hq,gamma_argument_zero_norm zero_lt_one,Real.Gamma_one,div_one,div_pow]
  field_simp [(Real.Gamma_pos_of_pos hq).ne',norm_gamma_argument_ne zero_lt_one x]

theorem gammaModulusRatio_recurrence {q : ℝ} (hq : 0 < q) (x : ℝ) :
    gammaModulusRatio (q + 1) x = (x ^ 2 + q ^ 2) * gammaModulusRatio q x := by
  have hArg : gammaArgument (q + 1) x = gammaArgument q x + 1 := by
    unfold gammaArgument
    push_cast
    ring
  have hArgNe : gammaArgument q x ≠ 0 := by
    intro h
    have hRe := congrArg Complex.re h
    simp only [gammaArgument_re,Complex.zero_re] at hRe
    exact hq.ne' hRe
  have hNorm : ‖gammaArgument q x‖ ^ 2 = q ^ 2 + x ^ 2 := by
    simp only [←Complex.normSq_eq_norm_sq,Complex.normSq_apply,gammaArgument,
      Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,Complex.mul_re,
      Complex.mul_im,Complex.I_re,Complex.I_im]
    ring
  unfold gammaModulusRatio
  rw [hArg,Complex.Gamma_add_one _ hArgNe,norm_mul,mul_pow,hNorm]
  ring

end ACS12.GammaMeasure

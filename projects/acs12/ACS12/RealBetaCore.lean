import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! The complete positive ordinary beta integral is a shared primitive. -/
namespace ACS12.GammaDeficit
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

noncomputable def betaKernel (a b x : ℝ) : ℝ := x ^ (a - 1) * (1 - x) ^ (b - 1)

noncomputable def betaReal (a b : ℝ) : ℝ := Real.Gamma a * Real.Gamma b / Real.Gamma (a + b)

theorem betaReal_eq_integral {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x : ℝ in Ioo 0 1, betaKernel a b x) = betaReal a b := by
  apply Complex.ofReal_inj.mp
  have h : (∫ x : ℝ in Ioo 0 1, (betaKernel a b x : ℂ)) = Complex.betaIntegral a b := by
    rw [Complex.betaIntegral,intervalIntegral.integral_of_le (by norm_num),integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    have hx₀ : 0 < x := hx.1
    have hx₁ : 0 < 1 - x := sub_pos.mpr hx.2
    simp only [betaKernel]
    rw [Complex.ofReal_mul,Complex.ofReal_cpow hx₀.le,Complex.ofReal_cpow hx₁.le,
      Complex.ofReal_sub,Complex.ofReal_sub,Complex.ofReal_sub,Complex.ofReal_one]
  calc
    Complex.ofReal (∫ x : ℝ in Ioo 0 1, betaKernel a b x) =
        (∫ x : ℝ in Ioo 0 1, (betaKernel a b x : ℂ)) := (integral_ofReal (𝕜 := ℂ)).symm
    _ = _ := by
      rw [h,Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simpa only [Complex.ofReal_re] using ha)
        (by simpa only [Complex.ofReal_re] using hb),← Complex.ofReal_add,Complex.Gamma_ofReal,
        Complex.Gamma_ofReal,Complex.Gamma_ofReal]
      unfold betaReal
      push_cast
      rfl

theorem betaKernel_integrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (betaKernel a b) (Ioo 0 1) := by
  apply Integrable.of_integral_ne_zero
  rw [betaReal_eq_integral ha hb]
  exact (div_pos (mul_pos (Real.Gamma_pos_of_pos ha) (Real.Gamma_pos_of_pos hb))
    (Real.Gamma_pos_of_pos (add_pos ha hb))).ne'

end ACS12.GammaDeficit

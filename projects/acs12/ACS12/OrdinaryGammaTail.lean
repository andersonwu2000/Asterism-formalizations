import ACS12.OrdinaryGammaPolynomial
import ACS12.GammaUnitTail
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-! The selected ordinary-Beta tail, uniformly over every compact positive shape interval. -/
namespace ACS12.GammaMeasure
open Set
set_option backward.isDefEq.respectTransparency false

theorem gamma_shape_tail {s t : ℝ} (hs : 0 < s) (k : ℕ) (hsk : s ≤ (k+1:ℕ))
    (ht : 1 ≤ |t|) :
    ‖Complex.Gamma (gammaArgument s t)‖ ≤
      (Real.Gamma s*gammaUnitTailConstant)*(1+|t|)^(k+1)*Real.exp (-Real.pi*|t|/2) := by
  have hU := gammaUnit_tail ht
  rw [gammaUnit_norm_abs] at hU
  have hBound := (gamma_shape_integer_bound hs k hsk).trans
    (mul_le_mul_of_nonneg_left hU (by positivity : 0 ≤ Real.Gamma s*(1+|t|)^k))
  have hAbs : |t| ≤ 1+|t| := by linarith
  calc
    _ ≤ Real.Gamma s*(1+|t|)^k*(gammaUnitTailConstant*|t| *Real.exp (-Real.pi*|t|/2)) := hBound
    _ ≤ Real.Gamma s*(1+|t|)^k*(gammaUnitTailConstant*(1+|t|)*Real.exp (-Real.pi*|t|/2)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAbs gammaUnitTailConstant_pos.le)
          (Real.exp_pos _).le) (by positivity)
    _ = _ := by rw [pow_succ]; ring

theorem gamma_compact_shape_tail {a b : ℝ} (ha : 0 < a) :
    ∃ C > 0, ∃ k : ℕ, ∀ s ∈ Icc a b, ∀ t : ℝ, 1 ≤ |t| →
      ‖Complex.Gamma (gammaArgument s t)‖ ≤ C*(1+|t|)^k*Real.exp (-Real.pi*|t|/2) := by
  have hCont : ContinuousOn Real.Gamma (Icc a b) := by
    intro x hx
    exact (Real.differentiableOn_Gamma_Ioi x (ha.trans_le hx.1)).continuousWithinAt.mono
      (fun y hy => ha.trans_le hy.1)
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hCont
  obtain ⟨k,hk⟩ := exists_nat_gt b
  refine ⟨(max B 1)*gammaUnitTailConstant, mul_pos (lt_of_lt_of_le zero_lt_one (le_max_right B 1))
    gammaUnitTailConstant_pos,k+1,?_⟩
  intro s hs t ht
  have hs₀ : 0 < s := ha.trans_le hs.1
  have hSk : s ≤ (k+1:ℕ) := by
    have hk' : b < (k:ℝ) := hk
    push_cast
    linarith only [hs.2,hk']
  have hG : Real.Gamma s ≤ max B 1 :=
    (le_abs_self _).trans ((hB s hs).trans (le_max_left B 1))
  exact (gamma_shape_tail hs₀ k hSk ht).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hG gammaUnitTailConstant_pos.le) (by positivity))
      (Real.exp_pos _).le)

end ACS12.GammaMeasure

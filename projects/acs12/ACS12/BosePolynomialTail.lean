import ACS12.ComplexBoseCore
import ACS12.BoseWeightBounds
import ACS12.PowerSine

/-! A full polynomial-exponential Bose envelope is integrable away from zero. -/
namespace ACS12.NativeCells
open Set MeasureTheory

theorem integrableOn_bosePolynomialTail {d : ℝ} (hd : 0 < d) (k : ℕ) :
    IntegrableOn (fun ξ : ℝ => (1+ξ)^k*Real.exp (-d*ξ)) (Ioi 1) := by
  have hI : IntegrableOn (fun ξ : ℝ => ξ^k*Real.exp (-d*ξ)) (Ioi 0) := by
    have h := GammaDeficit.integrable_gamma_exp (a := (k:ℝ)+1) (by positivity) hd
    simpa only [add_sub_cancel_right,Real.rpow_natCast] using h
  have hSub : Ioi (1:ℝ) ⊆ Ioi (0:ℝ) := by
    intro ξ hξ
    change 0 < ξ
    exact zero_lt_one.trans hξ
  have hI' : IntegrableOn (fun ξ : ℝ => (2:ℝ)^k*(ξ^k*Real.exp (-d*ξ))) (Ioi 1) :=
    (hI.mono_set hSub).const_mul _
  apply hI'.mono' (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
  have hξ₀ : 0 ≤ ξ := (zero_lt_one.trans hξ).le
  rw [Real.norm_of_nonneg (by positivity)]
  have hPow : (1+ξ)^k ≤ (2*ξ)^k := by
    apply pow_le_pow_left₀ (by positivity)
    change 1 < ξ at hξ
    linarith only [hξ]
  rw [mul_pow] at hPow
  nlinarith [mul_le_mul_of_nonneg_right hPow (Real.exp_pos (-d*ξ)).le]

end ACS12.NativeCells

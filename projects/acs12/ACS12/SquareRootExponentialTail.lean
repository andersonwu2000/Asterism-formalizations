import ACS12.PositiveSquareSubstitution
import ACS12.PowerSine

/-! Any finite real power is integrable against the full exponential square-root tail away from zero. -/
namespace ACS12
open MeasureTheory Set Filter

theorem integrableOn_rpow_exp_neg_sqrt {q c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t^q*Real.exp (-c*Real.sqrt t)) (Ioi 1) := by
  let R := max q 0
  let g (t : ℝ) := t^R*Real.exp (-c*Real.sqrt t)
  have hR : 0 ≤ R := le_max_right _ _
  have hRq : q ≤ R := le_max_left _ _
  have hGamma : IntegrableOn
      (fun v : ℝ => v^(2*R+1)*Real.exp (-c*v)) (Ioi 0) := by
    simpa only [show 2*R+2-1 = 2*R+1 by ring] using
      GammaDeficit.integrable_gamma_exp (a := 2*R+2) (by linarith only [hR]) hc
  have hPoint (v : ℝ) (hv : 0 < v) :
      2*v*g (v^2) = 2*(v^(2*R+1)*Real.exp (-c*v)) := by
    have hPow : (v^2)^R = v^(2*R) := by
      rw [show v^2 = v^(2:ℝ) by rw [Real.rpow_two],← Real.rpow_mul hv.le]
    have hPow₁ : v^(2*R+1) = v^(2*R)*v := Real.rpow_add_one hv.ne' (2*R)
    unfold g
    rw [Real.sqrt_sq hv.le,hPow,hPow₁]
    ring
  have hI : IntegrableOn g (Ioi 0) := by
    apply (integrableOn_positiveSquare_iff g).mpr
    apply (hGamma.const_mul (2:ℝ)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact (hPoint v hv).symm
  have hI' : IntegrableOn g (Ioi 1) := hI.mono_set (fun t ht => by
    change 0<t
    have ht₀ : 1<t := ht
    linarith only [ht₀])
  apply hI'.mono' (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht₁ : 1<t := ht
  have ht₀ : 0<t := zero_lt_one.trans ht₁
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht₀.le _) (Real.exp_pos _).le)]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le ht₁.le hRq) (Real.exp_pos _).le

end ACS12

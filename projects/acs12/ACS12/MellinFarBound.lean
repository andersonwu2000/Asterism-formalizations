import ACS12.MellinPhiBounds

/-! A single uniform positive-shape bound controls the entire actual complex Mellin tail. -/
namespace ACS12.NativeCells
open MeasureTheory ProbabilityTheory Set

noncomputable def mellinFarConstant (ε : ℝ) : ℝ := ((1-Real.exp (-1))⁻¹)^ε

theorem mellinFarConstant_pos (ε : ℝ) : 0 < mellinFarConstant ε := by
  unfold mellinFarConstant
  exact Real.rpow_pos_of_pos (inv_pos.mpr (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num)))) ε

theorem mellinPhi_rpow_tail {ε t : ℝ} (hε : 0 < ε) (ht : 1 ≤ t) :
    (mellinPhi t)^ε ≤ mellinFarConstant ε*t^(ε/2)*Real.exp (-(ε/2)*Real.sqrt t) := by
  have ht₀ : 0 < t := zero_lt_one.trans_le ht
  have hK : 0 < (1-Real.exp (-1))⁻¹ :=
    inv_pos.mpr (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num)))
  have h := Real.rpow_le_rpow (mellinPhi_pos ht₀).le (mellinPhi_tail ht) hε.le
  have hEq : ((1-Real.exp (-1))⁻¹*Real.sqrt t*Real.exp (-Real.sqrt t/2))^ε =
      mellinFarConstant ε*t^(ε/2)*Real.exp (-(ε/2)*Real.sqrt t) := by
    rw [Real.mul_rpow (mul_nonneg hK.le (Real.sqrt_nonneg t)) (Real.exp_pos _).le,
      Real.mul_rpow hK.le (Real.sqrt_nonneg t)]
    have hSqrt : (Real.sqrt t)^ε = t^(ε/2) := by
      rw [Real.sqrt_eq_rpow,← Real.rpow_mul ht₀.le]
      congr 1
      ring
    have hExp : (Real.exp (-Real.sqrt t/2))^ε = Real.exp (-(ε/2)*Real.sqrt t) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
      congr 1
      ring
    rw [hSqrt,hExp]
    rfl
  exact h.trans_eq hEq

theorem mellinFar_norm_bound {α h : ℂ} {z ε B t : ℝ} (hz : 0 ≤ z)
    (hε : 0 < ε) (hα : ε ≤ α.re) (hh : -B ≤ h.re) (ht : 1 ≤ t) :
    ‖(t:ℂ)^(-h-1)*jointLaplaceCarrier α z (t:ℂ)‖ ≤
      mellinFarConstant ε*t^(B+ε/2)*Real.exp (-(ε/2)*Real.sqrt t) := by
  have ht₀ : 0 < t := zero_lt_one.trans_le ht
  have hWeight : t^((-h-1).re) ≤ t^B := by
    apply Real.rpow_le_rpow_of_exponent_le ht
    simp only [Complex.sub_re,Complex.neg_re,Complex.one_re]
    linarith only [hh]
  have hCarrier : ‖jointLaplaceCarrier α z (t:ℂ)‖ ≤ (mellinPhi t)^ε :=
    (jointLaplaceCarrier_norm_le hz ht₀).trans
      (Real.rpow_le_rpow_of_exponent_ge (mellinPhi_pos ht₀) (mellinPhi_le_one ht₀) hα)
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ht₀]
  have h := mul_le_mul hWeight
    (hCarrier.trans (mellinPhi_rpow_tail hε ht)) (norm_nonneg _) (Real.rpow_nonneg ht₀.le B)
  convert h using 1
  rw [Real.rpow_add ht₀]
  ring

end ACS12.NativeCells

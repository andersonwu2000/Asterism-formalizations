import ACS12.HighCurrentKernel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The whole finite two-half-circle hump integral, with its exact correlated moment. -/
namespace ACS12.HighCurrent

open MeasureTheory Set

theorem complete_current_hump_integral {τ x : ℝ} (hτ : 0 < τ) (hx : 0 < x) :
    2 * (∫ z in (0 : ℝ)..τ, τ * z ^ 3 * (τ - z) / (x + z ^ 2)) ≤
      τ ^ 6 / (10 * x + 3 * τ ^ 2) := by
  let μ := 3 * τ ^ 2 / 10
  let c := μ / (x + μ)
  let d := x / (x + μ) ^ 2
  let upper (z : ℝ) := τ * z * (τ - z) * (c + d * (z ^ 2 - μ))
  let primitive (z : ℝ) :=
    c * (τ ^ 2 * z ^ 2 / 2 - τ * z ^ 3 / 3) +
      d * (τ ^ 2 * z ^ 4 / 4 - τ * z ^ 5 / 5 -
        μ * (τ ^ 2 * z ^ 2 / 2 - τ * z ^ 3 / 3))
  have hμ : 0 ≤ μ := by unfold μ; positivity
  have hI : IntervalIntegrable (fun z : ℝ => τ * z ^ 3 * (τ - z) / (x + z ^ 2)) volume 0 τ :=
    ((by fun_prop : Continuous (fun z : ℝ => τ * z ^ 3 * (τ - z))).div
      (by fun_prop : Continuous (fun z : ℝ => x + z ^ 2))
      (fun z => (show 0 < x + z ^ 2 by positivity).ne')).intervalIntegrable _ _
  have hU : IntervalIntegrable upper volume 0 τ :=
    (by unfold upper; fun_prop : Continuous upper).intervalIntegrable _ _
  have hD (z : ℝ) : HasDerivAt primitive (upper z) z := by
    have h₂ := (((hasDerivAt_id z).pow 2).const_mul (τ ^ 2)).div_const 2
    have h₃ := (((hasDerivAt_id z).pow 3).const_mul τ).div_const 3
    have h₄ := (((hasDerivAt_id z).pow 4).const_mul (τ ^ 2)).div_const 4
    have h₅ := (((hasDerivAt_id z).pow 5).const_mul τ).div_const 5
    convert ((h₂.sub h₃).const_mul c).add
      (((h₄.sub h₅).sub ((h₂.sub h₃).const_mul μ)).const_mul d) using 1
    simp only [id_eq,Pi.pow_apply,pow_one,one_mul,upper]
    ring
  have hIntegral := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => hD z) hU
  have hValue : 2 * (∫ z in (0 : ℝ)..τ, upper z) = τ ^ 6 / (10 * x + 3 * τ ^ 2) := by
    rw [hIntegral]
    unfold primitive c d μ
    norm_num only [zero_pow (by decide : (2 : ℕ) ≠ 0),zero_pow (by decide : (3 : ℕ) ≠ 0),
      zero_pow (by decide : (4 : ℕ) ≠ 0),zero_pow (by decide : (5 : ℕ) ≠ 0),mul_zero,zero_div,sub_zero,sub_self,add_zero]
    field_simp [show x + 3 * τ ^ 2 / 10 ≠ 0 by positivity,
      show 10 * x + 3 * τ ^ 2 ≠ 0 by positivity,
      show 10 * x + τ ^ 2 * 3 ≠ 0 by positivity]
    <;> ring
  have hCmp : (∫ z in (0 : ℝ)..τ, τ * z ^ 3 * (τ - z) / (x + z ^ 2)) ≤
      ∫ z in (0 : ℝ)..τ, upper z := by
    apply intervalIntegral.integral_mono_on hτ.le hI hU
    intro z hz
    have hWeight : 0 ≤ τ * z * (τ - z) :=
      mul_nonneg (mul_nonneg hτ.le hz.1) (sub_nonneg.mpr hz.2)
    have h := mul_le_mul_of_nonneg_left (current_rational_tangent hx hμ (sq_nonneg z)) hWeight
    unfold upper c d
    convert h using 1
    ring
  have hScaled := mul_le_mul_of_nonneg_left hCmp (by norm_num : (0 : ℝ) ≤ 2)
  rwa [hValue] at hScaled

end ACS12.HighCurrent

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-! A genuine positive exponential moment pays every finite nonnegative real power. -/
namespace ACS12
open MeasureTheory Filter

theorem integrable_rpow_of_exponential {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : Measurable X) (hPos : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    {c : ℝ} (hc : 0 < c) (hExp : Integrable (fun ω => Real.exp (c*X ω)) μ)
    {r : ℝ} (hr : 0 ≤ r) : Integrable (fun ω => X ω^r) μ := by
  obtain ⟨k,hk⟩ := exists_nat_gt r
  let C : ℝ := (k.factorial:ℝ)/c^k
  have hC : 0 ≤ C := by unfold C; positivity
  have hPower (x : ℝ) (hx : 0 ≤ x) : x^k ≤ C*Real.exp (c*x) := by
    have h := Real.pow_div_factorial_le_exp (c*x) (mul_nonneg hc.le hx) k
    rw [mul_pow] at h
    have h' := (div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos k))).mp h
    have hId : C*Real.exp (c*x) = (Real.exp (c*x)*(k.factorial:ℝ))/c^k := by unfold C; ring
    rw [hId]
    apply (le_div_iff₀ (pow_pos hc k)).mpr
    nlinarith only [h']
  have hBound (x : ℝ) (hx : 0 ≤ x) : x^r ≤ 1+C*Real.exp (c*x) := by
    by_cases hx₁ : x ≤ 1
    · exact (Real.rpow_le_one hx hx₁ hr).trans (le_add_of_nonneg_right (mul_nonneg hC (Real.exp_pos _).le))
    · have hx₁ : 1 ≤ x := (lt_of_not_ge hx₁).le
      have h := Real.rpow_le_rpow_of_exponent_le hx₁ hk.le
      rw [Real.rpow_natCast] at h
      exact h.trans ((hPower x hx).trans (le_add_of_nonneg_left zero_le_one))
  apply ((integrable_const (1:ℝ)).add (hExp.const_mul C)).mono' (hX.pow_const r).aestronglyMeasurable
  filter_upwards [hPos] with ω hω
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hω r)]
  exact hBound _ hω

end ACS12

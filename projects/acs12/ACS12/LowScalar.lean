import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Scalar components of the selected low-power Mellin argument. -/

namespace ACS12.LowScalar

open MeasureTheory Set

def massPolynomial (p b : ℝ) : ℝ :=
  (3 * p + 6) * b ^ 3 + 2 * p * b ^ 2 + (p - 4) * b - 2

theorem massPolynomial_one_at_two_thirds : massPolynomial 1 (2 / 3) = -4 / 9 := by
  norm_num [massPolynomial]

/-- The actual finite-row estimate has to establish positivity of this
polynomial. Its numerical consequence follows by a direct factorization. -/
theorem two_thirds_lt_of_massPolynomial_pos {p b : ℝ} (hp : p ≤ 1) (hb : 0 < b)
    (hQ : 0 < massPolynomial p b) : 2 / 3 < b := by
  have hQp : massPolynomial 1 b - massPolynomial p b =
      (1 - p) * (3 * b ^ 3 + 2 * b ^ 2 + b) := by
    unfold massPolynomial
    ring
  have hQle : massPolynomial p b ≤ massPolynomial 1 b := by
    rw [← sub_nonneg, hQp]
    exact mul_nonneg (sub_nonneg.mpr hp) (by positivity)
  have hQ1 : massPolynomial 1 b =
      (b - 2 / 3) * (9 * b ^ 2 + 8 * b + 7 / 3) - 4 / 9 := by
    unfold massPolynomial
    ring
  by_contra! h
  have hprod := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h)
    (show 0 ≤ 9 * b ^ 2 + 8 * b + 7 / 3 by positivity)
  linarith

/-- The closed expression in the literal-one scalar evaluation is negative.
The two rational upper bounds here follow from Mathlib's checked bounds. -/
theorem endpoint_expression_lt :
    11 * Real.pi ^ 2 / 48 + (5 / 2) * Real.log 2 - 4 < -(41 / 29400) := by
  have hπ : Real.pi < 22 / 7 := by linarith [Real.pi_lt_d4]
  have hlog : Real.log 2 < 347 / 500 := by linarith [Real.log_two_lt_d9]
  have hπsq : Real.pi ^ 2 < (22 / 7 : ℝ) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hπ) (show 0 < 22 / 7 + Real.pi by positivity)]
  linarith

/-- Mellin transport across a negative-to-positive crossing. This lemma
compares the weighted and unweighted signed integrals on the same measure. -/
theorem mellin_crossing_bound {μ : Measure ℝ} {f : ℝ → ℝ} {c p : ℝ} (hc : 0 < c) (hp : p ≤ 1)
    (hf : IntegrableOn f (Ioi 0) μ)
    (hfp : IntegrableOn (fun x => x ^ (p - 1) * f x) (Ioi 0) μ)
    (hleft : ∀ x ∈ Ioo 0 c, f x ≤ 0) (hright : ∀ x ∈ Ioi c, 0 ≤ f x) :
    (∫ x in Ioi (0 : ℝ), x ^ (p - 1) * f x ∂μ) ≤
      c ^ (p - 1) * ∫ x in Ioi (0 : ℝ), f x ∂μ := by
  rw [← integral_const_mul]
  apply integral_mono_ae hfp (hf.const_mul _)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := hx
  rcases lt_trichotomy x c with h | rfl | h
  · exact mul_le_mul_of_nonpos_right (Real.rpow_le_rpow_of_nonpos hx0 h.le (sub_nonpos.mpr hp))
      (hleft x ⟨hx0, h⟩)
  · rfl
  · exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hc h.le (sub_nonpos.mpr hp))
      (hright x h)

theorem mellin_crossing_neg {μ : Measure ℝ} {f : ℝ → ℝ} {c p : ℝ} (hc : 0 < c) (hp : p ≤ 1)
    (hf : IntegrableOn f (Ioi 0) μ)
    (hfp : IntegrableOn (fun x => x ^ (p - 1) * f x) (Ioi 0) μ)
    (hleft : ∀ x ∈ Ioo 0 c, f x ≤ 0) (hright : ∀ x ∈ Ioi c, 0 ≤ f x)
    (hnegative : (∫ x in Ioi (0 : ℝ), f x ∂μ) < 0) :
    (∫ x in Ioi (0 : ℝ), x ^ (p - 1) * f x ∂μ) < 0 :=
  (mellin_crossing_bound hc hp hf hfp hleft hright).trans_lt
    (mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos hc _) hnegative)

end ACS12.LowScalar

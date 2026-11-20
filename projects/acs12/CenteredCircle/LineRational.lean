import CenteredCircle.ScalarIntegral
import CenteredCircle.ScalarCertificate

/-! The line scalar is the explicit rational series used by the exact certificate. -/

namespace CenteredCircle.AllN

open MeasureTheory Set

theorem lineKernel_a_formula {t : ℝ} (ht : 0 < t) :
    lineKernel .a t = 1 / t - 1 / (t + 1) - 1 / (t + 1) ^ 2 := by
  rw [lineKernel, laplace_density_integral (densityPolynomial .a)
    (continuous_densityPolynomial .a).measurable (fun _ hu => (densityPolynomial_pos .a hu).le)]
  simpa using integral_polyA_moment 0 ht

theorem lineKernel_b_formula {t : ℝ} (ht : 0 < t) :
    lineKernel .b t = 1 / t ^ 2 - 1 / t + 1 / (t + 1) := by
  rw [lineKernel, laplace_density_integral (densityPolynomial .b)
    (continuous_densityPolynomial .b).measurable (fun _ hu => (densityPolynomial_pos .b hu).le)]
  simpa using integral_polyB_moment 0 ht

theorem lineLeftKernel_eq_comparisonF {t : ℝ} (ht : 0 < t) : lineLeftKernel t = comparisonF t := by
  rw [lineLeftKernel, lineKernel_a_formula ht, lineKernel_b_formula ht, comparisonF]
  have ht1 : 0 < t + 1 := by linarith
  field_simp
  <;> ring

theorem lineRightKernel_eq_comparisonG {t : ℝ} (ht : 0 < t) : lineRightKernel t = comparisonG t := by
  rw [lineRightKernel, lineKernel_a_formula ht, lineKernel_b_formula ht, comparisonG]
  have ht1 : 0 < t + 1 := by linarith
  field_simp
  <;> ring

theorem comparisonF_summable {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    Summable (fun j : ℕ => comparisonF (t + j * s)) := by
  have h := (lineKernel_summable .a ht hs).sub ((lineKernel_summable .b ht hs).div_const 4)
  apply h.congr
  intro j
  exact lineLeftKernel_eq_comparisonF (by positivity)

theorem comparisonG_summable {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    Summable (fun j : ℕ => comparisonG (t + j * s)) := by
  have h := (lineKernel_summable .b ht hs).sub ((lineKernel_summable .a ht hs).div_const 4)
  apply h.congr
  intro j
  exact lineRightKernel_eq_comparisonG (by positivity)

theorem comparisonF_le_cubic {t : ℝ} (ht : 0 < t) : comparisonF t ≤ 1 / t ^ 3 := by
  have ht1 : 0 < t + 1 := by linarith
  have he : 1 / t ^ 3 - comparisonF t =
      (t ^ 2 + 9 * t + 4) / (4 * t ^ 3 * (t + 1) ^ 2) := by
    rw [comparisonF]
    field_simp
    <;> ring
  have hp : 0 ≤ (t ^ 2 + 9 * t + 4) / (4 * t ^ 3 * (t + 1) ^ 2) := by positivity
  linarith

theorem comparisonG_le_cubic {t : ℝ} (ht : 0 < t) : comparisonG t ≤ 1 / t ^ 3 := by
  have ht1 : 0 < t + 1 := by linarith
  have he : 1 / t ^ 3 - comparisonG t =
      (t + 2) ^ 2 / (4 * t ^ 3 * (t + 1) ^ 2) := by
    rw [comparisonG]
    field_simp
    <;> ring
  have hp : 0 ≤ (t + 2) ^ 2 / (4 * t ^ 3 * (t + 1) ^ 2) := by positivity
  linarith

theorem comparison_pair_cubic_bound {b t : ℝ} (hb : 0 < b) (ht : 0 < t) :
    comparisonF t + b * comparisonG (t * b) ≤ (1 + b⁻¹ ^ 2) / t ^ 3 := by
  have hF := comparisonF_le_cubic ht
  have hG := mul_le_mul_of_nonneg_left (comparisonG_le_cubic (mul_pos ht hb)) hb.le
  have he : 1 / t ^ 3 + b * (1 / (t * b) ^ 3) = (1 + b⁻¹ ^ 2) / t ^ 3 := by
    field_simp
    <;> ring
  linarith

noncomputable def rationalPair (b : ℝ) (j : ℕ) : ℝ :=
  comparisonF ((j : ℝ) + 1) + b * comparisonG (((j : ℝ) + 1) * b)

theorem rationalPair_summable {b : ℝ} (hb : 0 < b) : Summable (rationalPair b) := by
  have hF : Summable (fun j : ℕ => comparisonF ((j : ℝ) + 1)) := by
    simpa only [mul_one, add_comm] using comparisonF_summable (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1)
  have hG : Summable (fun j : ℕ => b * comparisonG (((j : ℝ) + 1) * b)) := by
    simpa only [add_mul, one_mul, add_comm] using (comparisonG_summable hb hb).mul_left b
  exact hF.add hG

theorem lineScalar_eq_rational {b : ℝ} (hb : 0 < b) :
    lineScalar b = (∑' j : ℕ, rationalPair b j) - 9 / 4 + (3 / 2) * b := by
  have hF : Summable (fun j : ℕ => comparisonF ((j : ℝ) + 1)) := by
    simpa only [mul_one, add_comm] using comparisonF_summable (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1)
  have hG : Summable (fun j : ℕ => comparisonG (((j : ℝ) + 1) * b)) := by
    simpa only [add_mul, one_mul, add_comm] using comparisonG_summable hb hb
  have heF : samplingTail lineLeftKernel 0 1 = ∑' j : ℕ, comparisonF ((j : ℝ) + 1) := by
    simp only [samplingTail, zero_add, mul_one, one_mul, Nat.cast_add, Nat.cast_one]
    apply tsum_congr
    intro j
    exact lineLeftKernel_eq_comparisonF (by positivity)
  have heG : samplingTail lineRightKernel 0 b = b * ∑' j : ℕ, comparisonG (((j : ℝ) + 1) * b) := by
    simp only [samplingTail, zero_add, Nat.cast_add, Nat.cast_one]
    congr 1
    apply tsum_congr
    intro j
    exact lineRightKernel_eq_comparisonG (by positivity)
  rw [lineScalar, heF, heG]
  change _ = (∑' j : ℕ, (comparisonF ((j : ℝ) + 1) + b * comparisonG (((j : ℝ) + 1) * b))) - _ + _
  rw [hF.tsum_add (hG.mul_left b), tsum_mul_left]
  ring

end CenteredCircle.AllN

import CenteredCircle.MixedKernelShape
import CenteredCircle.SelfImages

/-!
Newtonian specialization of the corrected scalar comparison from the
broad-power handoff. Pointwise positivity avoids differentiating the scalar
in its mass parameter. The lattice-sum/integral bridge is a separate obligation.
-/

namespace CenteredCircle.AllN

noncomputable def leftMixPolynomial (u : ℝ) : ℝ := polyA u - polyB u / 4
noncomputable def rightMixPolynomial (u : ℝ) : ℝ := polyB u - polyA u / 4
noncomputable def scaledExpTail (u b : ℝ) : ℝ := b / (Real.exp (u * b) - 1)

theorem rightMixPolynomial_pos {u : ℝ} (hu : 0 < u) : 0 < rightMixPolynomial u := by
  have hp := polyA_pos hu
  have hlt := polyA_lt_polyB hu
  dsimp [rightMixPolynomial]
  linarith

theorem scaledExpTail_eq_factor {u : ℝ} (hu : 0 < u) (b : ℝ) :
    scaledExpTail u b = expTailFactor (u * b) / u := by
  unfold scaledExpTail expTailFactor
  field_simp

theorem scaledExpTail_one_le {u b : ℝ} (hu : 0 < u) (hb : 0 < b) (hb1 : b ≤ 1) :
    scaledExpTail u 1 ≤ scaledExpTail u b := by
  rw [scaledExpTail_eq_factor hu, scaledExpTail_eq_factor hu]
  exact div_le_div_of_nonneg_right
    (strictAntiOn_expTailFactor.antitoneOn (mul_pos hu hb) (by simpa using hu)
      (mul_le_mul_of_nonneg_left hb1 hu.le)) hu.le

theorem polynomial_total_sample {u : ℝ} (hu : 0 < u) :
    (leftMixPolynomial u + rightMixPolynomial u) * scaledExpTail u 1 =
      (3 / 4 : ℝ) * u * Real.exp (-u) := by
  have hden : Real.exp u - 1 ≠ 0 := ne_of_gt (expTail_den_pos hu)
  dsimp [leftMixPolynomial, rightMixPolynomial, polyA, polyB, scaledExpTail]
  rw [mul_one, Real.exp_neg]
  field_simp
  <;> ring

noncomputable def lineResidualDensity (u b : ℝ) : ℝ :=
  leftMixPolynomial u * scaledExpTail u 1 + rightMixPolynomial u * scaledExpTail u b -
    (1 - b / 4) * u * Real.exp (-u) - (5 / 4) * (1 - b) * Real.exp (-u)

noncomputable def correctedLineDensity (u b : ℝ) : ℝ :=
  lineResidualDensity u b + (5 / 4) * (1 - b)

theorem correctedLineDensity_decomposition {u : ℝ} (hu : 0 < u) (b : ℝ) :
    correctedLineDensity u b =
      rightMixPolynomial u * (scaledExpTail u b - scaledExpTail u 1) +
        (1 - b) * ((5 / 4) * (1 - Real.exp (-u)) - u * Real.exp (-u) / 4) := by
  have he := polynomial_total_sample hu
  dsimp [correctedLineDensity, lineResidualDensity]
  nlinarith

theorem correctionMultiplier_pos {u : ℝ} (hu : 0 < u) :
    0 < (5 / 4 : ℝ) * (1 - Real.exp (-u)) - u * Real.exp (-u) / 4 := by
  have h := expHead_numerator_pos hu
  have h' := expHead_den_pos hu
  linarith

theorem correctedLineDensity_nonneg {u b : ℝ} (hu : 0 < u) (hb : 0 < b) (hb1 : b ≤ 1) :
    0 ≤ correctedLineDensity u b := by
  rw [correctedLineDensity_decomposition hu]
  exact add_nonneg
    (mul_nonneg (rightMixPolynomial_pos hu).le (sub_nonneg.mpr (scaledExpTail_one_le hu hb hb1)))
    (mul_nonneg (sub_nonneg.mpr hb1) (correctionMultiplier_pos hu).le)

theorem correctedLineDensity_pos {u b : ℝ} (hu : 0 < u) (hb : 0 < b) (hb1 : b < 1) :
    0 < correctedLineDensity u b := by
  rw [correctedLineDensity_decomposition hu]
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg (rightMixPolynomial_pos hu).le (sub_nonneg.mpr (scaledExpTail_one_le hu hb hb1.le)))
    (mul_pos (sub_pos.mpr hb1) (correctionMultiplier_pos hu))

noncomputable def circleResidualDensity (L u b : ℝ) : ℝ :=
  circleWeight L u * lineResidualDensity u b - (5 / 4) * (1 - b) * (2 * imageDensity L u)

theorem scalar_density_difference (L u b : ℝ) :
    lineResidualDensity u b - circleResidualDensity L u b =
      (2 * imageDensity L u) * correctedLineDensity u b := by
  rw [circleResidualDensity, circleWeight_eq_one_sub_images]
  dsimp [correctedLineDensity]
  ring

theorem circleResidualDensity_lt_line (L : ℝ) {u b : ℝ}
    (hu : 0 < u) (hb : 0 < b) (hb1 : b < 1) :
    circleResidualDensity L u b < lineResidualDensity u b := by
  have h := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) (imageDensity_pos L u))
    (correctedLineDensity_pos hu hb hb1)
  rw [← scalar_density_difference] at h
  linarith

end CenteredCircle.AllN

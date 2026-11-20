import CenteredCircle.EulerIntegral
import CenteredCircle.PeriodizationSeries
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! Exact evaluation of the scalar integral in the periodic image identity. -/

namespace CenteredCircle.AllN

open MeasureTheory Filter Set
open scoped BigOperators

noncomputable def logisticKernel (b x : ℝ) : ℝ :=
  Real.exp (-b * x) / (1 + Real.exp (-x))

theorem logistic_exp_jacobian (b x : ℝ) :
    |Real.exp x| * ((Real.exp x) ^ ((1 - b) - 1) / (1 + Real.exp x)) =
      logisticKernel b x := by
  rw [abs_of_pos (Real.exp_pos x), show (1 - b) - 1 = -b by ring, ← Real.exp_mul]
  have he : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  have hc : x * -b = -b * x := by ring
  rw [hc, logisticKernel]
  rw [← mul_div_assoc]
  apply (div_eq_div_iff (by positivity : (1 + Real.exp x : ℝ) ≠ 0)
    (by positivity : (1 + Real.exp (-x) : ℝ) ≠ 0)).mpr
  nlinarith [congrArg (fun z : ℝ => z * Real.exp (-b * x)) he]

theorem logistic_integral {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    (∫ x : ℝ, logisticKernel b x) = Real.pi / Real.sin (Real.pi * b) := by
  have h := integral_image_eq_integral_abs_deriv_smul (s := (univ : Set ℝ))
    MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn (fun v : ℝ => v ^ ((1 - b) - 1) / (1 + v))
  simp only [Set.image_univ, Real.range_exp, Measure.restrict_univ, smul_eq_mul,
    logistic_exp_jacobian] at h
  rw [← h, euler_integral (by linarith : 0 < 1 - b) (by linarith : 1 - b < 1)]
  rw [mul_sub, mul_one, Real.sin_pi_sub]

theorem integrable_logistic {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    Integrable (logisticKernel b) := by
  apply Integrable.of_integral_ne_zero
  rw [logistic_integral hb hb1]
  apply ne_of_gt
  exact div_pos Real.pi_pos (Real.sin_pos_of_pos_of_lt_pi
    (mul_pos Real.pi_pos hb) (by nlinarith [Real.pi_pos]))

theorem logistic_reflection (b x : ℝ) :
    logisticKernel b (-x) = logisticKernel (1 - b) x := by
  have he : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  have hf : Real.exp (-b * -x) = Real.exp (-(1 - b) * x) * Real.exp x := by
    rw [← Real.exp_add]
    congr 1
    ring
  dsimp [logisticKernel]
  rw [neg_neg, hf]
  apply (div_eq_div_iff (by positivity : (1 + Real.exp x : ℝ) ≠ 0)
    (by positivity : (1 + Real.exp (-x) : ℝ) ≠ 0)).mpr
  nlinarith [congrArg (fun z : ℝ => Real.exp (-(1 - b) * x) * z) he]

theorem logistic_positive_pair_integral {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    (∫ x : ℝ in Ioi 0, logisticKernel b x + logisticKernel (1 - b) x) =
      Real.pi / Real.sin (Real.pi * b) := by
  have hi := integrable_logistic hb hb1
  have hj := integrable_logistic (by linarith : 0 < 1 - b) (by linarith : 1 - b < 1)
  rw [integral_add hi.integrableOn hj.integrableOn]
  have hn : (∫ x : ℝ in Ioi 0, logisticKernel (1 - b) x) =
      ∫ x : ℝ in Iic 0, logisticKernel b x := by
    simp_rw [← logistic_reflection]
    simpa using (integral_comp_neg_Ioi (f := logisticKernel b) (c := (0 : ℝ)))
  rw [hn]
  have hs := integral_add_compl measurableSet_Ioi hi (s := Ioi (0 : ℝ))
  rw [compl_Ioi] at hs
  rw [hs, logistic_integral hb hb1]

theorem periodization_integral_eval {L t : ℝ} (hL : 0 < L)
    (ht : 0 < t) (htL : t < L) :
    (∫ u : ℝ in Ioi 0,
        (Real.exp (-u * t) + Real.exp (-u * (L - t))) /
          (1 + Real.exp (-u * L))) =
      (Real.pi / L) / Real.sin (Real.pi * t / L) := by
  have hb : 0 < t / L := div_pos ht hL
  have hb1 : t / L < 1 := (div_lt_one hL).mpr htL
  let g : ℝ → ℝ := fun x => logisticKernel (t / L) x + logisticKernel (1 - t / L) x
  have he (u : ℝ) : g (L * u) =
      (Real.exp (-u * t) + Real.exp (-u * (L - t))) / (1 + Real.exp (-u * L)) := by
    dsimp [g, logisticKernel]
    have h1 : -(t / L) * (L * u) = -u * t := by field_simp <;> ring
    have h2 : -(1 - t / L) * (L * u) = -u * (L - t) := by field_simp <;> ring
    have h3 : -(L * u) = -u * L := by ring
    rw [h1, h2, h3, add_div]
  have hc := integral_comp_mul_left_Ioi g 0 hL
  simp only [mul_zero, smul_eq_mul] at hc
  simp_rw [he] at hc
  rw [hc]
  dsimp [g]
  rw [logistic_positive_pair_integral hb hb1]
  rw [show Real.pi * (t / L) = Real.pi * t / L by ring]
  ring

theorem radial_periodization {L t : ℝ} (hL : 0 < L) (ht : 0 < t) (htL : t < L) :
    (∑' j : ℤ, radialKernel L |t + j * L|) =
      (Real.pi / L) / Real.sin (Real.pi * t / L) := by
  rw [radial_periodization_integral hL ht htL, periodization_integral_eval hL ht htL]

end CenteredCircle.AllN

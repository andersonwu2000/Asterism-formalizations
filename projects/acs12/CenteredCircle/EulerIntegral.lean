import CenteredCircle.PowerDecay
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.Prod

/-!
The scalar beta integral required by periodization, proved from Gamma moments,
Fubini, and Mathlib's Euler reflection theorem. No project-specific premise.
-/

namespace CenteredCircle.AllN

open MeasureTheory Filter Set

theorem integrable_gamma_laplace {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => x ^ (a - 1) * Real.exp (-(r * x))) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr]
  exact ne_of_gt (mul_pos (Real.rpow_pos_of_pos (by positivity) a) (Real.Gamma_pos_of_pos ha))

theorem euler_integral_inner {b y : ℝ} (hb : 0 < b) (hy : 0 < y) :
    (∫ x : ℝ in Ioi 0, x ^ (b - 1) * Real.exp (-(x + 1) * y)) =
      Real.Gamma b * (y ^ (-b) * Real.exp (-y)) := by
  have he (x : ℝ) : x ^ (b - 1) * Real.exp (-(x + 1) * y) =
      Real.exp (-y) * (x ^ (b - 1) * Real.exp (-(y * x))) := by
    rw [show -(x + 1) * y = -y + -(y * x) by ring, Real.exp_add]
    ring
  simp_rw [he]
  rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hb hy]
  rw [one_div, ← Real.rpow_neg_eq_inv_rpow]
  ring

theorem euler_integral_inner_integrable {b y : ℝ} (hb : 0 < b) (hy : 0 < y) :
    IntegrableOn (fun x : ℝ => x ^ (b - 1) * Real.exp (-(x + 1) * y)) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [euler_integral_inner hb hy]
  exact ne_of_gt (mul_pos (Real.Gamma_pos_of_pos hb)
    (mul_pos (Real.rpow_pos_of_pos hy _) (Real.exp_pos _)))

theorem euler_integral_gamma_product {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    (∫ x : ℝ in Ioi 0, x ^ (b - 1) / (1 + x)) =
      Real.Gamma b * Real.Gamma (1 - b) := by
  have hcomp : 0 < 1 - b := by linarith
  let f : ℝ → ℝ → ℝ := fun x y => x ^ (b - 1) * Real.exp (-(x + 1) * y)
  have hm : Measurable (Function.uncurry f) := by
    dsimp [f, Function.uncurry]
    fun_prop
  have hiOuter : IntegrableOn
      (fun y : ℝ => Real.Gamma b * (y ^ (-b) * Real.exp (-y))) (Ioi 0) := by
    have h := (integrable_gamma_laplace hcomp (by norm_num : (0 : ℝ) < 1)).const_mul
      (Real.Gamma b)
    simpa only [show 1 - b - 1 = -b by ring, one_mul] using h
  have hnorm : ∀ᵐ y : ℝ ∂volume.restrict (Ioi 0),
      (∫ x : ℝ in Ioi 0, ‖f x y‖) = Real.Gamma b * (y ^ (-b) * Real.exp (-y)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [← euler_integral_inner hb hy]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    apply Real.norm_of_nonneg
    dsimp [f]
    exact (mul_pos (Real.rpow_pos_of_pos hx _) (Real.exp_pos _)).le
  have hp : Integrable (Function.uncurry f)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
    apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact euler_integral_inner_integrable hb hy
    · exact hiOuter.congr (Filter.EventuallyEq.symm hnorm)
  have heOuter (x : ℝ) (hx : 0 < x) :
      (∫ y : ℝ in Ioi 0, f x y) = x ^ (b - 1) / (1 + x) := by
    dsimp [f]
    rw [integral_const_mul]
    have heval : (∫ y : ℝ in Ioi 0, Real.exp (-(x + 1) * y)) = 1 / (x + 1) := by
      calc
        (∫ y : ℝ in Ioi 0, Real.exp (-(x + 1) * y)) =
            ∫ y : ℝ in Ioi 0, Real.exp (-y * (x + 1)) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro y _
          dsimp only
          congr 1
          ring
        _ = 1 / (x + 1) := by
          simpa only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one,
            Nat.zero_add, pow_one] using
            integral_power_exponential 0 (x + 1) (add_pos hx zero_lt_one)
    rw [heval]
    ring
  calc
    (∫ x : ℝ in Ioi 0, x ^ (b - 1) / (1 + x)) =
        ∫ x : ℝ in Ioi 0, ∫ y : ℝ in Ioi 0, f x y := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact (heOuter x hx).symm
    _ = ∫ y : ℝ in Ioi 0, ∫ x : ℝ in Ioi 0, f x y := integral_integral_swap hp
    _ = ∫ y : ℝ in Ioi 0, Real.Gamma b * (y ^ (-b) * Real.exp (-y)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      exact euler_integral_inner hb hy
    _ = Real.Gamma b * Real.Gamma (1 - b) := by
      rw [integral_const_mul]
      have h := Real.integral_rpow_mul_exp_neg_mul_Ioi hcomp (by norm_num : (0 : ℝ) < 1)
      simpa only [sub_sub_cancel_left, one_mul, one_div_one, Real.one_rpow]
        using congrArg (fun z : ℝ => Real.Gamma b * z) h

theorem euler_integral {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    (∫ x : ℝ in Ioi 0, x ^ (b - 1) / (1 + x)) = Real.pi / Real.sin (Real.pi * b) := by
  rw [euler_integral_gamma_product hb hb1, Real.Gamma_mul_Gamma_one_sub]

end CenteredCircle.AllN

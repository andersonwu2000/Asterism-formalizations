import CenteredCircle.KernelAlgebra
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Differentiation under the actual Laplace integrals and radial decay. -/

namespace CenteredCircle.AllN

open MeasureTheory Filter Set
open scoped Topology

theorem hasDerivAt_weighted_laplace (g : ℝ → ℝ) (C : ℝ) (k : ℕ)
    (hg : Measurable g) (hC : 0 ≤ C)
    (hbound : ∀ u, 0 < u → |g u| ≤ C * u ^ k)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x => ∫ u : ℝ in Ioi 0, g u * Real.exp (-u * x))
      (-(∫ u : ℝ in Ioi 0, (u * g u) * Real.exp (-u * t))) t := by
  have hhalf : 0 < t / 2 := by positivity
  have hn : Ioi (t / 2) ∈ 𝓝 t := Ioi_mem_nhds (by linarith)
  have hm : ∀ᶠ x in 𝓝 t, AEStronglyMeasurable
      (fun u : ℝ => g u * Real.exp (-u * x)) (volume.restrict (Ioi 0)) := by
    apply Eventually.of_forall
    intro x
    have he : Measurable (fun u : ℝ => Real.exp (-u * x)) := by fun_prop
    exact (hg.mul he).aestronglyMeasurable
  have hm' : AEStronglyMeasurable
      (fun u : ℝ => -(u * g u) * Real.exp (-u * t)) (volume.restrict (Ioi 0)) := by
    have he : Measurable (fun u : ℝ => Real.exp (-u * t)) := by fun_prop
    exact ((measurable_id.mul hg).neg.mul he).aestronglyMeasurable
  have hb : ∀ᵐ u : ℝ ∂volume.restrict (Ioi 0), ∀ x ∈ Ioi (t / 2),
      ‖-(u * g u) * Real.exp (-u * x)‖ ≤
        C * (u ^ (k + 1) * Real.exp (-u * (t / 2))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro x hx
    change 0 < u at hu
    change t / 2 < x at hx
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_mul,
      abs_of_pos hu, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-u * x) ≤ Real.exp (-u * (t / 2)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    calc
      u * |g u| * Real.exp (-u * x) ≤
          u * (C * u ^ k) * Real.exp (-u * (t / 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hbound u hu) hu.le) he
          (Real.exp_pos _).le (by positivity)
      _ = C * (u ^ (k + 1) * Real.exp (-u * (t / 2))) := by
        rw [pow_succ]
        ring
  have hd : ∀ᵐ u : ℝ ∂volume.restrict (Ioi 0), ∀ x ∈ Ioi (t / 2),
      HasDerivAt (fun x => g u * Real.exp (-u * x))
        (-(u * g u) * Real.exp (-u * x)) x := by
    apply Eventually.of_forall
    intro u x _
    have h := (((hasDerivAt_id x).const_mul (-u)).exp).const_mul (g u)
    convert h using 1 <;> dsimp <;> ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ))) hn hm
    (integrable_weighted_exponential_of_abs_bound g C t k hg hbound ht) hm' hb
    ((integrable_power_exponential (k + 1) (t / 2) hhalf).const_mul C) hd
  simpa only [neg_mul, integral_neg] using h.2

theorem hasDerivAt_radialKernel {L t : ℝ} (hL : 0 < L) (ht : 0 < t) :
    HasDerivAt (radialKernel L) (-torqueKernel L t) t := by
  apply hasDerivAt_weighted_laplace (circleWeight L) 1 0
    (continuous_circleWeight L).measurable (by norm_num) _ ht
  intro u hu
  rw [abs_of_pos (circleWeight_pos hL hu), pow_zero, mul_one]
  exact (circleWeight_lt_one L u).le

theorem torqueKernel_eq_neg_deriv {L t : ℝ} (hL : 0 < L) (ht : 0 < t) :
    torqueKernel L t = -deriv (radialKernel L) t := by
  rw [(hasDerivAt_radialKernel hL ht).deriv, neg_neg]

theorem tanh_le_self_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.tanh x ≤ x := by
  have hd (y : ℝ) : HasDerivAt
      (fun z => z * Real.cosh z - Real.sinh z) (y * Real.sinh y) y := by
    have h := ((hasDerivAt_id y).mul (Real.hasDerivAt_cosh y)).sub
      (Real.hasDerivAt_sinh y)
    convert h using 1 <;> dsimp <;> ring
  have hm : MonotoneOn (fun z => z * Real.cosh z - Real.sinh z) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro y _
      exact (hd y).continuousAt.continuousWithinAt
    · intro y _
      exact (hd y).differentiableAt.differentiableWithinAt
    · intro y hy
      have hy' : 0 < y := by simpa using hy
      rw [(hd y).deriv]
      exact (mul_pos hy' (Real.sinh_pos_iff.mpr hy')).le
  have h := hm (by simp) hx hx
  change 0 * Real.cosh 0 - Real.sinh 0 ≤ x * Real.cosh x - Real.sinh x at h
  rw [Real.tanh_eq_sinh_div_cosh, div_le_iff₀ (Real.cosh_pos x)]
  simpa using (show Real.sinh x ≤ x * Real.cosh x by simpa using h)

theorem circleWeight_le_linear {L u : ℝ} (hL : 0 ≤ L) (hu : 0 ≤ u) :
    circleWeight L u ≤ L * u / 2 :=
  tanh_le_self_nonneg (by positivity)

theorem radialKernel_pos {L : ℝ} (hL : 0 < L) (t : ℝ) (ht : 0 < t) :
    0 < radialKernel L t := by
  letI : NeZero (volume.restrict (Ioi (0 : ℝ))) := ⟨positiveHalfLine_ne_zero⟩
  have h := integral_strict_of_ae_lt (volume.restrict (Ioi (0 : ℝ)))
    (integrable_zero ℝ ℝ _) (radialKernel_integrable hL t ht) ?_
  · simpa only [integral_zero] using h
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_pos (circleWeight_pos hL hu) (Real.exp_pos _)

theorem radialKernel_quadratic_bound {L : ℝ} (hL : 0 < L)
    (t : ℝ) (ht : 0 < t) : radialKernel L t ≤ (L / 2) / t ^ 2 := by
  have hm : (∫ u : ℝ in Ioi 0, (L / 2) * (u ^ 1 * Real.exp (-u * t))) =
      (L / 2) / t ^ 2 := by
    rw [integral_const_mul, integral_power_exponential 1 t ht]
    norm_num
    ring
  rw [← hm]
  apply integral_mono_ae (radialKernel_integrable hL t ht)
    ((integrable_power_exponential 1 t ht).const_mul (L / 2))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hb := mul_le_mul_of_nonneg_right (circleWeight_le_linear hL.le hu.le)
    (Real.exp_pos (-u * t)).le
  convert hb using 1 <;> ring

theorem torqueKernel_cubic_bound {L : ℝ} (hL : 0 < L)
    (t : ℝ) (ht : 0 < t) : torqueKernel L t ≤ L / t ^ 3 := by
  have hm : (∫ u : ℝ in Ioi 0, (L / 2) * (u ^ 2 * Real.exp (-u * t))) =
      L / t ^ 3 := by
    rw [integral_const_mul, integral_power_exponential 2 t ht]
    norm_num
    ring
  rw [← hm]
  apply integral_mono_ae (torqueKernel_integrable hL t ht)
    ((integrable_power_exponential 2 t ht).const_mul (L / 2))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hb := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (circleWeight_le_linear hL.le hu.le) hu.le)
    (Real.exp_pos (-u * t)).le
  convert hb using 1 <;> ring

end CenteredCircle.AllN

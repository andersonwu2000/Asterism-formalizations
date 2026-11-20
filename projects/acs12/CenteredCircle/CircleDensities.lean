import CenteredCircle.PositiveDensity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
The actual positive densities of the manuscript's A and B kernels, including
their quadratic bounds. This file proves the density estimates for every L>0.
-/

namespace CenteredCircle.AllN

open Set

noncomputable def polyA (u : ℝ) : ℝ := 1 - (1 + u) * Real.exp (-u)
noncomputable def polyB (u : ℝ) : ℝ := u - 1 + Real.exp (-u)

theorem hasDerivAt_polyA (u : ℝ) : HasDerivAt polyA (u * Real.exp (-u)) u := by
  have hd := (hasDerivAt_const u (1 : ℝ)).sub
    (((hasDerivAt_const u (1 : ℝ)).add (hasDerivAt_id u)).mul
      ((hasDerivAt_id u).neg.exp))
  convert hd using 1 <;> dsimp [polyA] <;> ring

theorem polyA_monotone_nonneg : MonotoneOn polyA (Ici (0 : ℝ)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
  · exact fun t _ => (hasDerivAt_polyA t).continuousAt.continuousWithinAt
  · exact fun t _ => (hasDerivAt_polyA t).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hasDerivAt_polyA t).deriv]
    exact mul_nonneg (show t ∈ Ici (0 : ℝ) from interior_subset ht) (Real.exp_pos _).le

theorem hasDerivAt_polyB (u : ℝ) : HasDerivAt polyB (1 - Real.exp (-u)) u := by
  have hd := ((hasDerivAt_id u).sub_const 1).add ((hasDerivAt_id u).neg.exp)
  convert hd using 1 <;> dsimp [polyB] <;> ring

theorem polyA_pos {u : ℝ} (hu : 0 < u) : 0 < polyA u := by
  have hp := expHead_numerator_pos hu
  dsimp [polyA]
  nlinarith

theorem polyB_pos {u : ℝ} (hu : 0 < u) : 0 < polyB u := by
  have hp := Real.add_one_lt_exp (neg_ne_zero.mpr (ne_of_gt hu))
  dsimp [polyB]
  linarith

theorem hasDerivAt_polyB_sub_polyA (u : ℝ) :
    HasDerivAt (fun x => polyB x - polyA x) (polyA u) u := by
  have hd := (hasDerivAt_polyB u).sub (hasDerivAt_polyA u)
  convert hd using 1 <;> dsimp [polyA] <;> ring

theorem polyA_lt_polyB {u : ℝ} (hu : 0 < u) : polyA u < polyB u := by
  have hm : StrictMonoOn (fun x => polyB x - polyA x) (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · intro x _
      exact (hasDerivAt_polyB_sub_polyA x).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : 0 < x := by simpa using hx
      rw [(hasDerivAt_polyB_sub_polyA x).deriv]
      exact polyA_pos hx'
  have hz : polyB 0 - polyA 0 = 0 := by norm_num [polyA, polyB]
  have h := hm (by simp) hu.le hu
  change polyB 0 - polyA 0 < polyB u - polyA u at h
  rw [hz] at h
  linarith

theorem hasDerivAt_quadratic_sub_polyB (u : ℝ) :
    HasDerivAt (fun x => x ^ 2 / 2 - polyB x) (polyB u) u := by
  have hd := (((hasDerivAt_id u).pow 2).div_const 2).sub (hasDerivAt_polyB u)
  convert hd using 1 <;> dsimp [polyB] <;> ring

theorem polyB_lt_quadratic {u : ℝ} (hu : 0 < u) : polyB u < u ^ 2 / 2 := by
  have hm : StrictMonoOn (fun x => x ^ 2 / 2 - polyB x) (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · intro x _
      exact (hasDerivAt_quadratic_sub_polyB x).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : 0 < x := by simpa using hx
      rw [(hasDerivAt_quadratic_sub_polyB x).deriv]
      exact polyB_pos hx'
  have h := hm (by simp) hu.le hu
  norm_num [polyB] at h
  dsimp [polyB]
  linarith

inductive CircleKernelKind
  | a | b
  deriving DecidableEq

noncomputable def densityPolynomial (kind : CircleKernelKind) (u : ℝ) : ℝ :=
  match kind with
  | .a => polyA u
  | .b => polyB u

theorem densityPolynomial_pos (kind : CircleKernelKind) {u : ℝ} (hu : 0 < u) :
    0 < densityPolynomial kind u := by
  cases kind with
  | a => exact polyA_pos hu
  | b => exact polyB_pos hu

theorem densityPolynomial_lt_quadratic (kind : CircleKernelKind) {u : ℝ} (hu : 0 < u) :
    densityPolynomial kind u < u ^ 2 / 2 := by
  cases kind with
  | a => exact (polyA_lt_polyB hu).trans (polyB_lt_quadratic hu)
  | b => exact polyB_lt_quadratic hu

theorem continuous_densityPolynomial (kind : CircleKernelKind) :
    Continuous (densityPolynomial kind) := by
  cases kind with
  | a => exact continuous_iff_continuousAt.mpr (fun u => (hasDerivAt_polyA u).continuousAt)
  | b => exact continuous_iff_continuousAt.mpr (fun u => (hasDerivAt_polyB u).continuousAt)

noncomputable def circleWeight (L u : ℝ) : ℝ := Real.tanh (L * u / 2)

theorem circleWeight_pos {L u : ℝ} (hL : 0 < L) (hu : 0 < u) : 0 < circleWeight L u := by
  rw [circleWeight, Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr (by positivity)) (Real.cosh_pos _)

theorem circleWeight_lt_one (L u : ℝ) : circleWeight L u < 1 := Real.tanh_lt_one _

theorem continuous_circleWeight (L : ℝ) : Continuous (circleWeight L) := by
  have hc : Continuous (fun u : ℝ => L * u / 2) := by fun_prop
  have hnum := hc.rexp.sub hc.neg.rexp
  have hden := hc.rexp.add hc.neg.rexp
  have h := hnum.div hden (fun u => ne_of_gt (add_pos (Real.exp_pos _) (Real.exp_pos _)))
  convert h using 1
  funext u
  exact Real.tanh_eq _

noncomputable def circleDensity (L : ℝ) (kind : CircleKernelKind) (u : ℝ) : ℝ :=
  circleWeight L u * densityPolynomial kind u

theorem continuous_circleDensity (L : ℝ) (kind : CircleKernelKind) :
    Continuous (circleDensity L kind) :=
  (continuous_circleWeight L).mul (continuous_densityPolynomial kind)

theorem circleDensity_pos {L u : ℝ} (hL : 0 < L) (kind : CircleKernelKind) (hu : 0 < u) :
    0 < circleDensity L kind u :=
  mul_pos (circleWeight_pos hL hu) (densityPolynomial_pos kind hu)

theorem circleDensity_quadratic_bound {L u : ℝ} (kind : CircleKernelKind) (hu : 0 < u) :
    circleDensity L kind u ≤ (1 / 2 : ℝ) * u ^ 2 := by
  have h := mul_le_mul_of_nonneg_right (circleWeight_lt_one L u).le
    (densityPolynomial_pos kind hu).le
  have hp := densityPolynomial_lt_quadratic kind hu
  dsimp [circleDensity]
  nlinarith

end CenteredCircle.AllN

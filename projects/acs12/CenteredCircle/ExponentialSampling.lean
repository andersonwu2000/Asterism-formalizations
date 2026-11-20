import CenteredCircle.Quadrature
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! Strict sampling monotonicity for a pure positive exponential. -/

namespace CenteredCircle.AllN

open Set
open scoped BigOperators

noncomputable def expHeadFactor (s : ℝ) : ℝ := s / (1 - Real.exp (-s))
noncomputable def expTailFactor (s : ℝ) : ℝ := s / (Real.exp s - 1)

theorem expHead_den_pos {s : ℝ} (hs : 0 < s) : 0 < 1 - Real.exp (-s) := by
  have he : Real.exp (-s) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  linarith

theorem expTail_den_pos {s : ℝ} (hs : 0 < s) : 0 < Real.exp s - 1 := by
  have he : 1 < Real.exp s := Real.one_lt_exp_iff.mpr hs
  linarith

theorem hasDerivAt_expHeadFactor {s : ℝ} (hs : 0 < s) :
    HasDerivAt expHeadFactor
      ((1 - Real.exp (-s) - s * Real.exp (-s)) / (1 - Real.exp (-s)) ^ 2) s := by
  have hd := (hasDerivAt_id s).div
    ((hasDerivAt_const s (1 : ℝ)).sub ((hasDerivAt_id s).neg.exp))
    (ne_of_gt (expHead_den_pos hs))
  convert hd using 1 <;> simp

theorem hasDerivAt_expTailFactor {s : ℝ} (hs : 0 < s) :
    HasDerivAt expTailFactor
      ((Real.exp s - 1 - s * Real.exp s) / (Real.exp s - 1) ^ 2) s := by
  have hd := (hasDerivAt_id s).div
    ((Real.hasDerivAt_exp s).sub_const 1) (ne_of_gt (expTail_den_pos hs))
  convert hd using 1 <;> simp

theorem expHead_numerator_pos {s : ℝ} (hs : 0 < s) :
    0 < 1 - Real.exp (-s) - s * Real.exp (-s) := by
  have hx := mul_lt_mul_of_pos_right (Real.add_one_lt_exp (ne_of_gt hs))
    (Real.exp_pos (-s))
  have he : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add]; simp
  rw [he] at hx
  nlinarith

theorem expTail_numerator_neg {s : ℝ} (hs : 0 < s) :
    Real.exp s - 1 - s * Real.exp s < 0 := by
  have hx := mul_lt_mul_of_pos_right
    (Real.add_one_lt_exp (neg_ne_zero.mpr (ne_of_gt hs))) (Real.exp_pos s)
  have he : Real.exp (-s) * Real.exp s = 1 := by rw [← Real.exp_add]; simp
  rw [he] at hx
  nlinarith

theorem strictMonoOn_expHeadFactor : StrictMonoOn expHeadFactor (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro s hs
    exact (hasDerivAt_expHeadFactor hs).continuousAt.continuousWithinAt
  · intro s hs
    have hs' : 0 < s := by simpa using hs
    rw [(hasDerivAt_expHeadFactor hs').deriv]
    exact div_pos (expHead_numerator_pos hs') (sq_pos_of_pos (expHead_den_pos hs'))

theorem strictAntiOn_expTailFactor : StrictAntiOn expTailFactor (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro s hs
    exact (hasDerivAt_expTailFactor hs).continuousAt.continuousWithinAt
  · intro s hs
    have hs' : 0 < s := by simpa using hs
    rw [(hasDerivAt_expTailFactor hs').deriv]
    exact div_neg_of_neg_of_pos (expTail_numerator_neg hs')
      (sq_pos_of_pos (expTail_den_pos hs'))

theorem exponential_samples_hasSum (u t s : ℝ) (hu : 0 < u) (hs : 0 < s) :
    HasSum (fun j : ℕ => Real.exp (-u * (t + j * s)))
      (Real.exp (-u * t) * (1 - Real.exp (-u * s))⁻¹) := by
  have he : Real.exp (-u * s) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hg := (hasSum_geometric_of_lt_one (Real.exp_pos (-u * s)).le he).mul_left
    (Real.exp (-u * t))
  convert hg using 1
  ext j
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

theorem samplingHead_exponential (u t s : ℝ) (hu : 0 < u) (hs : 0 < s) :
    samplingHead (fun x => Real.exp (-u * x)) t s =
      (Real.exp (-u * t) / u) * expHeadFactor (u * s) := by
  rw [samplingHead, (exponential_samples_hasSum u t s hu hs).tsum_eq]
  unfold expHeadFactor
  have hn : u ≠ 0 := ne_of_gt hu
  rw [show -(u * s) = -u * s by ring]
  field_simp

theorem samplingTail_exponential (u t s : ℝ) (hu : 0 < u) (hs : 0 < s) :
    samplingTail (fun x => Real.exp (-u * x)) t s =
      (Real.exp (-u * t) / u) * expTailFactor (u * s) := by
  rw [samplingTail_eq_shift, samplingHead_exponential u (t + s) s hu hs]
  unfold expHeadFactor expTailFactor
  have hn : u ≠ 0 := ne_of_gt hu
  have hd : Real.exp (u * s) - 1 ≠ 0 := ne_of_gt (expTail_den_pos (mul_pos hu hs))
  have he : Real.exp (u * s) ≠ 0 := Real.exp_ne_zero _
  rw [show -u * (t + s) = -u * t + -(u * s) by ring, Real.exp_add, Real.exp_neg]
  field_simp

theorem strictMonoOn_samplingHead_exponential (u t : ℝ) (hu : 0 < u) :
    StrictMonoOn (samplingHead (fun x => Real.exp (-u * x)) t) (Ioi 0) := by
  intro s hs h hh hsh
  rw [samplingHead_exponential u t s hu hs, samplingHead_exponential u t h hu hh]
  exact mul_lt_mul_of_pos_left
    (strictMonoOn_expHeadFactor (mul_pos hu hs) (mul_pos hu hh)
      (mul_lt_mul_of_pos_left hsh hu)) (div_pos (Real.exp_pos _) hu)

theorem strictAntiOn_samplingTail_exponential (u t : ℝ) (hu : 0 < u) :
    StrictAntiOn (samplingTail (fun x => Real.exp (-u * x)) t) (Ioi 0) := by
  intro s hs h hh hsh
  rw [samplingTail_exponential u t s hu hs, samplingTail_exponential u t h hu hh]
  exact mul_lt_mul_of_pos_left
    (strictAntiOn_expTailFactor (mul_pos hu hs) (mul_pos hu hh)
      (mul_lt_mul_of_pos_left hsh hu)) (div_pos (Real.exp_pos _) hu)

end CenteredCircle.AllN

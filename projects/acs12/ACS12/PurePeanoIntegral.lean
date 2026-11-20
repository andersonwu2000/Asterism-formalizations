import ACS12.PurePeano
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Complete positive Peano representations of the normalized source moments. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set

theorem purePeanoA_integral {p u x : ℝ} (hp : 0 < p) (hu : 0 < u) (hx : 0 < x) :
    purePeanoA p u x = p * (p + 1) * ∫ t in 0..u, t * (x + t) ^ (-(p + 2)) := by
  let F (t : ℝ) := -(t * (x + t) ^ (-(p + 1))) / (p + 1) -
    (x + t) ^ (-p) / (p * (p + 1))
  let f (t : ℝ) := t * (x + t) ^ (-(p + 2))
  have hD (t : ℝ) (ht : 0 ≤ t) : HasDerivAt F (f t) t := by
    have hPos := add_pos_of_pos_of_nonneg hx ht
    have hX := (hasDerivAt_id t).const_add x
    have hY := hX.rpow_const (p := -(p + 1)) (Or.inl hPos.ne')
    have hZ := hX.rpow_const (p := -p) (Or.inl hPos.ne')
    convert (((hasDerivAt_id t).mul hY).neg.div_const (p + 1)).sub
      (hZ.div_const (p * (p + 1))) using 1
    simp only [f, id_eq, one_mul, mul_one, show -(p + 1) - 1 = -(p + 2) by ring,
      show -p - 1 = -(p + 1) by ring]
    field_simp [hp.ne', (show p + 1 ≠ 0 by positivity)]
    ring
  have hF : ContinuousOn f (Icc 0 u) := by
    unfold f
    apply continuousOn_id.mul
    apply ContinuousOn.rpow_const (continuousOn_const.add continuousOn_id)
    intro t ht
    exact Or.inl (add_pos_of_pos_of_nonneg hx ht.1).ne'
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := u)
    (fun t ht => by
      rw [uIcc_of_le hu.le] at ht
      exact hD t ht.1)
    (hF.intervalIntegrable_of_Icc (μ := volume) hu.le)
  change _ = p * (p + 1) * (∫ t in 0..u, f t)
  rw [hI]
  simp only [F, purePeanoA, add_zero, zero_mul, neg_zero, zero_div, zero_sub]
  field_simp [hp.ne', (show p + 1 ≠ 0 by positivity)]
  ring

theorem purePeanoB_integral {p u x : ℝ} (hp : 0 < p) (hu : 0 < u) (hx : 0 < x) :
    purePeanoB p u x = p * (p + 1) * ∫ t in 0..u, (u - t) * (x + t) ^ (-(p + 2)) := by
  let F (t : ℝ) := -((u - t) * (x + t) ^ (-(p + 1))) / (p + 1) +
    (x + t) ^ (-p) / (p * (p + 1))
  let f (t : ℝ) := (u - t) * (x + t) ^ (-(p + 2))
  have hD (t : ℝ) (ht : 0 ≤ t) : HasDerivAt F (f t) t := by
    have hPos := add_pos_of_pos_of_nonneg hx ht
    have hX := (hasDerivAt_id t).const_add x
    have hY := hX.rpow_const (p := -(p + 1)) (Or.inl hPos.ne')
    have hZ := hX.rpow_const (p := -p) (Or.inl hPos.ne')
    convert ((((hasDerivAt_id t).const_sub u).mul hY).neg.div_const (p + 1)).add
      (hZ.div_const (p * (p + 1))) using 1
    simp only [f, id_eq, one_mul, mul_one, show -(p + 1) - 1 = -(p + 2) by ring,
      show -p - 1 = -(p + 1) by ring]
    field_simp [hp.ne', (show p + 1 ≠ 0 by positivity)]
    ring
  have hF : ContinuousOn f (Icc 0 u) := by
    unfold f
    apply (continuousOn_const.sub continuousOn_id).mul
    apply ContinuousOn.rpow_const (continuousOn_const.add continuousOn_id)
    intro t ht
    exact Or.inl (add_pos_of_pos_of_nonneg hx ht.1).ne'
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := u)
    (fun t ht => by
      rw [uIcc_of_le hu.le] at ht
      exact hD t ht.1)
    (hF.intervalIntegrable_of_Icc (μ := volume) hu.le)
  change _ = p * (p + 1) * (∫ t in 0..u, f t)
  rw [hI]
  simp only [F, purePeanoB, add_zero, sub_self, zero_mul, neg_zero, zero_div, zero_add, sub_zero]
  field_simp [hp.ne', (show p + 1 ≠ 0 by positivity)]
  ring

theorem purePeanoB_scale {p u x : ℝ} (hu : 0 < u) (hx : 0 < x) :
    purePeanoB p u (u * x) = u ^ (-p) * purePeanoB p 1 x := by
  unfold purePeanoB
  rw [show u * x + u = u * (x + 1) by ring,
    Real.mul_rpow hu.le hx.le, Real.mul_rpow hu.le hx.le,
    Real.mul_rpow hu.le (by positivity : 0 ≤ x + 1),
    show u ^ (-(p + 1)) = u ^ (-p) / u by
      rw [show -(p + 1) = -p - 1 by ring, Real.rpow_sub_one hu.ne']]
  field_simp [hu.ne']

theorem purePeanoA_one {u x : ℝ} (hu : 0 < u) (hx : 0 < x) :
    purePeanoA 1 u x = u ^ 2 / (x * (x + u) ^ 2) := by
  unfold purePeanoA
  have hxu := add_pos hx hu
  rw [Real.rpow_neg hx.le, Real.rpow_neg hxu.le, Real.rpow_one, Real.rpow_one,
    show -((1 : ℝ) + 1) = -2 by norm_num, Real.rpow_neg hxu.le, Real.rpow_two]
  field_simp [hx.ne', hxu.ne']
  ring

theorem purePeanoB_one {u x : ℝ} (hu : 0 < u) (hx : 0 < x) :
    purePeanoB 1 u x = u ^ 2 / (x ^ 2 * (x + u)) := by
  unfold purePeanoB
  have hxu := add_pos hx hu
  rw [show -((1 : ℝ) + 1) = -2 by norm_num, Real.rpow_neg hx.le, Real.rpow_two,
    Real.rpow_neg hx.le, Real.rpow_neg hxu.le, Real.rpow_one, Real.rpow_one]
  field_simp [hx.ne', hxu.ne']
  ring

end ACS12.GammaMeasure

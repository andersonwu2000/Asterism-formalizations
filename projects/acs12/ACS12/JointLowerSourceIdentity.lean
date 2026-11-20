import ACS12.JointLowerKnownTail
import ACS12.JointPureUpperDiagonal

/-! The exact pure adjacent and fourth rows along the same lower diagonal. -/
namespace ACS12.GammaMeasure

open CenteredCircle.AllN

private theorem purePeanoA_scale_mass {p u m x : ℝ} (hu : 0 < u) (hm : 0 < m) (hx : 0 < x) :
    purePeanoA p u (m * x) = m ^ (-p) * purePeanoA p (u / m) x := by
  unfold purePeanoA
  have hM : m * x + u = m * (x + u / m) := by field_simp [hm.ne']
  rw [hM,Real.mul_rpow hm.le hx.le,Real.mul_rpow hm.le (by positivity : 0 ≤ x + u / m),
    Real.mul_rpow hm.le (by positivity : 0 ≤ x + u / m),
    show -(p + 1) = -p - 1 by ring,Real.rpow_sub_one hm.ne']
  field_simp [hm.ne']

private theorem lowerDiagonalRight_sampling {p u m : ℝ} (hu : 0 < u) (hm : 0 < m) :
    samplingHead (purePeanoA p u) m m = m ^ (1 - p) * rightSourceSum 0 p (u / m) := by
  unfold samplingHead
  rw [rightSourceSum_zero_eq]
  have hA (j : ℕ) : purePeanoA p u (m + (j : ℝ) * m) =
      m ^ (-p) * purePeanoA p (u / m) (1 + (j : ℝ)) := by
    rw [show m + (j : ℝ) * m = m * (1 + (j : ℝ)) by ring]
    exact purePeanoA_scale_mass hu hm (by positivity)
  simp_rw [hA,tsum_mul_left,← mul_assoc]
  rw [mul_comm m,← Real.rpow_add_one hm.ne',show -p + 1 = 1 - p by ring]

theorem purePeanoA_tail_self {p m : ℝ} (hm : 0 < m) :
    samplingTail (purePeanoA p m) 0 m = m ^ (1 - p) * rightSourceSum 0 p 1 := by
  have h : samplingTail (purePeanoA p m) 0 m = samplingHead (purePeanoA p m) m m := by
    unfold samplingTail samplingHead
    apply congrArg (fun y : ℝ => m * y)
    apply tsum_congr
    intro j
    simp only [zero_add,Nat.cast_succ]
    congr 1
    ring
  rw [h,lowerDiagonalRight_sampling hm hm,div_self hm.ne']

theorem lowerDiagonal_adjacent_source_eq {p L δ : ℝ} (hp : 1 ≤ p) (hP : p ≤ 2) (hL : 0 < L)
    (hδ : 0 ≤ δ) (hD : δ ≤ 1 / 8) :
    adjacentDiagonal p L 0 (1 - δ) (lowerDiagonalMass δ) =
      lowerDiagonalKnown p δ + lowerDiagonalRight p δ := by
  let m := lowerDiagonalMass δ
  let u := 1 - δ
  have hm : 0 < m := by unfold m lowerDiagonalMass; linarith only [hD]
  have hu : 0 < u := by unfold u; linarith only [hD]
  have hp₀ := zero_lt_one.trans_le hp
  have hA : samplingHead (lawPeanoKernel p L 0 u .a) m m = samplingHead (purePeanoA p u) m m := by
    unfold samplingHead
    apply congrArg (fun x : ℝ => m * x)
    exact tsum_congr (fun j => (lawPeanoKernel_zero hp hP hL hu (show 0 < m + (j : ℝ) * m by positivity)).1)
  have hB : samplingTail (lawPeanoKernel p L 0 u .b) 0 1 = lowerKnownSum 0 p u := by
    rw [lowerKnownSum_zero_eq]
    unfold samplingTail
    rw [one_mul]
    apply tsum_congr
    intro j
    have h := (lawPeanoKernel_zero hp hP hL hu (show 0 < 1 + (j : ℝ) by positivity)).2
    simpa only [zero_add,mul_one,Nat.cast_succ,add_comm] using h
  change adjacentDiagonal p L 0 u m = _
  unfold adjacentDiagonal adjacentSourceLaw
  rw [hA,hB,lowerDiagonalRight_sampling hu hm,lawMoment_zero_radial hp₀ hu,lawMoment_zero_slope hp₀ hu]
  simp only [lawSelf,zero_mul,add_zero]
  change lowerKnownSum 0 p u + u * u ^ (-p) - m * (u * (p * u ^ (-(p + 1))) + u ^ (-p)) +
    m ^ (1 - p) * rightSourceSum 0 p (u / m) =
      ((p + 1) * u ^ (-p) - (2 * p + 1) * u ^ (1 - p) + lowerKnownSum 0 p u) +
        m ^ (1 - p) * rightSourceSum 0 p (u / m)
  rw [show -(p + 1) = -p - 1 by ring,Real.rpow_sub_one hu.ne',show 1 - p = -p + 1 by ring,Real.rpow_add_one hu.ne']
  have hM : m = 2 * u - 1 := by unfold m lowerDiagonalMass u; ring
  rw [hM]
  field_simp [hu.ne'] <;> ring

noncomputable def lowerDiagonalLeft (p δ : ℝ) : ℝ :=
  let u := 1 - δ
  let m := lowerDiagonalMass δ
  u * purePeanoB p m u + ∑' j : ℕ, purePeanoB p m (u + (1 + (j : ℝ)))

theorem lowerDiagonal_fourth_source_eq {p L δ : ℝ} (hp : 1 ≤ p) (hP : p ≤ 2) (hL : 0 < L)
    (hδ : 0 ≤ δ) (hD : δ ≤ 1 / 8) :
    fourthSourceRow p L 0 (1 - δ) (lowerDiagonalMass δ) (lowerDiagonalMass δ) (lowerDiagonalMass δ) =
      lowerDiagonalLeft p δ - (pureZ p - 1) * lowerDiagonalMass δ ^ (1 - p) := by
  let m := lowerDiagonalMass δ
  let u := 1 - δ
  have hm : 0 < m := by unfold m lowerDiagonalMass; linarith only [hD]
  have hu : 0 < u := by unfold u; linarith only [hD]
  have hp₀ := zero_lt_one.trans_le hp
  have hA : samplingTail (lawPeanoKernel p L 0 m .a) 0 m = samplingTail (purePeanoA p m) 0 m := by
    unfold samplingTail
    apply congrArg (fun x : ℝ => m * x)
    exact tsum_congr (fun j => (lawPeanoKernel_zero hp hP hL hm
      (show 0 < 0 + ((j + 1 : ℕ) : ℝ) * m by positivity)).1)
  have hB : samplingTail (lawPeanoKernel p L 0 m .b) u 1 =
      ∑' j : ℕ, purePeanoB p m (u + (1 + (j : ℝ))) := by
    unfold samplingTail
    rw [one_mul]
    apply tsum_congr
    intro j
    have h := (lawPeanoKernel_zero hp hP hL hm (show 0 < u + (1 + (j : ℝ)) by positivity)).2
    simpa only [mul_one,Nat.cast_succ,add_comm (1 : ℝ)] using h
  change fourthSourceRow p L 0 u m m m = _
  unfold fourthSourceRow
  dsimp only
  rw [hA,hB,(lawPeanoKernel_zero hp hP hL hm hu).2,purePeanoA_tail_self hm,rightSourceSum_zero_one hp hP,
    lawMoment_zero_slope hp₀ hm]
  simp only [sub_self,zero_mul,add_zero]
  change u * purePeanoB p m u + _ + m ^ (1 - p) * (p + 1 - pureZ p) -
    m * m * (p * m ^ (-(p + 1))) = (u * purePeanoB p m u + _) - (pureZ p - 1) * m ^ (1 - p)
  rw [show -(p + 1) = -p - 1 by ring,Real.rpow_sub_one hm.ne',
    show 1 - p = -p + 1 by ring,Real.rpow_add_one hm.ne']
  field_simp [hm.ne'] <;> ring

end ACS12.GammaMeasure

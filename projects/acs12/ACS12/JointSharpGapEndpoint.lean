import ACS12.JointSharpGapMoments
import ACS12.JointGapK

/-! Sharp, fully summed far-corner constants in the canonical joint value. -/
namespace ACS12.GammaMeasure

open MeasureTheory Set
open scoped BigOperators
open GammaDeficit (lineDensity)

noncomputable def pureR (p : ℝ) : ℝ := p * (p + 1) * (p + 2) * powerTail (p + 3) 1

private theorem momentGamma_one {p : ℝ} (hp : 0 < p) :
    Real.Gamma (p + 1) / Real.Gamma p = p := by
  rw [Real.Gamma_add_one hp.ne',mul_div_cancel_right₀ _ (Real.Gamma_pos_of_pos hp).ne']

private theorem momentGamma_two {p : ℝ} (hp : 0 < p) :
    Real.Gamma (p + 2) / Real.Gamma p = p * (p + 1) := by
  rw [show p + 2 = (p + 1) + 1 by ring,Real.Gamma_add_one (by positivity : 0 < p + 1).ne',
    mul_div_assoc,momentGamma_one hp]
  ring

private theorem momentGamma_three {p : ℝ} (hp : 0 < p) :
    Real.Gamma (p + 3) / Real.Gamma p = p * (p + 1) * (p + 2) := by
  rw [show p + 3 = (p + 2) + 1 by ring,Real.Gamma_add_one (by positivity : 0 < p + 2).ne',
    mul_div_assoc,momentGamma_two hp]
  ring

private theorem momentTail_two {r : ℝ} (hr : 1 < r) :
    powerTail r 2 = powerTail r 1 - 1 := by
  simpa only [Nat.reduceAdd,Nat.cast_one,Real.one_rpow] using powerTail_shift hr 1

private theorem momentTail_three {r : ℝ} (hr : 1 < r) :
    powerTail r 3 = powerTail r 1 - 1 - (2 : ℝ) ^ (-r) := by
  simpa only [Nat.reduceAdd,Nat.cast_ofNat,momentTail_two hr] using powerTail_shift hr 2

theorem jointGapKp_exact {p : ℝ} (hp : 0 < p) :
    jointGapKp p = p * (1 - p) * pureZ p + (2 * p + 1) * pureQ p - pureR p := by
  have hI : IntegrableOn (fun s : ℝ => lineDensity p s * Real.exp (-s * (0 : ℕ)) *
      CenteredCircle.AllN.polyA s * s * (-BoseShape.C₁ s)) (Ioi 0) := by
    simpa only [Nat.cast_zero,mul_zero,Real.exp_zero,mul_one] using (jointGapKp_integral_bound hp).1
  have h := sharpGapMoment_exact hp 0 hI
  simp only [Nat.cast_zero,mul_zero,Real.exp_zero,mul_one,zero_mul,sub_zero] at h
  change jointGapKp p = _ at h
  rw [h]
  unfold sharpACValue sharpCValue momentBValue momentDValue momentEValue pureZ pureQ pureR
  simp only [Nat.reduceAdd,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,add_zero,Real.one_rpow,
    div_self (Real.Gamma_pos_of_pos hp).ne',one_mul,
    momentGamma_one hp,momentGamma_two hp,momentGamma_three hp,
    show p + 2 - 1 = p + 1 by ring,show p + 3 - 1 = p + 2 by ring]
  rw [momentTail_two (by linarith only [hp] : 1 < p + 1),
    momentTail_two (by linarith only [hp] : 1 < p + 2),momentTail_two (by linarith only [hp] : 1 < p + 3)]
  ring

private theorem fifthLowerFar {b v : ℝ} {k : ℕ} (hb : 0 < b) (hv : 0 ≤ v)
    (h : v ^ 5 < (b ^ k)⁻¹) : v < b ^ (-(k : ℝ) / 5) := by
  apply lt_of_pow_lt_pow_left₀ 5 (Real.rpow_nonneg hb.le _)
  rw [← Real.rpow_mul_natCast hb.le,show -(k : ℝ) / 5 * ↑(5 : ℕ) = -(k : ℝ) by norm_num,
    Real.rpow_neg hb.le,Real.rpow_natCast]
  exact h

private def farPrefix (j : Fin 11) : ℕ := ![99999999999,3589682358,512646476,128858193,44151348,18402379,8780704,4625598,2628063,1584892,1003031] j

private theorem farPrefix_lt (j : Fin 11) :
    (farPrefix j : ℝ) / 100000000000 < (1 + (j.val : ℝ)) ^ (-(24 : ℝ) / 5) := by
  apply fifthLowerFar (k := 24) (by positivity) (by positivity)
  fin_cases j <;> norm_num [farPrefix]

theorem powerTail_four_point_eight_lower : (104314778 / 100000000 : ℝ) < powerTail (24 / 5) 1 := by
  have hTail := powerTail_trapezoid_lower (q := 24 / 5) (m := 12) (by norm_num) (by decide)
  have hSplit := powerTail_prefix_split (q := 24 / 5) (by norm_num) 11
  norm_num only [Nat.reduceAdd] at hSplit
  have hS := Finset.sum_le_sum (s := Finset.univ) (fun j _ => (farPrefix_lt j).le)
  have hEq : (∑ j : Fin 11, (farPrefix j : ℝ) / 100000000000) = 104312363041 / 100000000000 := by
    norm_num [Fin.sum_univ_succ,farPrefix]
  rw [hEq] at hS
  have hA : (7927042 / 100000000000 : ℝ) < (12 : ℝ) ^ (-(19 : ℝ) / 5) :=
    fifthLowerFar (k := 19) (by norm_num) (by norm_num) (by norm_num)
  have hB : (660585 / 100000000000 : ℝ) < (12 : ℝ) ^ (-(24 : ℝ) / 5) :=
    fifthLowerFar (k := 24) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hTail
  simp only [neg_div] at hA hB hS
  linarith only [hSplit,hTail,hA,hB,hS]

theorem jointLowerMassScale_le {p : ℝ} (hP : p ≤ 9 / 5) :
    (3 / 4 : ℝ) ^ (1 - p) < 12588 / 10000 := by
  have hM := Real.rpow_le_rpow_of_exponent_ge (by norm_num : 0 < (3 / 4 : ℝ))
    (by norm_num : (3 / 4 : ℝ) ≤ 1) (show -(4 / 5 : ℝ) ≤ 1 - p by linarith only [hP])
  refine hM.trans_lt ?_
  apply lt_of_pow_lt_pow_left₀ 5 (by norm_num)
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3 / 4),
    show -(4 / 5 : ℝ) * ↑(5 : ℕ) = -(↑(4 : ℕ) : ℝ) by norm_num,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3 / 4),Real.rpow_natCast]
  norm_num

end ACS12.GammaMeasure

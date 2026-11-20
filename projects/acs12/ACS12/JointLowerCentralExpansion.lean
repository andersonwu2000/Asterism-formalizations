import ACS12.JointLowerNativeStream
import Mathlib.Analysis.Analytic.Binomial

/-! Exact centered binomial expansion of the original native atom. -/
namespace ACS12.GammaMeasure

open Set

theorem multichoose_shift (p : ℝ) (n : ℕ) :
    ((n : ℝ) + 1) * Ring.multichoose p (n + 1) =
      p * Ring.multichoose (p + 1) n := by
  have h := Ring.choose_smul_choose (p + (n : ℝ)) (show n ≤ n + 1 by omega)
  rw [Nat.choose_succ_self_right,nsmul_eq_mul,Nat.cast_succ,add_sub_cancel_right,
    show n + 1 - n = 1 by omega,Ring.choose_one_right,mul_comm _ p] at h
  simpa only [Ring.multichoose_eq,Nat.cast_succ,add_sub_cancel_right,
    show p + 1 + (n : ℝ) - 1 = p + (n : ℝ) by ring,
    show p + ((n : ℝ) + 1) - 1 = p + (n : ℝ) by ring] using h

private theorem shiftedPower_hasSum {y s : ℝ} (hy : 0 < y) (hs : |s| < y) (p : ℝ) :
    HasSum (fun n : ℕ => Ring.multichoose p n * s ^ n * y ^ (-(p + (n : ℝ)))) ((y - s) ^ (-p)) := by
  have hB : s / y ∈ Metric.eball (0 : ℝ) 1 := by
    have h : |s / y| < 1 := by
      rw [abs_div,abs_of_pos hy]
      exact (div_lt_one hy).mpr hs
    simpa [Metric.mem_eball,edist_dist,Real.dist_eq,ENNReal.ofReal_lt_one,abs_div] using h
  have h := ((Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero p).hasSum_sub hB).mul_left (y ^ (-p))
  have hVal : y ^ (-p) * (1 / (1 - s / y) ^ p) = (y - s) ^ (-p) := by
    have hY : 0 < y - s := sub_pos.mpr ((le_abs_self s).trans_lt hs)
    have hD : 0 < 1 - s / y := by
      rw [sub_pos,div_lt_one hy]
      exact (le_abs_self s).trans_lt hs
    rw [one_div,← Real.rpow_neg hD.le,← Real.mul_rpow hy.le hD.le]
    congr 1
    field_simp [hy.ne']
  rw [hVal] at h
  apply h.congr_fun
  intro n
  simp only [sub_zero,FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul]
  rw [← Ring.multichoose_eq,div_pow,neg_add_rev,Real.rpow_add hy,Real.rpow_neg hy.le,Real.rpow_natCast]
  ring

noncomputable def lowerCentralWeight (p : ℝ) (n : ℕ) : ℝ :=
  p * Ring.multichoose (p + 1) n / (2 : ℝ) ^ n

noncomputable def lowerCentralCoefficient (n : ℕ) (d : ℝ) : ℝ :=
  if Even n then (n : ℝ) / ((n : ℝ) + 1) - d else 13 / 25 - d + (12 / 25) * d ^ 2

theorem lowerNativeSite_central_hasSum {p j d : ℝ} (hj : 0 ≤ j) (hd : d < 1 / 2) :
    let m := 1 - 2 * d
    let y := (j + 1 / 2) * m + 1
    HasSum (fun n : ℕ => lowerCentralWeight p n * (m * lowerCentralCoefficient n d) *
      y ^ (-(p + 1 + (n : ℝ)))) (lowerNativeSite 0 p j d) := by
  let m := 1 - 2 * d
  let y := (j + 1 / 2) * m + 1
  let x := 1 + j - (1 + 2 * j) * d
  let a := (6 / 25 : ℝ) * (1 - d ^ 2)
  let z := 1 - d - a
  have hm : 0 < m := by unfold m; linarith only [hd]
  have hy : 1 < y := by
    unfold y
    exact lt_add_of_pos_left _ (mul_pos (by linarith only [hj]) hm)
  have hy₀ := zero_lt_one.trans hy
  have hX : y - 1 / 2 = x := by unfold y m x; ring
  have hY : y - (-(1 / 2)) = x + 1 := by unfold y m x; ring
  let A (n : ℕ) := Ring.multichoose p n * (1 / 2 : ℝ) ^ n * y ^ (-(p + (n : ℝ)))
  let B (n : ℕ) := Ring.multichoose p n * (-(1 / 2) : ℝ) ^ n * y ^ (-(p + (n : ℝ)))
  let C (n : ℕ) := Ring.multichoose (p + 1) n * (1 / 2 : ℝ) ^ n * y ^ (-(p + 1 + (n : ℝ)))
  let D (n : ℕ) := Ring.multichoose (p + 1) n * (-(1 / 2) : ℝ) ^ n * y ^ (-(p + 1 + (n : ℝ)))
  have hAP : HasSum A (x ^ (-p)) := hX ▸ shiftedPower_hasSum hy₀ (by simpa using (show (1 / 2 : ℝ) < y by linarith only [hy])) p
  have hBP : HasSum B ((x + 1) ^ (-p)) := hY ▸ shiftedPower_hasSum hy₀ (by simpa using (show (1 / 2 : ℝ) < y by linarith only [hy])) p
  have hCP : HasSum C (x ^ (-(p + 1))) := hX ▸ shiftedPower_hasSum hy₀ (by simpa using (show (1 / 2 : ℝ) < y by linarith only [hy])) (p + 1)
  have hDP : HasSum D ((x + 1) ^ (-(p + 1))) := hY ▸ shiftedPower_hasSum hy₀ (by simpa using (show (1 / 2 : ℝ) < y by linarith only [hy])) (p + 1)
  have hS : HasSum (fun n : ℕ => B (n + 1) - A (n + 1)) ((x + 1) ^ (-p) - x ^ (-p)) := by
    have h := (hasSum_nat_add_iff' (f := fun n => B n - A n) 1).mpr (hBP.sub hAP)
    simpa [A,B] using h
  have hEq : lowerNativeSite 0 p j d =
      m * ((p * z) * x ^ (-(p + 1)) + (p * a) * (x + 1) ^ (-(p + 1)) +
        ((x + 1) ^ (-p) - x ^ (-p))) := by
    unfold lowerNativeSite
    simp only [weightedAffineResponse_zero]
    rw [show 1 + j + 1 - (1 + 2 * j) * d = x + 1 by unfold x; ring]
    unfold m z a
    ring
  change HasSum _ (lowerNativeSite 0 p j d)
  rw [hEq]
  apply (((hCP.mul_left (p * z)).add (hDP.mul_left (p * a))).add hS |>.mul_left m).congr_fun
  intro n
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hN := multichoose_shift p n
  have hE : Ring.multichoose p (n + 1) =
      p * Ring.multichoose (p + 1) n / ((n : ℝ) + 1) := (eq_div_iff hn.ne').mpr (by rw [mul_comm]; exact hN)
  simp only [A,B,C,D,hE,Nat.cast_succ]
  rw [show p + ((n : ℝ) + 1) = p + 1 + (n : ℝ) by ring]
  unfold lowerCentralWeight lowerCentralCoefficient
  have hP : (1 / 2 : ℝ) ^ n = ((2 : ℝ) ^ n)⁻¹ := by rw [one_div,inv_pow]
  rw [pow_succ (1 / 2 : ℝ),pow_succ (-(1 / 2) : ℝ),
    neg_pow, hP]
  by_cases hnE : Even n
  · rw [if_pos hnE,hnE.neg_one_pow]
    set w : ℝ := y ^ (-(p + 1 + (n : ℝ)))
    unfold z a
    field_simp [hn.ne']
    ring
  · have hO : Odd n := Nat.not_even_iff_odd.mp hnE
    rw [if_neg hnE,hO.neg_one_pow]
    unfold z a
    ring


theorem lowerCentralWeight_summable (p : ℝ) : Summable (lowerCentralWeight p) := by
  have h := (shiftedPower_hasSum (y := 1) (s := 1 / 2) (by norm_num) (by norm_num) (p + 1)).summable.mul_left p
  convert h using 1
  funext n
  simp only [lowerCentralWeight,Real.one_rpow,mul_one,div_eq_mul_inv,one_mul,inv_pow,mul_assoc]

theorem lowerCentralWeight_pos {p : ℝ} (hp : 0 < p) (n : ℕ) : 0 < lowerCentralWeight p n := by
  have h (n : ℕ) : ∀ q > (0 : ℝ), 0 < Ring.multichoose q n := by
    induction n with
    | zero => intro q _; simp
    | succ n ih =>
      intro q hq
      have hS := multichoose_shift q n
      have hP := mul_pos hq (ih (q + 1) (by positivity))
      rw [← hS] at hP
      exact pos_of_mul_pos_right hP (by positivity)
  unfold lowerCentralWeight
  exact div_pos (mul_pos hp (h n (p + 1) (by positivity))) (by positivity)

end ACS12.GammaMeasure


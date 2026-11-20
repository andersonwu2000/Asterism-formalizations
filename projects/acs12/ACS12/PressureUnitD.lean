import ACS12.PressureUnitG
import ACS12.PressureHalfPath

/-! The whole fixed-root-ratio derivative of the original unit D gap. -/
namespace ACS12.Pressure

open Set

private theorem tanh_monotone : Monotone Real.tanh := by
  have hD (x : ℝ) : HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
    have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
    convert h using 1
    · funext t
      simp only [Real.tanh_eq_sinh_div_cosh,Pi.div_apply]
    · rw [← pow_two,← pow_two,Real.cosh_sq_sub_sinh_sq]
  exact monotone_of_deriv_nonneg (fun x => (hD x).differentiableAt) (fun x => by rw [(hD x).deriv]; positivity)

private theorem logCosh_le_mul_tanh {w : ℝ} (hw : 0 ≤ w) :
    Real.log (Real.cosh w) ≤ w * Real.tanh w := by
  rcases hw.eq_or_lt with rfl | hw
  · norm_num
  have hD (x : ℝ) : HasDerivAt (fun y => Real.log (Real.cosh y)) (Real.tanh x) x := by
    simpa only [Real.tanh_eq_sinh_div_cosh] using (Real.hasDerivAt_cosh x).log (Real.cosh_pos x).ne'
  have hC : Continuous (fun y : ℝ => Real.log (Real.cosh y)) :=
    continuous_iff_continuousAt.mpr fun x => (hD x).continuousAt
  have hDiff : Differentiable ℝ (fun y : ℝ => Real.log (Real.cosh y)) := fun x => (hD x).differentiableAt
  obtain ⟨t,ht,h⟩ := exists_deriv_eq_slope (fun y : ℝ => Real.log (Real.cosh y)) hw hC.continuousOn hDiff.differentiableOn
  rw [(hD t).deriv,Real.cosh_zero,Real.log_one,sub_zero,sub_zero] at h
  simpa only [mul_comm] using (div_le_iff₀ hw).mp (h.symm.trans_le (tanh_monotone ht.2.le))

noncomputable def unitGapDD (p z : ℝ) : ℝ :=
  -(Real.exp (-z) * Real.cosh ((p - 1) * z) ^ (1 / (p + 1)) *
    ((p + 1) * z * Real.tanh ((p - 1) * z) - Real.log (Real.cosh ((p - 1) * z)))) / (p + 1) ^ 2

theorem unitGapD_deriv {p : ℝ} (hp : 0 < p) (z : ℝ) :
    HasDerivAt (fun t => unitGapD t z) (unitGapDD p z) p := by
  let w := (p - 1) * z
  have h := hasDerivAt_id p
  have hW := (h.sub_const 1).mul_const z
  have hL := hW.cosh.log (Real.cosh_pos w).ne'
  have hP : p + 1 ≠ 0 := by positivity
  have hF := (hL.div (h.add_const 1) hP).exp
  convert ((hF.const_sub (Real.cosh z)).const_mul (Real.exp (-z))) using 1
  · funext t
    unfold unitGapD
    rw [Real.rpow_def_of_pos (Real.cosh_pos _)]
    simp only [Pi.div_apply,id_eq]
    congr 2
    ring
  · change unitGapDD p z = _
    unfold unitGapDD
    simp only [id_eq,Pi.div_apply,mul_one,Real.tanh_eq_sinh_div_cosh]
    rw [Real.rpow_def_of_pos (Real.cosh_pos _)]
    have hE : Real.log (Real.cosh ((p - 1) * z)) * (1 / (p + 1)) =
        Real.log (Real.cosh ((p - 1) * z)) / (p + 1) := by ring
    rw [hE]
    field_simp [hP,(Real.cosh_pos ((p - 1) * z)).ne']

theorem unitGapD_deriv_lt {p z : ℝ} (hp : 9 / 5 ≤ p) (hp₂ : p ≤ 2)
    (hz : 0 < z) (hZ : z ≤ 4 / 5) : unitGapDD p z < -(28 / 405) * z ^ 2 := by
  let w := (p - 1) * z
  let b := Real.tanh w
  have hp₀ : 0 < p := by linarith only [hp]
  have hW : (4 / 5) * z ≤ w := mul_le_mul_of_nonneg_right (by linarith only [hp]) hz.le
  have hZ₂ := pow_le_pow_left₀ hz.le hZ 2
  have hT : (7 / 10) * z < b := by
    have ht := (tanh_rational_bounds (show 0 < (4 / 5) * z by positivity)).1
    apply lt_of_lt_of_le _ (ht.le.trans (tanh_monotone hW))
    apply (lt_div_iff₀ (by positivity : 0 < 3 + ((4 / 5) * z) ^ 2)).mpr
    have hQ : (7 / 10 : ℝ) * (3 + ((4 / 5) * z) ^ 2) < 3 * (4 / 5) := by
      norm_num at hZ₂
      nlinarith only [hZ₂]
    nlinarith only [mul_lt_mul_of_pos_right hQ hz]
  have hB : 0 < b := (by positivity : 0 < (7 / 10) * z).trans hT
  have hLog : Real.log (Real.cosh w) ≤ w * b :=
    logCosh_le_mul_tanh ((by positivity : 0 ≤ (4 / 5) * z).trans hW)
  have hE : (4 / 9 : ℝ) < Real.exp (-z) := by
    have h := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 4 / 5) (by norm_num : (4 / 5 : ℝ) ≤ 1)
      (n := 10) (by decide)
    norm_num [Finset.sum_range_succ,Nat.factorial] at h
    have hU : Real.exp z < 9 / 4 := (Real.exp_le_exp.mpr hZ).trans_lt (by linarith only [h])
    rw [Real.exp_neg,← one_div]
    exact (lt_div_iff₀ (Real.exp_pos _)).mpr (by linarith only [hU])
  have hC : 1 ≤ Real.cosh w ^ (1 / (p + 1)) := Real.one_le_rpow (Real.one_le_cosh w) (by positivity)
  have hDen : 0 < (p + 1) ^ 2 := by positivity
  have hDen' : (p + 1) ^ 2 ≤ 9 := by
    have h := pow_le_pow_left₀ (show 0 ≤ p + 1 by positivity) (show p + 1 ≤ 3 by linarith only [hp₂]) 2
    norm_num at h
    exact h
  have hLog' : 2 * z * b ≤ (p + 1) * z * b - Real.log (Real.cosh w) := by
    unfold w at hLog
    nlinarith only [hLog]
  have hQ : (7 / 5) * z ^ 2 < (p + 1) * z * b - Real.log (Real.cosh w) := by
    have h' := mul_lt_mul_of_pos_left hT (show 0 < 2 * z by positivity)
    exact (by nlinarith only [h'] : (7 / 5) * z ^ 2 < 2 * z * b).trans_le hLog'
  have hNum : (28 / 45) * z ^ 2 <
      Real.exp (-z) * Real.cosh w ^ (1 / (p + 1)) *
        ((p + 1) * z * b - Real.log (Real.cosh w)) := by
    have hPos : 0 < (p + 1) * z * b - Real.log (Real.cosh w) := (by positivity : 0 < (7 / 5) * z ^ 2).trans hQ
    have h' := mul_lt_mul_of_pos_left hQ (show (0 : ℝ) < 4 / 9 by norm_num)
    have h'' := mul_le_mul_of_nonneg_right (hE.le.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hC (Real.exp_pos (-z)).le)) hPos.le
    exact (by nlinarith only [h'] : (28 / 45) * z ^ 2 <
      (4 / 9) * ((p + 1) * z * b - Real.log (Real.cosh w))).trans_le h''
  unfold unitGapDD
  rw [neg_div,show -(28 / 405 : ℝ) * z ^ 2 = -((28 / 405) * z ^ 2) by ring,neg_lt_neg_iff]
  apply (lt_div_iff₀ hDen).mpr
  have h := mul_le_mul_of_nonneg_left hDen' (show 0 ≤ (28 / 405 : ℝ) * z ^ 2 by positivity)
  exact (by norm_num at h ⊢; linarith only [h] : (28 / 405) * z ^ 2 * (p + 1) ^ 2 ≤ (28 / 45) * z ^ 2).trans_lt hNum

theorem unitGapD_anti {z : ℝ} (hz : 0 < z) (hZ : z ≤ 4 / 5) :
    AntitoneOn (fun t => unitGapD t z) (Icc (9 / 5) 2) := by
  have hP (t : ℝ) (ht : t ∈ Icc (9 / 5) 2) : 0 < t := (by norm_num : (0 : ℝ) < 9 / 5).trans_le ht.1
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    (fun t ht => (unitGapD_deriv (hP t ht) z).continuousAt.continuousWithinAt)
    (fun t ht => (unitGapD_deriv (hP t (interior_subset ht)) z).differentiableAt.differentiableWithinAt)
  intro t ht
  have ht' := interior_subset ht
  rw [(unitGapD_deriv (hP t ht') z).deriv]
  exact (unitGapD_deriv_lt ht'.1 ht'.2 hz hZ).le.trans
    (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg z))

end ACS12.Pressure


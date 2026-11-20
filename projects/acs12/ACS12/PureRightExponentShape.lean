import ACS12.PureZCurvatureDensity

/-! Spatial estimates for the log-power term in the exponent derivative. -/

namespace ACS12.GammaMeasure

open Set

noncomputable def logTailPower (p x : ℝ) : ℝ := x ^ (-(p + 1)) * (p * Real.log x - 1)

noncomputable def logTailSlope (p x : ℝ) : ℝ :=
  x ^ (-(p + 2)) * (2 * p + 1 - p * (p + 1) * Real.log x)

noncomputable def logTailSecond (p x : ℝ) : ℝ :=
  x ^ (-(p + 3)) * (p * (p + 1) * (p + 2) * Real.log x - (3 * p ^ 2 + 6 * p + 2))

theorem logTailPower_deriv (p : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (logTailPower p) (logTailSlope p x) x := by
  have h := (Real.hasDerivAt_rpow_const (p := -(p + 1)) (Or.inl hx.ne')).mul
    (((Real.hasDerivAt_log hx.ne').const_mul p).sub_const 1)
  convert h using 1
  rw [logTailSlope, show -(p + 2) = -(p + 1) - 1 by ring, Real.rpow_sub_one hx.ne']
  field_simp [hx.ne']
  ring

theorem logTailSlope_deriv (p : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (logTailSlope p) (logTailSecond p x) x := by
  have h := (Real.hasDerivAt_rpow_const (p := -(p + 2)) (Or.inl hx.ne')).mul
    (((Real.hasDerivAt_log hx.ne').const_mul (p * (p + 1))).const_sub (2 * p + 1))
  convert h using 1
  rw [logTailSecond, show -(p + 3) = -(p + 2) - 1 by ring, Real.rpow_sub_one hx.ne']
  field_simp [hx.ne']
  ring

theorem logTailSecond_continuousOn (p : ℝ) : ContinuousOn (logTailSecond p) (Ioi 0) := by
  have hL : ContinuousOn Real.log (Ioi 0) :=
    fun x hx => (Real.continuousAt_log (show 0 < x from hx).ne').continuousWithinAt
  unfold logTailSecond
  exact (continuousOn_id.rpow_const (fun x hx => Or.inl (show 0 < x from hx).ne')).mul
    ((continuousOn_const.mul hL).sub continuousOn_const)

theorem logTailPower_pos {p x : ℝ} (hp : 0 < p) (hx : 0 < x) (h : 1 / p < Real.log x) :
    0 < logTailPower p x := by
  unfold logTailPower
  have h' := (div_lt_iff₀ hp).mp h
  exact mul_pos (Real.rpow_pos_of_pos hx _) (sub_pos.mpr (by linarith only [h']))

theorem logTailSecond_le {p x : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) (hx : 1 ≤ x) :
    logTailSecond p x ≤ 1 / 50 := by
  let y := Real.log x
  let A := p * (p + 1) * (p + 2)
  let c := 1 / p + 1 / (p + 1) + 1 / (p + 2)
  have hp₀ := zero_lt_one.trans_le hp
  have hx₀ := zero_lt_one.trans_le hx
  have hy : 0 ≤ y := Real.log_nonneg hx
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hA' : A ≤ 20 := by
    have h := mul_le_mul (mul_le_mul hP (show p + 1 ≤ 14 / 5 by linarith only [hP])
      (by positivity : 0 ≤ p + 1) (by norm_num)) (show p + 2 ≤ 19 / 5 by linarith only [hP])
      (by positivity : 0 ≤ p + 2) (by norm_num : (0 : ℝ) ≤ (9 / 5) * (14 / 5))
    dsimp only [A]
    linarith only [h]
  have hc : 7 / 6 ≤ c := by
    have h₁ := one_div_le_one_div_of_le hp₀ hP
    have h₂ := one_div_le_one_div_of_le (show 0 < p + 1 by positivity) (show p + 1 ≤ 14 / 5 by linarith only [hP])
    have h₃ := one_div_le_one_div_of_le (show 0 < p + 2 by positivity) (show p + 2 ≤ 19 / 5 by linarith only [hP])
    dsimp only [c]
    linarith only [h₁, h₂, h₃]
  have hEq : logTailSecond p x = Real.exp (y * (-(p + 3))) * (A * (y - c)) := by
    unfold logTailSecond
    rw [Real.rpow_def_of_pos hx₀]
    dsimp only [A, c, y]
    field_simp [hp₀.ne', (show 0 < p + 1 by positivity).ne', (show 0 < p + 2 by positivity).ne']
    ring
  rw [hEq]
  by_cases h : y ≤ c
  · exact (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      (mul_nonpos_of_nonneg_of_nonpos hA (sub_nonpos.mpr h))).trans (by norm_num)
  have hY : 0 ≤ y - c := sub_nonneg.mpr (lt_of_not_ge h).le
  have hE : Real.exp (y * (-(p + 3))) ≤ Real.exp (-4 * y) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg hy (sub_nonneg.mpr hp)]
  have hB : A * (y - c) ≤ 20 * (y - 7 / 6) := by
    exact mul_le_mul hA' (sub_le_sub_left hc _) hY (by norm_num)
  have hT := mul_le_mul hE hB (mul_nonneg hA hY) (Real.exp_pos _).le
  have hTan := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (4 * (y - 7 / 6) - 1)) (Real.exp_pos (-4 * y)).le
  rw [← Real.exp_add, show 4 * (y - 7 / 6) - 1 + -4 * y = -(17 / 3) by ring] at hTan
  have hExp : Real.exp (-(17 / 3) : ℝ) ≤ 1 / 250 := by
    have h₁ : (27 / 10 : ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
    have h₂ := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 2 / 3 by norm_num)
    have h₃ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27 / 10) h₁ 5
    have h₄ := mul_le_mul h₃ h₂ (by norm_num : (0 : ℝ) ≤ 1 + 2 / 3 + (2 / 3) ^ 2 / 2)
      (by positivity : 0 ≤ Real.exp 1 ^ 5)
    rw [← Real.exp_nat_mul, ← Real.exp_add] at h₄
    have h₅ : (250 : ℝ) ≤ Real.exp (17 / 3) := by norm_num at h₄ ⊢; linarith only [h₄]
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) h₅
  nlinarith only [hT, hTan, hExp]

private theorem logTailDamped_deriv_nonneg {p x : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hx : 0 < x) (h : 1 / p < Real.log x) :
    0 ≤ logTailSlope p x + logTailPower p x / 2 := by
  let y := Real.log x
  let r := y - 5 / 9
  have hp₀ := zero_lt_one.trans_le hp
  have hInv : 5 / 9 ≤ 1 / p := by
    have h' := one_div_le_one_div_of_le hp₀ hP
    norm_num at h'
    simpa only [one_div] using h'
  have hy : 0 < y - 1 / p := sub_pos.mpr h
  have hr : 0 < r := by dsimp only [r]; linarith only [hy, hInv]
  have hE : (16 / 5 : ℝ) ≤ Real.exp (5 / 9 + 4 / 5) := by
    have h' := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 5 / 9 + 4 / 5 by norm_num)
    linarith only [h']
  have hX : (8 / 5) * (r + 1 / 5) ≤ x / 2 := by
    have hT := Real.add_one_le_exp (r - 4 / 5)
    have hC := mul_le_mul hE hT (show 0 ≤ r - 4 / 5 + 1 by linarith only [hr]) (Real.exp_pos _).le
    rw [← Real.exp_add, show (5 / 9 + 4 / 5) + (r - 4 / 5) = y by dsimp only [r]; ring,
      show Real.exp y = x from Real.exp_log hx] at hC
    linarith only [hC]
  have hQ : ((14 / 5) - x / 2) * r ≤ 1 := by
    have h' := mul_le_mul_of_nonneg_right hX hr.le
    nlinarith only [h', sq_nonneg (r - 31 / 40)]
  have hR : (p + 1 - x / 2) * (y - 1 / p) ≤ 1 := by
    rcases le_or_gt (p + 1 - x / 2) 0 with h₀ | h₀
    · exact (mul_nonpos_of_nonpos_of_nonneg h₀ hy.le).trans zero_le_one
    · have hL : y - 1 / p ≤ r := by dsimp only [r]; linarith only [hInv]
      exact (mul_le_mul (by linarith only [hP] : p + 1 - x / 2 ≤ 14 / 5 - x / 2)
        hL hy.le (by linarith only [hP, h₀])).trans hQ
  have hP' : 0 ≤ p - (p + 1 - x / 2) * (p * y - 1) := by
    have h' := mul_le_mul_of_nonneg_left hR hp₀.le
    have hI : p * (y - 1 / p) = p * y - 1 := by field_simp [hp₀.ne']
    have hJ : p * ((p + 1 - x / 2) * (y - 1 / p)) =
        (p + 1 - x / 2) * (p * y - 1) := by rw [← hI]; ring
    rw [hJ] at h'
    linarith only [h']
  have hPow : x ^ (-(p + 1)) = x ^ (-(p + 2)) * x := by
    calc
      _ = x ^ (-(p + 2) + 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hx, Real.rpow_one]
  rw [logTailSlope, logTailPower, hPow]
  have hF := mul_nonneg (Real.rpow_nonneg hx.le (-(p + 2))) hP'
  dsimp only [y] at hF
  nlinarith only [hF]

theorem logTailPower_next_ratio {p x : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hx : 0 < x) (h : 1 / p < Real.log x) :
    logTailPower p x < (5 / 3) * logTailPower p (x + 1) := by
  let g (t : ℝ) := Real.exp (t / 2) * logTailPower p t
  let d (t : ℝ) := Real.exp (t / 2) * (logTailSlope p t + logTailPower p t / 2)
  have hab : x ≤ x + 1 := by linarith
  have hD (t : ℝ) (ht : x ≤ t) : HasDerivAt g (d t) t := by
    have hE := ((hasDerivAt_id t).div_const 2).exp
    convert hE.mul (logTailPower_deriv p (hx.trans_le ht)) using 1
    norm_num [d, id_eq] <;> ring
  have hMono : MonotoneOn g (Icc x (x + 1)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun t ht => (hD t ht.1).continuousAt.continuousWithinAt
    · exact fun t ht => (hD t (interior_subset ht).1).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Icc x (x + 1) := interior_subset ht
      rw [(hD t ht'.1).deriv]
      exact mul_nonneg (Real.exp_pos _).le
        (logTailDamped_deriv_nonneg hp hP (hx.trans_le ht'.1) (h.trans_le (Real.log_le_log hx ht'.1)))
  have hA := hMono (show x ∈ Icc x (x + 1) from ⟨le_rfl, hab⟩)
    (show x + 1 ∈ Icc x (x + 1) from ⟨hab, le_rfl⟩) hab
  dsimp only [g] at hA
  rw [show (x + 1) / 2 = x / 2 + 1 / 2 by ring, Real.exp_add, mul_assoc] at hA
  have hB := le_of_mul_le_mul_left hA (Real.exp_pos (x / 2))
  have hExp : Real.exp (1 / 2 : ℝ) < 5 / 3 := by
    by_contra! h'
    have h'' := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5 / 3) h' 2
    rw [pow_two (Real.exp (1 / 2)), ← Real.exp_add, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num] at h''
    linarith only [h'', Real.exp_one_lt_d9]
  exact hB.trans_lt (mul_lt_mul_of_pos_right hExp (logTailPower_pos (zero_lt_one.trans_le hp)
    (hx.trans_le hab) (h.trans_le (Real.log_le_log hx hab))))

end ACS12.GammaMeasure

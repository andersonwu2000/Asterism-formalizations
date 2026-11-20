import ACS12.PressureGapEnclosure

/-! Restore the signed debit on the original two physical masses. -/
namespace ACS12.Pressure

noncomputable def originalGapG (p x y : ℝ) : ℝ :=
  ((x + y) / 2) ^ (1 / (p + 1)) - (x ^ (1 / (p + 1)) + y ^ (1 / (p + 1))) / 2

noncomputable def originalGapD (p x y : ℝ) : ℝ :=
  (x ^ (1 / p) + y ^ (1 / p)) / 2 -
    ((x ^ (1 / p) * y + y ^ (1 / p) * x) / 2) ^ (1 / (p + 1))

private theorem exp_pair_avg (s d : ℝ) :
    (Real.exp (s + d) + Real.exp (s - d)) / 2 = Real.exp s * Real.cosh d := by
  rw [Real.cosh_eq,Real.exp_add,Real.exp_sub,Real.exp_neg]
  ring

private theorem originalGapG_exp (p s z : ℝ) :
    originalGapG p (Real.exp (p * s)) (Real.exp (p * (s - 2 * z))) =
      Real.exp ((p / (p + 1)) * s) * unitGapG p z := by
  let a : ℝ := 1 / (p + 1)
  let β : ℝ := p / (p + 1)
  have hA : p * a = β := by unfold a β; ring
  have hM : (Real.exp (p * s) + Real.exp (p * (s - 2 * z))) / 2 =
      Real.exp (p * (s - z)) * Real.cosh (p * z) := by
    rw [← exp_pair_avg]
    congr 2 <;> congr 1 <;> ring
  have hC : (Real.exp (p * s) ^ a + Real.exp (p * (s - 2 * z)) ^ a) / 2 =
      Real.exp (β * (s - z)) * Real.cosh (β * z) := by
    rw [← Real.exp_mul,← Real.exp_mul,← exp_pair_avg]
    have hE (t : ℝ) : p * t * a = β * t := by rw [← hA]; ring
    rw [hE,hE]
    congr 2 <;> congr 1 <;> ring
  change ((Real.exp (p * s) + Real.exp (p * (s - 2 * z))) / 2) ^ a -
    (Real.exp (p * s) ^ a + Real.exp (p * (s - 2 * z)) ^ a) / 2 =
      Real.exp (β * s) * (Real.exp (-β * z) * (Real.cosh (p * z) ^ a - Real.cosh (β * z)))
  rw [hM,hC,Real.mul_rpow (Real.exp_pos _).le (Real.cosh_pos _).le,← Real.exp_mul]
  have hE : p * (s - z) * a = β * (s - z) := by rw [← hA]; ring
  rw [hE,show β * (s - z) = β * s + -β * z by ring,Real.exp_add]
  ring

private theorem originalGapD_exp {p : ℝ} (hp : 0 < p) (s z : ℝ) :
    originalGapD p (Real.exp (p * s)) (Real.exp (p * (s - 2 * z))) =
      Real.exp s * unitGapD p z := by
  let a : ℝ := 1 / (p + 1)
  let ν := p + 1
  have hA : ν * a = 1 := by unfold a ν; field_simp [show p + 1 ≠ 0 by positivity]
  have hE (t : ℝ) : Real.exp (p * t) ^ (1 / p) = Real.exp t := by
    rw [← Real.exp_mul]
    congr 1
    field_simp [hp.ne']
  have hM : (Real.exp s + Real.exp (s - 2 * z)) / 2 = Real.exp (s - z) * Real.cosh z := by
    rw [← exp_pair_avg]
    congr 2 <;> congr 1 <;> ring
  have hC : (Real.exp s * Real.exp (p * (s - 2 * z)) + Real.exp (s - 2 * z) * Real.exp (p * s)) / 2 =
      Real.exp (ν * (s - z)) * Real.cosh ((p - 1) * z) := by
    rw [← Real.exp_add,← Real.exp_add,add_comm (Real.exp _),← exp_pair_avg]
    unfold ν
    congr 2 <;> congr 1 <;> ring
  unfold originalGapD unitGapD
  rw [hE,hE,hM,hC,Real.mul_rpow (Real.exp_pos _).le (Real.cosh_pos _).le,← Real.exp_mul]
  have hL : ν * (s - z) * a = s - z := by linear_combination (s - z) * hA
  change Real.exp (s - z) * Real.cosh z -
    Real.exp (ν * (s - z) * a) * Real.cosh ((p - 1) * z) ^ a = _
  rw [hL,Real.exp_sub,Real.exp_neg]
  ring

theorem originalGaps_eq_zero {p x : ℝ} (hp : 0 < p) (hx : 0 < x) :
    originalGapG p x x = 0 ∧ originalGapD p x x = 0 := by
  constructor
  · unfold originalGapG
    rw [show (x + x) / 2 = x by ring]
    ring
  · unfold originalGapD
    rw [show (x ^ (1 / p) * x + x ^ (1 / p) * x) / 2 = x ^ (1 / p) * x by ring,
      ← Real.rpow_add_one hx.ne',← Real.rpow_mul hx.le]
    have hE : (1 / p + 1) * (1 / (p + 1)) = 1 / p := by
      field_simp [hp.ne',show p + 1 ≠ 0 by positivity]
      ring
    rw [hE]
    ring

private theorem originalGapD_le_weighted_of_lt {p x y : ℝ} (hp : 9 / 5 ≤ p) (hp₂ : p ≤ 2)
    (hy : 1 / 16 ≤ y) (hxy : y < x) (hx : x ≤ 1) :
    originalGapD p x y ≤ (28 / 27) * originalGapG p x y := by
  have hp₀ : 0 < p := by linarith only [hp]
  have hy₀ : 0 < y := by linarith only [hy]
  have hx₀ : 0 < x := hy₀.trans hxy
  let s := Real.log x / p
  let z := Real.log (x / y) / (2 * p)
  have hS : s ≤ 0 := div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos hx₀.le hx) hp₀.le
  have hZ : 0 < z := div_pos (Real.log_pos ((one_lt_div hy₀).mpr hxy)) (by positivity)
  have hL : (9 / 5) * z ≤ pressureContrastCap := by
    have hQ : x / y ≤ 16 := (div_le_iff₀ hy₀).mpr (by linarith only [hy,hx])
    have hQ' := Real.log_le_log (div_pos hx₀ hy₀) hQ
    have hLog : Real.log 16 = 2 * pressureContrastCap := by
      unfold pressureContrastCap
      rw [show (16 : ℝ) = 4 * 4 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
      ring
    have hz : p * z = Real.log (x / y) / 2 := by unfold z; field_simp [hp₀.ne']
    have h := mul_le_mul_of_nonneg_right hp hZ.le
    linarith only [h,hz,hQ',hLog]
  have hxE : x = Real.exp (p * s) := by
    unfold s
    rw [mul_div_cancel₀ _ hp₀.ne',Real.exp_log hx₀]
  have hyE : y = Real.exp (p * (s - 2 * z)) := by
    have hEq : p * (s - 2 * z) = Real.log y := by
      unfold s z
      rw [Real.log_div hx₀.ne' hy₀.ne']
      field_simp [hp₀.ne']
      ring
    rw [hEq,Real.exp_log hy₀]
  have hD : originalGapD p x y = Real.exp s * unitGapD p z := by
    rw [hxE,hyE,originalGapD_exp hp₀]
  have hG : originalGapG p x y = Real.exp ((p / (p + 1)) * s) * unitGapG p z := by
    rw [hxE,hyE,originalGapG_exp]
  obtain ⟨hPos,hLow,hUpper⟩ := pressureUnitGap_enclosure hp hp₂ hZ hL
  have hG₀ := hPos.le.trans hLow
  have hTail := (sourceGapTail_bounds (show 0 ≤ (9 / 5 : ℝ) * z by positivity) hL).2
  have hBound : unitGapD p z ≤ (28 / 27) * unitGapG p z := by
    calc
      _ ≤ sourceGapLower z * (1 + sourceGapTail ((9 / 5) * z)) := hUpper
      _ ≤ sourceGapLower z * (28 / 27) :=
        mul_le_mul_of_nonneg_left (by linarith only [hTail]) hPos.le
      _ ≤ _ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hLow (by norm_num)
  have hScale : Real.exp s ≤ Real.exp ((p / (p + 1)) * s) := by
    have hP : p / (p + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    exact Real.exp_le_exp.mpr (by simpa only [one_mul] using mul_le_mul_of_nonpos_right hP hS)
  rw [hD,hG]
  calc
    _ ≤ Real.exp s * ((28 / 27) * unitGapG p z) := mul_le_mul_of_nonneg_left hBound (Real.exp_pos _).le
    _ ≤ Real.exp ((p / (p + 1)) * s) * ((28 / 27) * unitGapG p z) :=
      mul_le_mul_of_nonneg_right hScale (mul_nonneg (by norm_num) hG₀)
    _ = _ := by ring

theorem originalGapD_le_weighted {p x y : ℝ} (hp : 9 / 5 ≤ p) (hp₂ : p ≤ 2)
    (hx₀ : 1 / 16 ≤ x) (hy₀ : 1 / 16 ≤ y) (hx : x ≤ 1) (hy : y ≤ 1) :
    originalGapD p x y ≤ (28 / 27) * originalGapG p x y := by
  rcases lt_trichotomy y x with h | h | h
  · exact originalGapD_le_weighted_of_lt hp hp₂ hy₀ h hx
  · subst y
    obtain ⟨hG,hD⟩ := originalGaps_eq_zero (by linarith only [hp]) (by linarith only [hx₀])
    rw [hG,hD,mul_zero]
  · have hD : originalGapD p x y = originalGapD p y x := by unfold originalGapD; ring
    have hG : originalGapG p x y = originalGapG p y x := by unfold originalGapG; ring
    rw [hD,hG]
    exact originalGapD_le_weighted_of_lt hp hp₂ hx₀ h hy

end ACS12.Pressure


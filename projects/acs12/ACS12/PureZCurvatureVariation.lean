import ACS12.PureZCurvatureDensity

/-! The positive variation of the Z curvature slope on the complete spatial tail. -/

namespace ACS12.GammaMeasure

open Set MeasureTheory intervalIntegral

private theorem log_four_bounds :
    (693 / 500 : ℝ) < Real.log 4 ∧ Real.log 4 < 347 / 250 := by
  have h : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  constructor
  · linarith only [h, Real.log_two_gt_d9]
  · linarith only [h, Real.log_two_lt_d9]

private theorem slope_lower {p x : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) (hx : 4 ≤ x) :
    -(4 / 125) ≤ zetaCurvatureSlope p x := by
  let y := Real.log x
  let a := p * (p + 1)
  have hx₀ : 0 < x := (by norm_num : (0 : ℝ) < 4).trans_le hx
  have hy : 5 / 4 ≤ y := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hx
    dsimp only [y]
    linarith only [log_four_bounds.1, h]
  have ha₀ : 0 ≤ a := by dsimp only [a]; positivity
  have ha : a ≤ 126 / 25 := by
    dsimp only [a]
    calc
      _ ≤ (9 / 5 : ℝ) * (9 / 5 + 1) :=
        mul_le_mul hP (by linarith only [hP]) (by linarith only [hp]) (by norm_num)
      _ = _ := by norm_num
  have hB : (5 / 4) * a + 2 ≤ 4 * p + 2 := by
    have h := mul_nonneg (show 0 ≤ p by linarith only [hp])
      (show 0 ≤ 4 - (5 / 4) * (p + 1) by linarith only [hP])
    dsimp only [a]
    nlinarith only [h]
  have hQ : -peanoExponentQuadratic p y ≤ a * y * (y - 5 / 4) := by
    have h₁ := mul_le_mul_of_nonneg_right hB (show 0 ≤ y by linarith only [hy])
    unfold peanoExponentQuadratic
    nlinarith only [h₁, hy]
  have hq₀ : 0 ≤ a * y * (y - 5 / 4) :=
    mul_nonneg (mul_nonneg ha₀ (by linarith only [hy])) (sub_nonneg.mpr hy)
  have hE : Real.exp (y * (-(p + 2))) ≤ Real.exp (-3 * y) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg (sub_nonneg.mpr hp) (show 0 ≤ y by linarith only [hy])]
  have hFirst : y * Real.exp (-y) ≤ 46 / 125 := by
    have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (y - 1)) (Real.exp_pos (-y)).le
    rw [← Real.exp_add, show y - 1 + -y = -1 by ring] at h
    have h' : Real.exp (-1 : ℝ) < 46 / 125 := by linarith only [Real.exp_neg_one_lt_d9]
    nlinarith only [h, h']
  have hExp : Real.exp (-(7 / 2) : ℝ) ≤ 1 / 30 := by
    have h1 : (27 / 10 : ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
    have h2 : (13 / 8 : ℝ) ≤ Real.exp (1 / 2) := by
      have h := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      norm_num at h ⊢
      exact h
    have h3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27 / 10) h1 3
    have h4 := mul_le_mul h3 h2 (by norm_num : (0 : ℝ) ≤ 13 / 8) (by positivity : 0 ≤ Real.exp 1 ^ 3)
    rw [← Real.exp_nat_mul, ← Real.exp_add] at h4
    have h5 : (30 : ℝ) ≤ Real.exp (7 / 2) := by norm_num at h4 ⊢; linarith only [h4]
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) h5
  have hSecond : (y - 5 / 4) * Real.exp (-2 * y) ≤ 1 / 60 := by
    have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (2 * (y - 5 / 4) - 1))
      (Real.exp_pos (-2 * y)).le
    rw [← Real.exp_add, show 2 * (y - 5 / 4) - 1 + -2 * y = -(7 / 2) by ring] at h
    nlinarith only [h, hExp]
  have hFact : a * y * (y - 5 / 4) * Real.exp (-3 * y) =
      a * (y * Real.exp (-y)) * ((y - 5 / 4) * Real.exp (-2 * y)) := by
    rw [show -3 * y = -y + -2 * y by ring, Real.exp_add]
    ring
  have hPos : 0 ≤ (y - 5 / 4) * Real.exp (-2 * y) :=
    mul_nonneg (sub_nonneg.mpr hy) (Real.exp_pos _).le
  have hProd := mul_le_mul (mul_le_mul ha hFirst (by positivity : 0 ≤ y * Real.exp (-y))
    (by norm_num : (0 : ℝ) ≤ 126 / 25)) hSecond hPos (by norm_num : (0 : ℝ) ≤ (126 / 25) * (46 / 125))
  have hT := (mul_le_mul_of_nonneg_right hQ (Real.exp_pos (y * (-(p + 2)))).le).trans
    (mul_le_mul_of_nonneg_left hE hq₀)
  rw [hFact] at hT
  unfold zetaCurvatureSlope
  rw [Real.rpow_def_of_pos hx₀]
  change -(4 / 125) ≤ Real.exp (y * (-(p + 2))) * peanoExponentQuadratic p y
  nlinarith only [hT, hProd]

private theorem spatial_neg_at_four {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    zetaCurvatureQuadratic p (Real.log 4) < 0 := by
  let y := Real.log 4
  have hy : 693 / 500 < y := log_four_bounds.1
  have hy₂ : y ^ 2 ≤ 1927 / 1000 := by
    have h := pow_le_pow_left₀ (show 0 ≤ y by linarith only [hy]) log_four_bounds.2.le 2
    linarith only [h]
  have hA : 0 ≤ p * (p + 1) * (p + 2) := by positivity
  have hB : 0 ≤ 6 * p ^ 2 + 12 * p + 4 := by positivity
  have hC := mul_le_mul_of_nonneg_left hy₂ hA
  have hD := mul_le_mul_of_nonneg_left hy.le hB
  have hp₀ : 0 ≤ p := by linarith only [hp]
  have hE := mul_le_mul_of_nonneg_right hP (sq_nonneg p)
  have hF := mul_le_mul_of_nonneg_right hP hp₀
  change zetaCurvatureQuadratic p y < 0
  unfold zetaCurvatureQuadratic
  nlinarith only [hC, hD, hE, hF, hp]

private theorem spatial_neg_at_three_halves {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    zetaCurvatureQuadratic p (3 / 2) < 0 := by
  have hp₀ : 0 < p := zero_lt_one.trans_le hp
  have h := mul_le_mul hP (show p - 1 ≤ 4 / 5 by linarith only [hP])
    (sub_nonneg.mpr hp) (by norm_num)
  have h' := mul_lt_mul_of_pos_left (show (9 / 4) * p * (p - 1) - 15 / 2 < 0 by nlinarith only [h]) hp₀
  unfold zetaCurvatureQuadratic
  nlinarith only [h']

theorem spatial_cut {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    ∃ X : ℝ, 4 ≤ X ∧
      (∀ x ∈ Icc 4 X, zetaCurvatureSpatial p x ≤ 0) ∧
      (∀ x ∈ Ici X, 0 ≤ zetaCurvatureSpatial p x ∧ zetaCurvatureSlope p x ≤ 0) := by
  let t := Real.log 4
  let a := p * (p + 1) * (p + 2)
  let b := 2 * a * t - (6 * p ^ 2 + 12 * p + 4)
  let c := zetaCurvatureQuadratic p t
  let D := b ^ 2 - 4 * a * c
  let d := Real.sqrt D
  let r := (d - b) / (2 * a)
  let s := (-d - b) / (2 * a)
  have ha : 0 < a := by dsimp only [a]; positivity
  have hc : c < 0 := spatial_neg_at_four hp hP
  have hD : b ^ 2 < D := by dsimp only [D]; nlinarith only [mul_neg_of_pos_of_neg ha hc]
  have hD₀ : 0 ≤ D := (sq_nonneg b).trans hD.le
  have hd : d ^ 2 = D := Real.sq_sqrt hD₀
  have hd' : |b| < d := by
    have hAbs : |b| ^ 2 = b ^ 2 := sq_abs b
    by_contra! h
    have h' := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
    nlinarith only [h', hd, hAbs, hD]
  have hr : 0 < r := div_pos (sub_pos.mpr ((le_abs_self _).trans_lt hd')) (by positivity)
  have hs : s < 0 := div_neg_of_neg_of_pos (by linarith only [(neg_le_abs _).trans_lt hd']) (by positivity)
  have hF (y : ℝ) : zetaCurvatureQuadratic p (t + y) = a * (y - r) * (y - s) := by
    have h1 : zetaCurvatureQuadratic p (t + y) = a * y ^ 2 + b * y + c := by
      dsimp only [a, b, c, zetaCurvatureQuadratic]
      ring
    rw [h1]
    have hd₂ : d ^ 2 = b ^ 2 - 4 * a * c := hd
    have hDen : 2 * a ≠ 0 := by positivity
    have hR : y - r = (2 * a * y + b - d) / (2 * a) := by
      dsimp only [r]
      field_simp [hDen, ha.ne'] <;> ring
    have hS : y - s = (2 * a * y + b + d) / (2 * a) := by
      dsimp only [s]
      field_simp [hDen, ha.ne'] <;> ring
    rw [hR, hS]
    calc
      _ = (a * (2 * a * y + b - d) * (2 * a * y + b + d)) / (2 * a) ^ 2 := by
        apply (eq_div_iff (pow_ne_zero _ hDen)).mpr
        linear_combination a * hd₂
      _ = _ := by ring
  have ht : t < 3 / 2 := log_four_bounds.2.trans (by norm_num)
  have hY : 3 / 2 < t + r := by
    by_contra! h
    have hR : 0 ≤ 3 / 2 - t - r := by linarith only [h]
    have hS : 0 ≤ 3 / 2 - t - s := by linarith only [ht, hs]
    have hN := mul_nonneg (mul_nonneg ha.le hR) hS
    rw [← hF, show t + (3 / 2 - t) = 3 / 2 by ring] at hN
    exact (not_lt_of_ge hN) (spatial_neg_at_three_halves hp hP)
  have hZero : zetaCurvatureQuadratic p (t + r) = 0 := by rw [hF, sub_self, mul_zero, zero_mul]
  have hNeg (y : ℝ) (hy : t + r ≤ y) : peanoExponentQuadratic p y ≤ 0 := by
    let Y := t + r
    have hL : 4 * p + 2 - 2 * p * (p + 1) * Y ≤ 0 := by
      have h := mul_le_mul_of_nonneg_left hY.le (show 0 ≤ 2 * p * (p + 1) by positivity)
      nlinarith only [h, mul_nonneg (sub_nonneg.mpr hp) (show 0 ≤ 3 * p + 2 by positivity)]
    have hQ : peanoExponentQuadratic p Y ≤ 0 := by
      have hE : (p + 2) * peanoExponentQuadratic p Y = 4 * p + 2 - 2 * p * (p + 1) * Y := by
        unfold peanoExponentQuadratic
        change zetaCurvatureQuadratic p Y = 0 at hZero
        unfold zetaCurvatureQuadratic at hZero
        linear_combination -hZero
      exact nonpos_of_mul_nonpos_right (hE.trans_le hL) (by positivity : 0 < p + 2)
    have hE : peanoExponentQuadratic p y = peanoExponentQuadratic p Y +
        (y - Y) * (4 * p + 2 - 2 * p * (p + 1) * Y) - p * (p + 1) * (y - Y) ^ 2 := by
      unfold peanoExponentQuadratic
      ring
    rw [hE]
    exact sub_nonpos.mpr ((add_nonpos hQ (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hy) hL)).trans
      (by positivity))
  let X := Real.exp (t + r)
  have hX₀ : 0 < X := Real.exp_pos _
  have hX : 4 ≤ X := by
    have h := Real.exp_le_exp.mpr (show t ≤ t + r by linarith only [hr])
    simpa only [t, X, Real.exp_log (by norm_num : (0 : ℝ) < 4)] using h
  have hShift (x : ℝ) : zetaCurvatureQuadratic p (Real.log x) =
      a * (Real.log x - t - r) * (Real.log x - t - s) := by
    have h := hF (Real.log x - t)
    rwa [add_sub_cancel] at h
  refine ⟨X, hX, ?_, ?_⟩
  · intro x hx
    have hx₀ : 0 < x := (by norm_num : (0 : ℝ) < 4).trans_le hx.1
    have hL : t ≤ Real.log x := Real.log_le_log (by norm_num) hx.1
    have hR : Real.log x ≤ t + r := by simpa only [X, Real.log_exp] using Real.log_le_log hx₀ hx.2
    rw [zetaCurvatureSpatial, hShift]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hx₀.le _)
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos ha.le (by linarith only [hR]))
        (by linarith only [hs, hL]))
  · intro x hx
    have hx₀ : 0 < x := hX₀.trans_le hx
    have hR : t + r ≤ Real.log x := by simpa only [X, Real.log_exp] using Real.log_le_log hX₀ hx
    constructor
    · rw [zetaCurvatureSpatial, hShift]
      exact mul_nonneg (Real.rpow_nonneg hx₀.le _) (mul_nonneg
        (mul_nonneg ha.le (by linarith only [hR])) (by linarith only [hR, hr, hs]))
    · exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hx₀.le _) (hNeg _ hR)

theorem zetaCurvature_positiveVariation_le_of_slope {p N c : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hN : 4 ≤ N) (hc : 0 ≤ c) (hSlope : ∀ x ≥ 4, -c ≤ zetaCurvatureSlope p x) :
    (∫ x in (4 : ℝ)..N, max 0 (zetaCurvatureSpatial p x)) ≤ c := by
  obtain ⟨X, hX, hLeft, hRight⟩ := spatial_cut hp hP
  have hC {a b : ℝ} (ha : 4 ≤ a) (hab : a ≤ b) :
      IntervalIntegrable (fun x => max 0 (zetaCurvatureSpatial p x)) volume a b := by
    have h : ContinuousOn (zetaCurvatureSpatial p) (Icc a b) :=
      (zetaCurvatureSpatial_continuousOn p).mono
        (fun x hx => (by norm_num : (0 : ℝ) < 4).trans_le (ha.trans hx.1))
    exact (continuous_max.comp_continuousOn (continuousOn_const.prodMk h)).intervalIntegrable_of_Icc hab
  have hZ (b : ℝ) (hb : 4 ≤ b) (hbx : b ≤ X) :
      (∫ x in (4 : ℝ)..b, max 0 (zetaCurvatureSpatial p x)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => 0) (fun x hx => ?_), intervalIntegral.integral_zero]
    rw [uIcc_of_le hb] at hx
    exact max_eq_left (hLeft x ⟨hx.1, hx.2.trans hbx⟩)
  rcases le_or_gt N X with h | h
  · rwa [hZ N hN h]
  · have hSpl := intervalIntegral.integral_add_adjacent_intervals (hC le_rfl hX) (hC hX h.le)
    rw [hZ X hX le_rfl, zero_add] at hSpl
    rw [← hSpl]
    have hS : (∫ x in X..N, max 0 (zetaCurvatureSpatial p x)) =
        (∫ x in X..N, zetaCurvatureSpatial p x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le h.le] at hx
      exact max_eq_right (hRight x hx.1).1
    rw [hS, intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => zetaCurvatureSlope_hasDerivAt p (by
        rw [uIcc_of_le h.le] at hx
        exact (by norm_num : (0 : ℝ) < 4).trans_le (hX.trans hx.1)))
      (((zetaCurvatureSpatial_continuousOn p).mono (fun x hx =>
        (by norm_num : (0 : ℝ) < 4).trans_le (hX.trans hx.1))).intervalIntegrable_of_Icc h.le)]
    have hL := hSlope X hX
    have hR := (hRight N h.le).2
    linarith only [hL, hR]

theorem zetaCurvature_positiveVariation_le {p N : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hN : 4 ≤ N) :
    (∫ x in (4 : ℝ)..N, max 0 (zetaCurvatureSpatial p x)) ≤ 4 / 125 :=
  zetaCurvature_positiveVariation_le_of_slope hp hP hN (by norm_num) (fun _ hx => slope_lower hp hP hx)

end ACS12.GammaMeasure

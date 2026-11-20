import ACS12.JointLogQUpper

/-! The complete lower Q curvature bound and its integrated first-moment bounds. -/
namespace ACS12.GammaMeasure

open Set Filter MeasureTheory intervalIntegral
open scoped Topology

private theorem slope_three_le_one {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    zetaCurvatureSlope p 3 ≤ zetaCurvatureSlope 1 3 := by
  let l := Real.log 3
  let R (p : ℝ) := p * (p + 1) * l ^ 2 - (6 * p + 3) * l + 6
  have hl : (1098612 / 1000000 : ℝ) < l := log_three_tight.1
  have hl' : l < 1098613 / 1000000 := log_three_tight.2
  have hR₁ : R 1 < 0 := by
    have h := pow_le_pow_left₀ (by linarith only [hl] : 0 ≤ l) hl'.le 2
    dsimp only [R]
    linarith only [h,hl]
  have hR₂ : R (9 / 5) < 0 := by
    have h := pow_le_pow_left₀ (by linarith only [hl] : 0 ≤ l) hl'.le 2
    dsimp only [R]
    linarith only [h,hl]
  have hR (p : ℝ) (hp : 1 ≤ p) (hP : p ≤ 9 / 5) : R p ≤ 0 := by
    let t := (5 / 4) * (p - 1)
    have ht : 0 ≤ t := by dsimp only [t]; linarith only [hp]
    have ht' : t ≤ 1 := by dsimp only [t]; linarith only [hP]
    have hEq : R p = (1 - t) * R 1 + t * R (9 / 5) -
        ((p - 1) * (9 / 5 - p)) * l ^ 2 := by dsimp only [R,t]; ring
    rw [hEq]
    exact sub_nonpos.mpr ((add_nonpos (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht') hR₁.le)
      (mul_nonpos_of_nonneg_of_nonpos ht hR₂.le)).trans
      (mul_nonneg (mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hP)) (sq_nonneg l)))
  have hD (p : ℝ) : HasDerivAt (fun q => zetaCurvatureSlope q 3) ((3 : ℝ) ^ (-(p + 2)) * l * R p) p := by
    let h := hasDerivAt_id p
    have hA := (((h.mul (h.add_const 1)).const_mul (-(l ^ 2))).add
      ((((h.const_mul 4).const_add 2).const_mul l))).sub_const 2
    have hB : HasDerivAt (fun q => peanoExponentQuadratic q l) ((4 - (2 * p + 1) * l) * l) p := by
      convert hA using 1
      · funext q
        simp only [peanoExponentQuadratic,Pi.mul_apply,Pi.add_apply,id_eq]
        ring
      · simp only [id_eq,mul_one,one_mul]
        ring
    have hPow : HasDerivAt (fun q : ℝ => (3 : ℝ) ^ (-(q + 2))) ((3 : ℝ) ^ (-(p + 2)) * (-l)) p := by
      convert (h.add_const 2).neg.const_rpow (by norm_num : (0 : ℝ) < 3) using 1
      simp only [id_eq,Pi.neg_apply,l]
      ring
    convert hPow.mul hB using 1
    dsimp only [R,peanoExponentQuadratic]
    ring
  have hM : AntitoneOn (fun q => zetaCurvatureSlope q 3) (Icc 1 (9 / 5)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · exact fun q _ => (hD q).continuousAt.continuousWithinAt
    · exact fun q _ => (hD q).differentiableAt.differentiableWithinAt
    · intro q hq
      have hq' : q ∈ Icc (1 : ℝ) (9 / 5) := interior_subset hq
      rw [(hD q).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (by linarith only [hl])) (hR q hq'.1 hq'.2)
  exact hM (show (1 : ℝ) ∈ Icc 1 (9 / 5) by constructor <;> norm_num) ⟨hp,hP⟩ hp

private theorem slope_le_positive_one {p x : ℝ} (hp : 1 ≤ p) (hx : 4 ≤ x) :
    zetaCurvatureSlope p x ≤ max 0 (zetaCurvatureSlope 1 x) := by
  let l := Real.log x
  let B (p : ℝ) := peanoExponentQuadratic p l
  have hx₀ : 0 < x := (by norm_num : (0 : ℝ) < 4).trans_le hx
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hl : (4 / 3 : ℝ) < l := by linarith only [h4,Real.log_two_gt_d9,Real.log_le_log (by norm_num : (0 : ℝ) < 4) hx]
  have hB : B p ≤ B 1 := by
    have hD : B p - B 1 = (p - 1) * l * (4 - (p + 2) * l) := by dsimp only [B,peanoExponentQuadratic]; ring
    apply sub_nonpos.mp
    rw [hD]
    have h := mul_le_mul (show (3 : ℝ) ≤ p + 2 by linarith only [hp]) hl.le
      (by norm_num) (by linarith only [hp])
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (sub_nonneg.mpr hp) (by linarith only [hl])) (by linarith only [h])
  by_cases h : 0 ≤ B p
  · have hW : x ^ (-(p + 2)) ≤ x ^ (-(1 + 2 : ℝ)) := by
      exact Real.rpow_le_rpow_of_exponent_le (by linarith only [hx]) (by linarith only [hp])
    exact (mul_le_mul hW hB h (Real.rpow_nonneg hx₀.le _)).trans (le_max_right _ _)
  · exact (mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hx₀.le _) (le_of_not_ge h)).trans (le_max_left _ _)

private noncomputable def positiveSlopeOne (x : ℝ) : ℝ := max 0 (zetaCurvatureSlope 1 x)

private theorem positiveSlopeOne_at_three_lt : positiveSlopeOne 3 < 81 / 1000 := by
  have hL := log_three_tight.1
  have hU := log_three_tight.2
  have hSq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1098612 / 1000000) hL.le 2
  unfold positiveSlopeOne
  apply max_lt (by norm_num)
  unfold zetaCurvatureSlope peanoExponentQuadratic
  norm_num [Real.rpow_neg,Real.rpow_ofNat]
  linarith only [hSq,hU]

private theorem zetaCurvature_one_lt {x : ℝ} (hx₃ : 3 ≤ x) : zetaCurvature 1 x < 1 / 50 := by
  let l := Real.log x
  have hx : 0 < x := by linarith only [hx₃]
  have hl₀ : 0 ≤ l := Real.log_nonneg (by linarith only [hx₃])
  by_cases hl : l ≤ 2
  · exact (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (Real.rpow_nonneg hx.le _) hl₀)
      (by linarith only [hl] : 1 * l - 2 ≤ 0)).trans_lt (by norm_num)
  · let y := l - 2
    have hy : 0 ≤ y := sub_nonneg.mpr (le_of_not_ge hl)
    have hE : 2 * y + y ^ 2 ≤ Real.exp (2 * y) := by
      have h := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 * y by positivity)
      nlinarith only [h,sq_nonneg y]
    have hB := mul_le_mul_of_nonneg_right hE (Real.exp_pos (-2 * y)).le
    rw [← Real.exp_add,show 2 * y + -2 * y = 0 by ring,Real.exp_zero] at hB
    have hEq : zetaCurvature 1 x = Real.exp (-4) * ((2 * y + y ^ 2) * Real.exp (-2 * y)) := by
      unfold zetaCurvature
      rw [Real.rpow_def_of_pos hx]
      have hX : Real.log x * (-(1 + 1 : ℝ)) = -4 + -2 * y := by dsimp only [y,l]; ring
      rw [hX,Real.exp_add]
      dsimp only [y,l]
      ring
    have h₁ : (27 / 10 : ℝ) < Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
    have h₂ := pow_lt_pow_left₀ h₁ (by norm_num) (by decide : 4 ≠ 0)
    rw [← Real.exp_nat_mul] at h₂
    have h₃ : (50 : ℝ) < Real.exp 4 := by norm_num at h₂; linarith only [h₂]
    rw [hEq]
    refine (mul_le_of_le_one_right (Real.exp_pos _).le hB).trans_lt ?_
    rw [Real.exp_neg,← one_div]
    exact one_div_lt_one_div_of_lt (by norm_num) h₃

private theorem positiveSlopeOne_control :
    AntitoneOn positiveSlopeOne (Ici 3) ∧
      ∀ b ≥ (3 : ℝ), (∫ x in (3 : ℝ)..b, positiveSlopeOne x) ≤ (1 / 50 + 1 / 9) := by
  let r : ℝ := (3 + Real.sqrt 5) / 2
  let r₀ : ℝ := (3 - Real.sqrt 5) / 2
  let c := Real.exp r
  have h5 : Real.sqrt (5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hS₀ : 0 ≤ Real.sqrt (5 : ℝ) := Real.sqrt_nonneg _
  have hS : (2 : ℝ) < Real.sqrt 5 := by
    by_contra! h
    have h' := pow_le_pow_left₀ hS₀ h 2
    linarith only [h',h5]
  have hS' : Real.sqrt (5 : ℝ) < 3 := by
    by_contra! h
    have h' := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) h 2
    linarith only [h',h5]
  have hr : 5 / 2 < r := by dsimp only [r]; linarith only [hS]
  have hr' : r < 3 := by dsimp only [r]; linarith only [hS']
  have hr₀ : r₀ < 1 := by dsimp only [r₀]; linarith only [hS]
  have hC : 3 ≤ c := by
    have h := Real.exp_le_exp.mpr (show Real.log 3 ≤ r by linarith only [log_three_tight.2,hr])
    simpa only [c,Real.exp_log (by norm_num : (0 : ℝ) < 3)] using h
  have hFactor (l : ℝ) : peanoExponentQuadratic 1 l = -2 * (l - r) * (l - r₀) := by
    unfold peanoExponentQuadratic
    dsimp only [r,r₀]
    linear_combination -(1 / 2 : ℝ) * h5
  have hLog (x : ℝ) (hx : 3 ≤ x) : 1 < Real.log x :=
    (by linarith only [log_three_tight.1] : (1 : ℝ) < Real.log 3).trans_le (Real.log_le_log (by norm_num) hx)
  have hLeft (x : ℝ) (hx : x ∈ Icc 3 c) : 0 ≤ zetaCurvatureSlope 1 x := by
    have hR : Real.log x ≤ r := by
      simpa only [c,Real.log_exp] using Real.log_le_log (by linarith only [hx.1] : 0 < x) hx.2
    rw [zetaCurvatureSlope,hFactor]
    exact mul_nonneg (Real.rpow_nonneg (by linarith only [hx.1]) _)
      (mul_nonneg (mul_nonneg_of_nonpos_of_nonpos (by norm_num) (sub_nonpos.mpr hR))
        (by linarith only [hLog x hx.1,hr₀]))
  have hRight (x : ℝ) (hx : c ≤ x) : zetaCurvatureSlope 1 x ≤ 0 := by
    have hR : r ≤ Real.log x := by simpa only [c,Real.log_exp] using Real.log_le_log (Real.exp_pos r) hx
    have h₀ := hC.trans hx
    rw [zetaCurvatureSlope,hFactor]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (by linarith only [h₀]) _)
      (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sub_nonneg.mpr hR))
        (by linarith only [hLog x h₀,hr₀]))
  have hD (x : ℝ) (hx : 0 < x) := zetaCurvatureSlope_hasDerivAt 1 hx
  have hM : AntitoneOn (zetaCurvatureSlope 1) (Icc 3 c) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · exact fun x hx => (hD x (by linarith only [hx.1])).continuousAt.continuousWithinAt
    · exact fun x hx => (hD x (by have hx' := (interior_subset hx : x ∈ Icc 3 c).1; linarith only [hx'])).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Icc 3 c := interior_subset hx
      have hx₀ : 0 < x := by linarith only [hx'.1]
      have hR : Real.log x ≤ r := by simpa only [c,Real.log_exp] using Real.log_le_log hx₀ hx'.2
      rw [(hD x hx₀).deriv,zetaCurvatureSpatial]
      have hQ : zetaCurvatureQuadratic 1 (Real.log x) = 6 * (Real.log x - 2 / 3) * (Real.log x - 3) := by
        unfold zetaCurvatureQuadratic; ring
      rw [hQ]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hx₀.le _)
        (mul_nonpos_of_nonneg_of_nonpos (by linarith only [hLog x hx'.1]) (by linarith only [hR,hr']))
  have hCts {a b : ℝ} (ha : 3 ≤ a) (hab : a ≤ b) : IntervalIntegrable positiveSlopeOne volume a b := by
    have h : ContinuousOn (zetaCurvatureSlope 1) (Icc a b) := by
      intro x hx
      exact (hD x (by linarith only [ha,hx.1])).continuousAt.continuousWithinAt
    exact (continuous_max.comp_continuousOn (continuousOn_const.prodMk h)).intervalIntegrable_of_Icc hab
  have hInt (b : ℝ) (hb : 3 ≤ b) (hbc : b ≤ c) :
      (∫ x in (3 : ℝ)..b, positiveSlopeOne x) ≤ 1 / 50 + 1 / 9 := by
    have hEq : (∫ x in (3 : ℝ)..b, positiveSlopeOne x) =
        ∫ x in (3 : ℝ)..b, zetaCurvatureSlope 1 x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hb] at hx
      exact max_eq_right (hLeft x ⟨hx.1,hx.2.trans hbc⟩)
    have hI : IntervalIntegrable (zetaCurvatureSlope 1) volume 3 b := by
      apply ContinuousOn.intervalIntegrable_of_Icc hb
      exact fun x hx => (hD x (by linarith only [hx.1])).continuousAt.continuousWithinAt
    rw [hEq,intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => zetaCurvature_hasDerivAt 1 (by rw [uIcc_of_le hb] at hx; linarith only [hx.1])) hI]
    have h3 : -(1 / 9) ≤ zetaCurvature 1 3 := by
      unfold zetaCurvature
      norm_num [Real.rpow_neg,Real.rpow_two,Real.rpow_ofNat]
      nlinarith only [sq_nonneg (Real.log 3 - 1)]
    linarith only [h3,zetaCurvature_one_lt hb]
  constructor
  · intro x hx y hy hxy
    by_cases hy' : y ≤ c
    · have hX : x ∈ Icc 3 c := ⟨hx,hxy.trans hy'⟩
      have hY : y ∈ Icc 3 c := ⟨hy,hy'⟩
      unfold positiveSlopeOne
      rw [max_eq_right (hLeft x hX),max_eq_right (hLeft y hY)]
      exact hM hX hY hxy
    · unfold positiveSlopeOne
      rw [max_eq_left (hRight y (le_of_not_ge hy'))]
      exact le_max_left _ _
  · intro b hb
    rcases le_or_gt b c with h | h
    · exact hInt b hb h
    · have hZ : (∫ x in c..b, positiveSlopeOne x) = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => 0) (fun x hx => ?_),intervalIntegral.integral_zero]
        rw [uIcc_of_le h.le] at hx
        exact max_eq_left (hRight x hx.1)
      have hS := intervalIntegral.integral_add_adjacent_intervals (hCts le_rfl hC) (hCts hC h.le)
      rw [hZ,add_zero] at hS
      rw [← hS]
      exact hInt c hC le_rfl

theorem slope_tail_three_le {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    (∑' j : ℕ, zetaCurvatureSlope p (3 + (j : ℝ))) ≤
      positiveSlopeOne 3 + (1 / 50 + 1 / 9) := by
  obtain ⟨hM,hI⟩ := positiveSlopeOne_control
  have hS (N : ℕ) : (∑ j ∈ Finset.range N, positiveSlopeOne (3 + (j + 1 : ℕ))) ≤
      ∫ x in (3 : ℝ)..(3 + (N : ℝ)), positiveSlopeOne x := by
    have hC (j : ℕ) : IntervalIntegrable positiveSlopeOne volume (3 + (j : ℝ)) (3 + (j + 1 : ℕ)) := by
      have ha : (3 : ℝ) ≤ 3 + j := le_add_of_nonneg_right (Nat.cast_nonneg _)
      have hab : (3 : ℝ) + j ≤ 3 + (j + 1 : ℕ) :=
        add_le_add_right (Nat.cast_le.mpr (Nat.le_succ j)) _
      have hD : ContinuousOn (zetaCurvatureSlope 1) (Icc (3 + j : ℝ) (3 + (j + 1 : ℕ))) := by
        intro x hx
        exact (zetaCurvatureSlope_hasDerivAt 1 (by linarith only [ha,hx.1] : 0 < x)).continuousAt.continuousWithinAt
      exact (continuous_max.comp_continuousOn (continuousOn_const.prodMk hD)).intervalIntegrable_of_Icc hab
    have hCell (j : ℕ) : positiveSlopeOne (3 + (j + 1 : ℕ)) ≤
        ∫ x in (3 + j : ℝ)..(3 + (j + 1 : ℕ)), positiveSlopeOne x := by
      let a : ℝ := 3 + j
      let b : ℝ := 3 + (j + 1 : ℕ)
      have hA : 3 ≤ a := le_add_of_nonneg_right (Nat.cast_nonneg _)
      have hE : b - a = 1 := by dsimp only [a,b]; push_cast; ring
      have hab : a ≤ b := by linarith only [hE]
      have h := intervalIntegral.integral_mono_on hab
        (intervalIntegral.intervalIntegrable_const (c := positiveSlopeOne b)) (hC j)
        (fun x hx => hM (hA.trans hx.1) (hA.trans hab) hx.2)
      rw [intervalIntegral.integral_const,smul_eq_mul,hE,one_mul] at h
      exact h
    have h := Finset.sum_le_sum (s := Finset.range N) (fun j _ => hCell j)
    rwa [intervalIntegral.sum_integral_adjacent_intervals (a := fun j => 3 + (j : ℝ))
      (fun j _ => hC j),Nat.cast_zero,add_zero] at h
  have hFin (N : ℕ) : (∑ j ∈ Finset.range (N + 1), zetaCurvatureSlope p (3 + (j : ℝ))) ≤
      positiveSlopeOne 3 + (1 / 50 + 1 / 9) := by
    rw [Finset.sum_range_succ',Nat.cast_zero,add_zero]
    have hOne : zetaCurvatureSlope p 3 ≤ positiveSlopeOne 3 :=
      (slope_three_le_one hp hP).trans (le_max_right _ _)
    have hPoint (j : ℕ) :
        zetaCurvatureSlope p (3 + ((j + 1 : ℕ) : ℝ)) ≤ positiveSlopeOne (3 + ((j + 1 : ℕ) : ℝ)) :=
      slope_le_positive_one hp (by
        have h : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_pos j)
        linarith only [h])
    have hTail := Finset.sum_le_sum (s := Finset.range N) (fun j _ => hPoint j)
    have hB := (hS N).trans (hI _ (le_add_of_nonneg_right (Nat.cast_nonneg _)))
    linarith only [hOne,hTail,hB]
  have hT := (zetaSlope_summable hp 3 (by decide)).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  exact le_of_tendsto_of_tendsto hT tendsto_const_nhds (Eventually.of_forall hFin)

theorem pureQSecond_gt {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    8 / 5 < pureQSecond p := by
  have h := pureQSecond_eq_tail hp 2
  have h1 : zetaCurvatureSlope p 1 = -2 := by simp [zetaCurvatureSlope,peanoExponentQuadratic]
  norm_num [Finset.sum_range_succ,h1] at h
  linarith only [h,slope_tail_three_le hp hP,positiveSlopeOne_at_three_lt,zetaSlope_two_lt hp hP]

end ACS12.GammaMeasure

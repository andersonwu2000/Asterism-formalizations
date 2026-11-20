import ACS12.PressureWeightedIdentity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Exponent order and the sign estimates on the entire weighted entropy support. -/

namespace ACS12.Pressure

open Set MeasureTheory

theorem weightedPressureEntropy_mono {p P sigma lam x y : ℝ} (hp : 1 < p) (hpP : p ≤ P)
    (hs : 0 ≤ sigma) (hLam : 0 ≤ lam) :
    weightedPressureEntropy lam p sigma x y ≤ weightedPressureEntropy lam P sigma x y := by
  have hp₀ := zero_lt_one.trans hp
  have hP := hp₀.trans_le hpP
  have hAdd : p + 1 ≤ P + 1 := by linarith only [hpP]
  have hAdd₀ : 0 < p + 1 := by positivity
  have hb (r : ℝ) (hr : 0 < r) : pressureB r = 1 - 1 / r := by
    unfold pressureB
    field_simp [hr.ne']
  have hBeta (r : ℝ) (hr : 0 < r) : pressureBeta r = 1 - 1 / (r + 1) := by
    unfold pressureBeta
    field_simp [show r + 1 ≠ 0 by positivity]
    ring
  have hc (r : ℝ) (hr : 0 < r) : pressureC r = 1 - 2 / (r + 1) := by
    unfold pressureC
    field_simp [show r + 1 ≠ 0 by positivity]
    ring
  have hB : pressureB p ≤ pressureB P := by
    rw [hb p hp₀,hb P hP]
    exact sub_le_sub_left (one_div_le_one_div_of_le hp₀ hpP) _
  have hβ : pressureBeta p ≤ pressureBeta P := by
    rw [hBeta p hp₀,hBeta P hP]
    exact sub_le_sub_left (one_div_le_one_div_of_le hAdd₀ hAdd) _
  have hC : pressureC p ≤ pressureC P := by
    rw [hc p hp₀,hc P hP]
    exact sub_le_sub_left (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hAdd₀ hAdd) _
  have hT : pressureTau p sigma ≤ pressureTau P sigma := by
    unfold pressureTau
    apply Real.exp_le_exp.mpr
    rw [neg_div,neg_div]
    exact neg_le_neg (div_le_div_of_nonneg_left hs (by positivity)
      (mul_le_mul hpP hAdd hAdd₀.le hP.le))
  have hB₀ : 0 ≤ pressureB p := div_nonneg (sub_nonneg.mpr hp.le) hp₀.le
  have hβ₀ : 0 ≤ pressureBeta p := by unfold pressureBeta; positivity
  have hC₀ : 0 ≤ pressureC p := div_nonneg (sub_nonneg.mpr hp.le) (by positivity)
  have hB' (z : ℝ) := entropyExp_scale_mono z hB₀ (hB₀.trans hB) hB
  have hβ' (z : ℝ) := entropyExp_scale_mono z hβ₀ (hβ₀.trans hβ) hβ
  have hC' := entropyExp_scale_mono (-(x + y) / 2) hC₀ (hC₀.trans hC) hC
  have hτ (r : ℝ) : 0 < pressureTau r sigma := Real.exp_pos _
  have hB'' := mul_le_mul (mul_le_mul hpP hT (hτ p).le hP.le) (add_le_add (hB' x) (hB' y))
    (add_nonneg (entropyExp_nonneg _) (entropyExp_nonneg _)) (mul_nonneg hP.le (hτ P).le)
  have hβ'' := mul_le_mul (mul_le_mul_of_nonneg_left hAdd hLam)
    (add_le_add (hβ' x) (hβ' y)) (add_nonneg (entropyExp_nonneg _) (entropyExp_nonneg _))
    (mul_nonneg hLam (by positivity : 0 ≤ P + 1))
  have hT' : lam + pressureTau p sigma ≤ lam + pressureTau P sigma := by linarith only [hT]
  have hC'' := mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hAdd (by norm_num : (0 : ℝ) ≤ 2))
    hT' (add_nonneg hLam (hτ p).le) (by positivity : 0 ≤ 2 * (P + 1))) hC'
    (entropyExp_nonneg _) (mul_nonneg (by positivity) (add_nonneg hLam (hτ P).le))
  unfold weightedPressureEntropy
  exact sub_le_sub_right (add_le_add (add_le_add hB'' hC'') hβ'') _

private noncomputable def negativeEntropyWord (tau x : ℝ) : ℝ :=
  (9 / 5) * tau * entropyExp ((4 / 9) * x) +
    (14 / 5) * (28 / 27) * entropyExp ((9 / 14) * x) - (28 / 27) * entropyExp x

private theorem entropyExp_neg_scale {a v : ℝ} (ha : 0 ≤ a) (ha₁ : a ≤ 1) (hv : 0 ≤ v) :
    a ^ 2 * entropyExp (-v) ≤ entropyExp (-(a * v)) := by
  let G (t : ℝ) := entropyExp (-(a * t)) - a ^ 2 * entropyExp (-t)
  let H (t : ℝ) := a * (1 - Real.exp (-(a * t))) - a ^ 2 * (1 - Real.exp (-t))
  have hH (t : ℝ) : HasDerivAt H (a ^ 2 * (Real.exp (-(a * t)) - Real.exp (-t))) t := by
    have ht := hasDerivAt_id t
    convert (((((ht.const_mul a).neg.exp).const_sub 1).const_mul a).sub
      ((ht.neg.exp.const_sub 1).const_mul (a ^ 2))) using 1
    simp only [Pi.neg_apply,id_eq,mul_one]
    ring
  have hM : MonotoneOn H (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
      (fun t _ => (hH t).continuousAt.continuousWithinAt)
      (fun t _ => (hH t).differentiableAt.differentiableWithinAt)
    intro t ht
    have ht₀ : 0 ≤ t := interior_subset ht
    rw [(hH t).deriv]
    exact mul_nonneg (sq_nonneg a) (sub_nonneg.mpr (Real.exp_le_exp.mpr (by
      linarith only [mul_le_of_le_one_left ht₀ ha₁])))
  have h₀ : H 0 = 0 := by simp [H]
  have hG (t : ℝ) : HasDerivAt G (H t) t := by
    have ht := hasDerivAt_id t
    have h₁ := (((ht.const_mul a).neg.exp).sub_const 1).sub ((ht.const_mul a).neg)
    have h₂ := ((ht.neg.exp.sub_const 1).sub ht.neg).const_mul (a ^ 2)
    convert h₁.sub h₂ using 1
    simp only [H,Pi.neg_apply,id_eq,mul_one]
    ring
  have hMG : MonotoneOn G (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
      (fun t _ => (hG t).continuousAt.continuousWithinAt)
      (fun t _ => (hG t).differentiableAt.differentiableWithinAt)
    intro t ht
    have ht₀ : 0 ≤ t := interior_subset ht
    rw [(hG t).deriv,← h₀]
    exact hM (mem_Ici.mpr le_rfl) ht₀ ht₀
  have h := hMG (mem_Ici.mpr le_rfl) hv hv
  have hZ : G 0 = 0 := by simp [G,entropyExp]
  rw [hZ] at h
  exact sub_nonneg.mp h

private theorem entropyExp_neg_lower {v : ℝ} (hv : 0 ≤ v) (hV : v ≤ Real.log 13)
    (hLog : Real.log 13 < 13 / 5) :
    (545 / 2197 : ℝ) * v ^ 2 ≤ entropyExp (-v) := by
  let L := Real.log 13
  have hL : 0 < L := Real.log_pos (by norm_num)
  have hE : Real.exp (-L) = 1 / 13 := by
    unfold L
    rw [Real.exp_neg,Real.exp_log (by norm_num)]
    exact inv_eq_one_div _
  have hScale := entropyExp_neg_scale (a := v / L) (v := L)
    (div_nonneg hv hL.le) ((div_le_one hL).mpr hV) hL.le
  rw [div_mul_cancel₀ _ hL.ne'] at hScale
  have hL₀ : 5 / 2 < L := by
    have hE₁ : Real.exp 1 < 11 / 4 := by linarith only [Real.exp_one_lt_d9]
    have hE₂ : Real.exp (1 / 2) < 5 / 3 := by
      apply lt_of_pow_lt_pow_left₀ 2 (by norm_num)
      rw [pow_two,← Real.exp_add,show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num]
      exact hE₁.trans (by norm_num)
    have hE₃ : Real.exp (5 / 2) < 13 := by
      rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num,Real.exp_add,
        show (2 : ℝ) = (2 : ℕ) * (1 : ℝ) by norm_num,Real.exp_nat_mul]
      have hP := pow_lt_pow_left₀ hE₁ (Real.exp_pos _).le (by decide : (2 : ℕ) ≠ 0)
      simpa only [Nat.cast_ofNat,mul_one] using
        (mul_lt_mul hP hE₂.le (Real.exp_pos _) (by norm_num : (0 : ℝ) ≤ (11 / 4) ^ 2)).trans
          (by norm_num : (11 / 4 : ℝ) ^ 2 * (5 / 3) < 13)
    apply Real.exp_lt_exp.mp
    simpa only [L,Real.exp_log (by norm_num : (0 : ℝ) < 13)] using hE₃
  have hP : (545 / 2197 : ℝ) * L ^ 2 ≤ L - 12 / 13 := by
    have hM' := mul_nonneg (sub_nonneg.mpr hLog.le)
      (show 0 ≤ (545 / 2197 : ℝ) * (L + 13 / 5) - 1 by linarith only [hL₀])
    nlinarith only [hM']
  have hE' : (545 / 2197 : ℝ) * L ^ 2 ≤ entropyExp (-L) := by
    unfold entropyExp
    linarith only [hE,hP]
  have h := mul_le_mul_of_nonneg_left hE' (sq_nonneg (v / L))
  have hEq : (v / L) ^ 2 * ((545 / 2197 : ℝ) * L ^ 2) = (545 / 2197) * v ^ 2 := by
    field_simp [hL.ne']
  exact (hEq ▸ h).trans hScale

private theorem negativeEntropyWord_lower {tau v : ℝ} (hTau : 3 / 5 ≤ tau)
    (hv : 0 < v) (hV : v ≤ Real.log 13) (hLog : Real.log 13 < 13 / 5) :
    (93 / 1000 : ℝ) * v ^ 2 < negativeEntropyWord tau (-v) := by
  have hA := entropyExp_neg_scale (a := 4 / 9) (by norm_num) (by norm_num) hv.le
  have hB := entropyExp_neg_scale (a := 9 / 14) (by norm_num) (by norm_num) hv.le
  have hC := entropyExp_neg_lower hv.le hV hLog
  have h₁ := mul_le_mul_of_nonneg_left hA (show 0 ≤ (9 / 5 : ℝ) * tau by linarith only [hTau])
  have h₂ := mul_le_mul_of_nonneg_left hB (show 0 ≤ (14 / 5 : ℝ) * (28 / 27) by norm_num)
  have h₃ := mul_le_mul_of_nonneg_right hTau (entropyExp_nonneg (-v))
  have h₄ := mul_le_mul_of_nonneg_left hC
    (show 0 ≤ (16 / 75 : ℝ) + (28 / 27) * (11 / 70) by norm_num)
  have h₅ := mul_pos (by norm_num : (0 : ℝ) < 27686 / 296595 - 93 / 1000) (sq_pos_of_pos hv)
  unfold negativeEntropyWord
  rw [show (4 / 9 : ℝ) * -v = -(4 / 9 * v) by ring,
    show (9 / 14 : ℝ) * -v = -(9 / 14 * v) by ring]
  nlinarith only [h₁,h₂,h₃,h₄,h₅]

private noncomputable def entropyAnchor : ℝ := Real.exp (-(25 / 126) * Real.log 13)

private noncomputable def entropyEta (t : ℝ) : ℝ := entropyAnchor * Real.exp ((25 / 126) * t)

private noncomputable def positiveEntropyWord (t : ℝ) : ℝ :=
  negativeEntropyWord (entropyEta t) t +
    (28 / 5) * (28 / 27 + entropyEta t) * entropyExp (-(1 / 7) * t)

private theorem entropyAnchor_bounds :
    (3 / 5 : ℝ) < entropyAnchor ∧ entropyAnchor < 5 / 8 := by
  have hD : (0 : ℝ) < 25 / 126 := by norm_num
  have hL : (0 : ℝ) < Real.log 13 := Real.log_pos (by norm_num)
  constructor
  · have hPow : (3 / 5 : ℝ) ^ (126 : ℕ) < entropyAnchor ^ (126 : ℕ) := by
      unfold entropyAnchor
      rw [← Real.exp_nat_mul,
        show ((126 : ℕ) : ℝ) * (-(25 / 126) * Real.log 13) = -(25 * Real.log 13) by norm_num <;> ring,
        Real.exp_neg,show (25 : ℝ) = ((25 : ℕ) : ℝ) by norm_num,Real.exp_nat_mul,Real.exp_log (by norm_num)]
      norm_num
    exact lt_of_pow_lt_pow_left₀ 126 (Real.exp_pos _).le hPow
  · have hExp : (8 / 5 : ℝ) < Real.exp ((25 / 126) * Real.log 13) := by
      have hLog : (5 / 2 : ℝ) < Real.log 13 := by
        have hE₁ : Real.exp 1 < 11 / 4 := by linarith only [Real.exp_one_lt_d9]
        have hE₂ : Real.exp (1 / 2) < 5 / 3 := by
          apply lt_of_pow_lt_pow_left₀ 2 (by norm_num)
          rw [pow_two,← Real.exp_add,show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num]
          exact hE₁.trans (by norm_num)
        apply Real.exp_lt_exp.mp
        rw [Real.exp_log (by norm_num),show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num,Real.exp_add,
          show (2 : ℝ) = (2 : ℕ) * (1 : ℝ) by norm_num,Real.exp_nat_mul]
        have hP := pow_lt_pow_left₀ hE₁ (Real.exp_pos _).le (by decide : (2 : ℕ) ≠ 0)
        simpa only [Nat.cast_ofNat,mul_one] using
          (mul_lt_mul hP hE₂.le (Real.exp_pos _) (by norm_num : (0 : ℝ) ≤ (11 / 4) ^ 2)).trans
            (by norm_num : (11 / 4 : ℝ) ^ 2 * (5 / 3) < 13)
      have hC := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 125 / 252 by norm_num)
      have hM := Real.exp_le_exp.mpr (show (125 / 252 : ℝ) ≤ 25 / 126 * Real.log 13 by linarith only [hLog])
      exact (by norm_num : (8 / 5 : ℝ) < 1 + 125 / 252 + (125 / 252) ^ 2 / 2).trans_le
        (hC.trans hM)
    unfold entropyAnchor
    rw [show -(25 / 126 : ℝ) * Real.log 13 = -(25 / 126 * Real.log 13) by ring,Real.exp_neg]
    exact (inv_lt_comm₀ (Real.exp_pos _) (by norm_num)).mpr (by norm_num at hExp ⊢; exact hExp)

private theorem entropySupportLog_upper : Real.log 13 < 13 / 5 := by
  apply Real.exp_lt_exp.mp
  rw [Real.exp_log (by norm_num),show (13 / 5 : ℝ) = 2 + 3 / 5 by norm_num,Real.exp_add]
  have h₂ := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num) 6
  have h₅ := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 3 / 5 by norm_num) 4
  norm_num [Finset.sum_range_succ,Nat.factorial] at h₂ h₅
  exact (by norm_num : (13 : ℝ) < (109 / 15) * (9 / 5)).trans_le
    (mul_le_mul h₂ (show (9 / 5 : ℝ) ≤ Real.exp (3 / 5) by linarith only [h₅]) (by norm_num)
      (Real.exp_pos _).le)

private theorem positiveEntropyWord_atLog_pos : (4643/70200 : ℝ) < positiveEntropyWord (Real.log 13) := by
  have hL : (0 : ℝ) < 13 := by norm_num
  have hEta : entropyEta (Real.log 13) = 1 := by
    unfold entropyEta entropyAnchor
    rw [← Real.exp_add,show -(25 / 126 : ℝ) * Real.log 13 + 25 / 126 * Real.log 13 = 0 by ring,
      Real.exp_zero]
  have hExp (r : ℝ) : Real.exp (r * Real.log 13) = (13 : ℝ) ^ r := by
    rw [Real.rpow_def_of_pos hL,mul_comm]
  have h₁ : (25 / 8 : ℝ) < (13 : ℝ) ^ (4 / 9 : ℝ) := by
    apply (Real.rpow_lt_rpow_iff (by norm_num : (0 : ℝ) ≤ 25 / 8)
      (Real.rpow_nonneg hL.le _) (z := 9) (by norm_num)).mp
    rw [← Real.rpow_mul hL.le,show (4 / 9 : ℝ) * 9 = 4 by norm_num]
    norm_num [show (9 : ℝ) = (9 : ℕ) by norm_num,show (4 : ℝ) = (4 : ℕ) by norm_num,
      Real.rpow_natCast]
  have h₂ : (26 / 5 : ℝ) < (13 : ℝ) ^ (9 / 14 : ℝ) := by
    apply (Real.rpow_lt_rpow_iff (by norm_num : (0 : ℝ) ≤ 26 / 5)
      (Real.rpow_nonneg hL.le _) (z := 14) (by norm_num)).mp
    rw [← Real.rpow_mul hL.le,show (9 / 14 : ℝ) * 14 = 9 by norm_num]
    norm_num [show (14 : ℝ) = (14 : ℕ) by norm_num,show (9 : ℝ) = (9 : ℕ) by norm_num,
      Real.rpow_natCast]
  have h₃ : (9 / 13 : ℝ) < (13 : ℝ) ^ (-(1 / 7) : ℝ) := by
    apply (Real.rpow_lt_rpow_iff (by norm_num : (0 : ℝ) ≤ 9 / 13)
      (Real.rpow_nonneg hL.le _) (z := 7) (by norm_num)).mp
    rw [← Real.rpow_mul hL.le,show (-(1 / 7) : ℝ) * 7 = -1 by norm_num,Real.rpow_neg_one]
    norm_num [show (7 : ℝ) = (7 : ℕ) by norm_num,Real.rpow_natCast]
  unfold positiveEntropyWord negativeEntropyWord entropyExp
  rw [hEta,hExp,hExp,hExp,Real.exp_log hL]
  linarith only [h₁,h₂,h₃]

private noncomputable def positiveEntropyJet (k : ℕ) (t : ℝ) : ℝ :=
  ((9 / 5) * entropyAnchor + (14 / 5) * (28 / 27)) * (9 / 14 : ℝ) ^ k * Real.exp ((9 / 14) * t) +
    (28 / 5) * (28 / 27) * (-(1 / 7) : ℝ) ^ k * Real.exp (-(1 / 7) * t) +
    (28 / 5) * entropyAnchor * (1 / 18 : ℝ) ^ k * Real.exp ((1 / 18) * t) -
    (28 / 27) * Real.exp t - (37 / 5) * entropyAnchor * (25 / 126 : ℝ) ^ k * Real.exp ((25 / 126) * t) -
    (37 / 5) * (28 / 27) * (0 : ℝ) ^ k

private theorem positiveEntropyWord_eq_jet (t : ℝ) : positiveEntropyWord t = positiveEntropyJet 0 t := by
  unfold positiveEntropyWord negativeEntropyWord entropyEta entropyExp positiveEntropyJet
  have h₁ : Real.exp ((25 / 126) * t) * Real.exp ((4 / 9) * t) = Real.exp ((9 / 14) * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h₂ : Real.exp ((25 / 126) * t) * Real.exp (-((1 / 7) * t)) = Real.exp ((1 / 18) * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  norm_num
  linear_combination (9 / 5) * entropyAnchor * h₁ + (28 / 5) * entropyAnchor * h₂

private theorem positiveEntropyJet_deriv (k : ℕ) (t : ℝ) :
    HasDerivAt (positiveEntropyJet k) (positiveEntropyJet (k + 1) t) t := by
  have h (a c : ℝ) : HasDerivAt (fun x => c * Real.exp (a*x)) (c * (Real.exp (a*t) * a)) t := by
    simpa only [id_eq, mul_one] using (((hasDerivAt_id t).const_mul a).exp.const_mul c)
  unfold positiveEntropyJet
  convert (((((h (9/14) _).add (h (-(1/7)) _)).add (h (1/18) _)).sub
    ((Real.hasDerivAt_exp t).const_mul (28/27))).sub (h (25/126) _)).sub_const _ using 1
  simp only [pow_succ]
  ring

private theorem positiveEntropyJet_fourth_neg {t : ℝ} (ht : 0 ≤ t) :
    positiveEntropyJet 4 t < 0 := by
  let A := entropyAnchor
  let E := Real.exp ((9 / 14) * t)
  have hA : 0 ≤ A := (by norm_num : (0:ℝ) ≤ 3/5).trans entropyAnchor_bounds.1.le
  have hAU : A ≤ 5 / 8 := entropyAnchor_bounds.2.le
  have htE (r : ℝ) (hr : r ≤ 9 / 14) : Real.exp (r*t) ≤ E :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hr ht)
  have h₁ : ((9 / 5) * A + (14 / 5) * (28 / 27)) * (9 / 14 : ℝ)^4 * E ≤ (4 / 5) * E :=
    mul_le_mul_of_nonneg_right (by linarith [hAU]) (Real.exp_pos _).le
  have h₂ : (28 / 5) * (28 / 27) * (-(1 / 7) : ℝ)^4 * Real.exp (-(1 / 7) * t) ≤ (1 / 200) * E := by
    exact (mul_le_mul_of_nonneg_left (htE (-(1/7)) (by norm_num)) (by norm_num)).trans
      (mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos _).le)
  have h₃ : (28 / 5) * A * (1 / 18 : ℝ)^4 * Real.exp ((1 / 18) * t) ≤ (1 / 200) * E := by
    exact (mul_le_mul_of_nonneg_left (htE (1/18) (by norm_num)) (by positivity)).trans
      (mul_le_mul_of_nonneg_right (by linarith [hAU]) (Real.exp_pos _).le)
  have h₄ : E ≤ (28 / 27) * Real.exp t := by
    have h := Real.exp_le_exp.mpr (show (9/14 : ℝ)*t ≤ t by linarith)
    exact h.trans (le_mul_of_one_le_left (Real.exp_pos _).le (by norm_num))
  have h₅ : 0 ≤ (37 / 5) * A * (25 / 126 : ℝ)^4 * Real.exp ((25 / 126) * t) := by positivity
  have hE : 0 < E := Real.exp_pos _
  unfold positiveEntropyJet
  norm_num only [show (0 : ℝ)^4 = 0 by norm_num, mul_zero, sub_zero]
  linarith only [h₁,h₂,h₃,h₄,h₅,hE]

private noncomputable def normalizedEntropyWord (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1, (1-u) * positiveEntropyJet 2 (u*t)

private theorem normalizedEntropyWord_identity (t : ℝ) :
    t^2 * normalizedEntropyWord t = positiveEntropyWord t := by
  let F (u : ℝ) := t * (1-u) * positiveEntropyJet 1 (u*t) + positiveEntropyJet 0 (u*t)
  have hD (u : ℝ) : HasDerivAt F (t^2 * ((1-u) * positiveEntropyJet 2 (u*t))) u := by
    have hu := hasDerivAt_id u
    have hv := hu.mul_const t
    have h₁ := (positiveEntropyJet_deriv 1 (u*t)).comp u hv
    have h₀ := (positiveEntropyJet_deriv 0 (u*t)).comp u hv
    convert (((hu.const_sub 1).const_mul t).mul h₁).add h₀ using 1
    simp only [Function.comp_apply,id_eq,Nat.reduceAdd,one_mul]
    ring
  have hI : Continuous fun u : ℝ => t^2 * ((1-u) * positiveEntropyJet 2 (u*t)) := by
    unfold positiveEntropyJet
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (fun u _ => hD u) (hI.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul] at h
  have h₀ : F 0 = 0 := by simp [F,positiveEntropyJet]; ring
  rw [h₀,sub_zero] at h
  simpa [F,normalizedEntropyWord,positiveEntropyWord_eq_jet,mul_comm] using h

private theorem normalizedEntropyWord_concave : ConcaveOn ℝ (Ici 0) normalizedEntropyWord := by
  have hC : ConcaveOn ℝ (Ici 0) (positiveEntropyJet 2) := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ici _)
      (fun t _ => (positiveEntropyJet_deriv 2 t).continuousAt.continuousWithinAt)
      (fun t _ => (positiveEntropyJet_deriv 2 t).hasDerivWithinAt)
      (fun t _ => (positiveEntropyJet_deriv 3 t).hasDerivWithinAt)
    exact fun t ht => (positiveEntropyJet_fourth_neg (interior_subset ht)).le
  refine ⟨convex_Ici _,?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  unfold normalizedEntropyWord
  let f (t u : ℝ) := (1-u) * positiveEntropyJet 2 (u*t)
  have hI (t : ℝ) : IntervalIntegrable (f t) volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold f positiveEntropyJet
    fun_prop
  change a * (∫ u in (0 : ℝ)..1, f x u) + b * (∫ u in (0 : ℝ)..1, f y u) ≤
    (∫ u in (0 : ℝ)..1, f (a*x+b*y) u)
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add ((hI x).const_mul a) ((hI y).const_mul b)]
  apply intervalIntegral.integral_mono_on zero_le_one (((hI x).const_mul a).add ((hI y).const_mul b)) (hI _)
  intro u hu
  have hr := hC.2 (show u*x ∈ Ici 0 from mul_nonneg hu.1 hx)
    (show u*y ∈ Ici 0 from mul_nonneg hu.1 hy) ha hb hab
  simp only [smul_eq_mul] at hr
  rw [show a*(u*x)+b*(u*y)=u*(a*x+b*y) by ring] at hr
  have h := mul_le_mul_of_nonneg_left hr (sub_nonneg.mpr hu.2)
  unfold f
  simpa only [Pi.add_apply] using (show a*((1-u)*positiveEntropyJet 2 (u*x)) +
      b*((1-u)*positiveEntropyJet 2 (u*y)) ≤ _ by linarith only [h])

private theorem normalizedEntropyWord_zero_gt : (7/25 : ℝ) < normalizedEntropyWord 0 := by
  let K := positiveEntropyJet 2 0
  have hD (u : ℝ) : HasDerivAt (fun u => (u-u^2/2)*K) ((1-u)*K) u := by
    convert (((hasDerivAt_id u).sub (((hasDerivAt_id u).pow 2).div_const 2)).mul_const K) using 1
    simp only [id_eq, mul_one, Nat.cast_ofNat, Nat.reduceSub,pow_one]
    ring
  have hI : Continuous fun u : ℝ => (1-u)*K := by fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (fun u _ => hD u) (hI.intervalIntegrable 0 1)
  have hEq : normalizedEntropyWord 0 = K/2 := by
    unfold normalizedEntropyWord
    simp only [mul_zero]
    change (∫ u in (0 : ℝ)..1, (1-u)*K) = K/2
    convert h using 1
    ring
  rw [hEq]
  unfold K positiveEntropyJet
  norm_num
  linarith only [entropyAnchor_bounds.1]

private theorem positiveEntropyWord_chord {t : ℝ} (ht : 0 < t) (hL : t ≤ Real.log 13) :
    t^2 * ((7/25)*(1-t/Real.log 13)+(9/1000)*(t/Real.log 13)) < positiveEntropyWord t := by
  let L := Real.log 13
  have hL₀ : 0 < L := Real.log_pos (by norm_num)
  have hL₁ : (9/1000 : ℝ) < normalizedEntropyWord L := by
    have h := positiveEntropyWord_atLog_pos
    change (4643/70200 : ℝ) < positiveEntropyWord L at h
    rw [← normalizedEntropyWord_identity L] at h
    have hBound := pow_le_pow_left₀ hL₀.le entropySupportLog_upper.le 2
    have h' : L^2*(9/1000) < L^2*normalizedEntropyWord L := by linarith only [h,hBound]
    exact lt_of_mul_lt_mul_left h' (sq_nonneg L)
  have hTL : t/L ≤ 1 := (div_le_one hL₀).mpr hL
  have hT₀ : 0 < t/L := div_pos ht hL₀
  have h := normalizedEntropyWord_concave.2 (mem_Ici.mpr (le_refl (0:ℝ))) (mem_Ici.mpr hL₀.le)
    (sub_nonneg.mpr hTL) hT₀.le (sub_add_cancel 1 (t/L))
  simp only [smul_eq_mul,mul_zero,zero_add,div_mul_cancel₀ _ hL₀.ne'] at h
  have h0 := mul_le_mul_of_nonneg_left normalizedEntropyWord_zero_gt.le (sub_nonneg.mpr hTL)
  have h1 := mul_lt_mul_of_pos_left hL₁ hT₀
  have hCh : (7/25)*(1-t/L)+(9/1000)*(t/L) < normalizedEntropyWord t := by linarith only [h,h0,h1]
  rw [← normalizedEntropyWord_identity t]
  exact mul_lt_mul_of_pos_left hCh (sq_pos_of_pos ht)

private theorem positiveEntropyWord_pos {t : ℝ} (ht : 0 < t) (hL : t ≤ Real.log 13) :
    0 < positiveEntropyWord t := by
  have h := positiveEntropyWord_chord ht hL
  have hLog : 0 < Real.log 13 := Real.log_pos (by norm_num)
  have hRatio := sub_nonneg.mpr ((div_le_one hLog).mpr hL)
  exact (show 0 ≤ t^2*((7/25)*(1-t/Real.log 13)+(9/1000)*(t/Real.log 13)) by positivity).trans_lt h

private theorem entropyWord_mono_tau {tau sigma t : ℝ} (h : tau ≤ sigma) :
    negativeEntropyWord tau t ≤ negativeEntropyWord sigma t := by
  have h₁ := mul_le_mul_of_nonneg_right h (entropyExp_nonneg ((4 / 9) * t))
  unfold negativeEntropyWord
  linarith only [h₁]

private theorem entropyExp_neg_superadd {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    entropyExp (-x) + entropyExp (-y) ≤ entropyExp (-(x + y)) := by
  have h := mul_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)))
    (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hy)))
  unfold entropyExp
  rw [neg_add,Real.exp_add]
  nlinarith only [h]

private theorem entropyEta_le_one {t : ℝ} (h : t ≤ Real.log 13) : entropyEta t ≤ 1 := by
  unfold entropyEta entropyAnchor
  rw [← Real.exp_add]
  exact Real.exp_le_one_iff.mpr (by linarith only [h])

private theorem entropyAnchor_le_eta {t : ℝ} (ht : 0 ≤ t) : entropyAnchor ≤ entropyEta t := by
  unfold entropyEta
  have h := mul_le_mul_of_nonneg_left (Real.one_le_exp_iff.mpr (by positivity : 0 ≤ (25 / 126 : ℝ) * t))
    (Real.exp_pos (-(25 / 126) * Real.log 13)).le
  simpa only [mul_one] using h

private theorem entropyMixed_coupling {x v : ℝ} (hx : 0 ≤ x) (hv : 0 ≤ v) :
    -(1 / 7 : ℝ) * v * (1 - Real.exp (-(1 / 7) * x)) ≤
      entropyExp (-(1 / 7) * (x - v)) - entropyExp (-(1 / 7) * x) := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp ((1 / 7) * v))
    (Real.exp_pos (-(1 / 7) * x)).le
  unfold entropyExp
  rw [show -(1 / 7 : ℝ) * (x - v) = -(1 / 7) * x + (1 / 7) * v by ring,Real.exp_add]
  nlinarith only [h]

private theorem entropyMixed_pos {x v : ℝ} (hx : 0 < x) (hv : 0 < v)
    (hL : x + v ≤ Real.log 13) :
    0 < negativeEntropyWord (entropyEta x) x + negativeEntropyWord (entropyEta x) (-v) +
      (28 / 5) * (28 / 27 + entropyEta x) * entropyExp (-(1 / 7) * (x - v)) := by
  let T := entropyEta x
  let C := (28 / 5 : ℝ) * (28 / 27 + T)
  have hxL : x ≤ Real.log 13 := by linarith only [hL,hv]
  have hvL : v ≤ Real.log 13 := by linarith only [hL,hx]
  have hT : T ≤ 1 := entropyEta_le_one hxL
  have hT₀ : 3 / 5 ≤ T := entropyAnchor_bounds.1.le.trans (entropyAnchor_le_eta hx.le)
  have hC : 0 ≤ C := by unfold C; linarith only [hT₀]
  have hCU : C ≤ (28 / 5) * (28 / 27 + 1) := by unfold C; linarith only [hT]
  have hN := negativeEntropyWord_lower hT₀ hv hvL entropySupportLog_upper
  have hMix := mul_le_mul_of_nonneg_left (entropyMixed_coupling hx.le hv.le) hC
  have hExp : Real.exp (-(1 / 7) * x) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hx.le)
  have hNeg : 0 ≤ 1 - Real.exp (-(1 / 7) * x) := sub_nonneg.mpr hExp
  have hE : 1 - Real.exp (-(1 / 7) * x) ≤ (1 / 7) * x := by
    linarith only [Real.add_one_le_exp (-(1 / 7) * x)]
  have hB := mul_le_mul hCU hE hNeg (by norm_num)
  have hLoss := mul_le_mul_of_nonneg_left hB (show 0 ≤ (1 / 7 : ℝ) * v by positivity)
  have hP := positiveEntropyWord_chord hx hxL
  let L := Real.log 13
  have hL₀ : 0 < L := Real.log_pos (by norm_num)
  have hSum : 0 < x+v := add_pos hx hv
  have hRatio : x/L ≤ x/(x+v) := div_le_div_of_nonneg_left hx.le hSum hL
  let q := v/x
  have hq : 0 ≤ q := div_nonneg hv.le hx.le
  have hPoly : 0 < 279*q^3-421*q^2+140*q+27 := by
    by_cases hq₁ : q ≤ 1
    · have hS := mul_nonneg hq (sq_nonneg (q-421/558))
      nlinarith only [hq₁,hS]
    · let z := q-1
      have hz : 0 ≤ z := sub_nonneg.mpr (le_of_not_ge hq₁)
      have hE : 279*q^3-421*q^2+140*q+27 = 25+135*z+416*z^2+279*z^3 := by unfold z; ring
      rw [hE]
      positivity
  have hHom : 0 < 279*v^3-421*x*v^2+140*x^2*v+27*x^3 := by
    have h := mul_pos (pow_pos hx 3) hPoly
    unfold q at h
    convert h using 1
    field_simp [hx.ne']
  have hChord : x^2*((7/25)*(1-x/(x+v))+(9/1000)*(x/(x+v))) ≤
      x^2*((7/25)*(1-x/L)+(9/1000)*(x/L)) := by
    linarith only [mul_le_mul_of_nonneg_left hRatio (sq_nonneg x)]
  have hPaid : 0 < x^2*((7/25)*(1-x/(x+v))+(9/1000)*(x/(x+v))) +
      (93/1000)*v^2 - (7/30)*x*v := by
    apply pos_of_mul_pos_right (a := (3000:ℝ)*(x+v)) _ (by positivity)
    convert hHom using 1
    field_simp [hSum.ne']
    ring
  unfold positiveEntropyWord at hP
  change x^2*((7/25)*(1-x/L)+(9/1000)*(x/L)) <
    negativeEntropyWord T x + C * entropyExp (-(1 / 7) * x) at hP
  change 0 < negativeEntropyWord T x + negativeEntropyWord T (-v) + C * entropyExp (-(1 / 7) * (x - v))
  nlinarith only [hP,hN,hMix,hLoss,hChord,hPaid,mul_nonneg hx.le hv.le]

private theorem weightedPressureEntropy_base_pos {sigma x y : ℝ}
    (hs : 0 ≤ sigma) (hsL : sigma ≤ Real.log 13)
    (hx : x ∈ Icc (-sigma) (Real.log 13 - sigma)) (hy : y ∈ Icc (-sigma) (Real.log 13 - sigma))
    (h : x ≠ 0 ∨ y ≠ 0) :
    0 < weightedPressureEntropy (28 / 27) (9 / 5) sigma x y := by
  let T := pressureTau (9 / 5) sigma
  let C := (28 / 5 : ℝ) * (28 / 27 + T)
  have hT (t : ℝ) (ht : t ≤ Real.log 13 - sigma) : entropyEta t ≤ T := by
    unfold entropyEta entropyAnchor T pressureTau
    rw [← Real.exp_add]
    norm_num
    linarith only [ht]
  have hTa : entropyAnchor ≤ T := by
    simpa only [entropyEta,mul_zero,Real.exp_zero,mul_one] using hT 0 (sub_nonneg.mpr hsL)
  have hT₀ : 3 / 5 ≤ T := entropyAnchor_bounds.1.le.trans hTa
  have hC : 0 ≤ C := by unfold C; linarith only [hT₀]
  have hE : weightedPressureEntropy (28 / 27) (9 / 5) sigma x y =
      negativeEntropyWord T x + negativeEntropyWord T y +
        C * entropyExp (-(1 / 7) * (x + y)) := by
    unfold weightedPressureEntropy negativeEntropyWord C T pressureC pressureBeta pressureB
    norm_num
    ring_nf
  have hNegative (t : ℝ) (ht : -sigma ≤ t) (ht₀ : t < 0) : 0 < negativeEntropyWord T t := by
    have hB := negativeEntropyWord_lower hT₀ (neg_pos.mpr ht₀)
      (show -t ≤ Real.log 13 by linarith only [ht,hsL]) entropySupportLog_upper
    rw [neg_neg] at hB
    exact (mul_nonneg (by norm_num : (0 : ℝ) ≤ 93 / 1000) (sq_nonneg (-t))).trans_lt hB
  have hPositive (t : ℝ) (ht : 0 < t) (htL : t ≤ Real.log 13 - sigma) :
      0 < negativeEntropyWord T t + C * entropyExp (-(1 / 7) * t) := by
    have hR : positiveEntropyWord t ≤ negativeEntropyWord T t + C * entropyExp (-(1 / 7) * t) := by
      unfold positiveEntropyWord C
      have hU := mul_le_mul_of_nonneg_right (hT t htL) (entropyExp_nonneg (-(1 / 7) * t))
      linarith only [hU,entropyWord_mono_tau (t := t) (hT t htL)]
    exact (positiveEntropyWord_pos ht (htL.trans (sub_le_self _ hs))).trans_le hR
  have hZero : negativeEntropyWord T 0 = 0 := by simp [negativeEntropyWord,entropyExp]
  rw [hE]
  rcases lt_trichotomy x 0 with hX | rfl | hX <;> rcases lt_trichotomy y 0 with hY | rfl | hY
  · exact add_pos_of_pos_of_nonneg (add_pos (hNegative x hx.1 hX) (hNegative y hy.1 hY))
      (mul_nonneg hC (entropyExp_nonneg _))
  · rw [hZero,add_zero,add_zero]
    exact add_pos_of_pos_of_nonneg (hNegative x hx.1 hX) (mul_nonneg hC (entropyExp_nonneg _))
  · have hBase := entropyMixed_pos hY (neg_pos.mpr hX) (by linarith only [hx.1,hy.2])
    rw [neg_neg,sub_neg_eq_add,add_comm y x] at hBase
    have hTx := hT y hy.2
    have hB := add_le_add (entropyWord_mono_tau (t := x) hTx) (entropyWord_mono_tau (t := y) hTx)
    have hC' := mul_le_mul_of_nonneg_right hTx (entropyExp_nonneg (-(1 / 7) * (x + y)))
    unfold C
    linarith only [hBase,hB,hC']
  · rw [hZero,zero_add,zero_add]
    exact add_pos_of_pos_of_nonneg (hNegative y hy.1 hY) (mul_nonneg hC (entropyExp_nonneg _))
  · exact (h.elim (fun h => h rfl) (fun h => h rfl)).elim
  · simpa only [hZero,zero_add] using hPositive y hY hy.2
  · have hBase := entropyMixed_pos hX (neg_pos.mpr hY) (by linarith only [hx.2,hy.1])
    rw [neg_neg,sub_neg_eq_add] at hBase
    have hTx := hT x hx.2
    have hB := add_le_add (entropyWord_mono_tau (t := x) hTx) (entropyWord_mono_tau (t := y) hTx)
    have hC' := mul_le_mul_of_nonneg_right hTx (entropyExp_nonneg (-(1 / 7) * (x + y)))
    unfold C
    linarith only [hBase,hB,hC']
  · simpa only [hZero,add_zero] using hPositive x hX hx.2
  · have hSup := entropyExp_neg_superadd (x := x / 7) (y := y / 7) (by positivity) (by positivity)
    have hSup' : entropyExp (-(1 / 7) * x) + entropyExp (-(1 / 7) * y) ≤ entropyExp (-(1 / 7) * (x + y)) := by
      convert hSup using 2 <;> ring
    have h := mul_le_mul_of_nonneg_left hSup' hC
    nlinarith only [h,hPositive x hX hx.2,hPositive y hY hy.2]

theorem weightedPressureEntropy_nonneg {p sigma x y : ℝ} (hp : 9 / 5 ≤ p)
    (hs : 0 ≤ sigma) (hsL : sigma ≤ Real.log 13)
    (hx : x ∈ Icc (-sigma) (Real.log 13 - sigma)) (hy : y ∈ Icc (-sigma) (Real.log 13 - sigma)) :
    0 ≤ weightedPressureEntropy (28 / 27) p sigma x y := by
  by_cases h : x = 0 ∧ y = 0
  · obtain ⟨rfl,rfl⟩ := h
    simp [weightedPressureEntropy,entropyExp]
  · have hNZ : x ≠ 0 ∨ y ≠ 0 := by
      by_cases hx₀ : x = 0
      · exact Or.inr fun hy₀ => h ⟨hx₀,hy₀⟩
      · exact Or.inl hx₀
    exact (weightedPressureEntropy_base_pos hs hsL hx hy hNZ).le.trans
      (weightedPressureEntropy_mono (by norm_num) hp hs (by norm_num))

theorem weightedPressureEntropy_zero_iff {p sigma x y : ℝ} (hp : 9 / 5 ≤ p)
    (hs : 0 ≤ sigma) (hsL : sigma ≤ Real.log 13)
    (hx : x ∈ Icc (-sigma) (Real.log 13 - sigma)) (hy : y ∈ Icc (-sigma) (Real.log 13 - sigma)) :
    weightedPressureEntropy (28 / 27) p sigma x y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    by_contra h'
    have hNZ : x ≠ 0 ∨ y ≠ 0 := by
      by_cases hx₀ : x = 0
      · exact Or.inr fun hy₀ => h' ⟨hx₀,hy₀⟩
      · exact Or.inl hx₀
    have hPos := (weightedPressureEntropy_base_pos hs hsL hx hy hNZ).trans_le
      (weightedPressureEntropy_mono (by norm_num) hp hs (by norm_num))
    exact hPos.ne' h
  · rintro ⟨rfl,rfl⟩
    simp [weightedPressureEntropy,entropyExp]

end ACS12.Pressure

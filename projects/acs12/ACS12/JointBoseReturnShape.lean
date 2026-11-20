import ACS12.JointFrequencyGuards

/-! Complete Bose guards used by DD15–19 and the joint return. -/
namespace ACS12.GammaMeasure

open CenteredCircle.AllN Polynomial Set
open BoseShape (expQuad expQuad_deriv)

private noncomputable def boseDecayGuardD (n : ℕ) (s : ℝ) : ℝ :=
  expQuad 2 0 (2 ^ n) (2 ^ n * (3 + (n : ℝ) / 2)) s +
    expQuad 1 0 (-2) (-2 * (3 + n)) s +
    expQuad (5 / 3) 0 (-6 * (5 / 3) ^ n) (-6 * (5 / 3) ^ n * (-1 + (3 / 5) * n)) s +
    expQuad (2 / 3) 0 0 (-6 * (2 / 3) ^ n) s

private theorem boseDecayGuard_pos {s : ℝ} (hs : 0 < s) :
    0 < (s + 3) * (Real.exp s - 1) ^ 2 -
      6 * ((s - 1) * Real.exp ((5 / 3) * s) + Real.exp ((2 / 3) * s)) := by
  let P : ℝ[X] := C (-3) + C (-1) * X
  have hD (n : ℕ) (t : ℝ) : HasDerivAt (boseDecayGuardD n) (boseDecayGuardD (n + 1) t) t := by
    unfold boseDecayGuardD
    convert (((expQuad_deriv 2 0 (2 ^ n) (2 ^ n * (3 + (n : ℝ) / 2)) t).add
      (expQuad_deriv 1 0 (-2) (-2 * (3 + n)) t)).add
      (expQuad_deriv (5 / 3) 0 (-6 * (5 / 3) ^ n) (-6 * (5 / 3) ^ n * (-1 + (3 / 5) * n)) t)).add
      (expQuad_deriv (2 / 3) 0 0 (-6 * (2 / 3) ^ n) t) using 1
    simp only [expQuad, pow_succ, Nat.cast_add, Nat.cast_one]
    ring
  have h0 (n : ℕ) (hn : n < 5) : boseDecayGuardD n 0 = (derivative^[n] P).eval 0 := by
    interval_cases n <;> norm_num [boseDecayGuardD, expQuad, P, derivative_add, derivative_C_mul]
  have hN (t : ℝ) (ht : 0 < t) : (derivative^[5] P).eval t < boseDecayGuardD 5 t := by
    have hP : (derivative^[5] P).eval t = 0 := by
      norm_num [P, derivative_add, derivative_C_mul]
    rw [hP]
    let e := Real.exp ((5 / 3) * t)
    have hE : Real.exp (2 * t) = e * Real.exp (t / 3) := by
      dsimp only [e]
      rw [← Real.exp_add]
      congr 1
      ring
    have h₁ : (1 + t / 3) * e ≤ Real.exp (2 * t) := by
      rw [hE, mul_comm e]
      exact mul_le_mul_of_nonneg_right (by simpa only [add_comm] using Real.add_one_le_exp (t / 3)) (Real.exp_pos _).le
    have h₂ : Real.exp t ≤ e := Real.exp_le_exp.mpr (by linarith only [ht])
    have h₃ : Real.exp ((2 / 3) * t) ≤ e := Real.exp_le_exp.mpr (by linarith only [ht])
    have h₄ := mul_le_mul_of_nonneg_left h₁ (show 0 ≤ 32 * t + 176 by positivity)
    have h₅ := mul_le_mul_of_nonneg_left h₂ (show 0 ≤ 2 * t + 16 by positivity)
    have h₆ := mul_le_mul_of_nonneg_left h₃ (by norm_num : (0 : ℝ) ≤ 64 / 81)
    have he : 0 < e := Real.exp_pos _
    have hPos := mul_pos he (show 0 < (32 * t + 176) * (1 + t / 3) -
      (2 * t + 16) - (6250 / 81) * (t + 2) - 64 / 81 by nlinarith only [ht, sq_nonneg t])
    norm_num [boseDecayGuardD, expQuad, one_mul]
    change (64 / 81) * Real.exp ((2 / 3) * t) < (32 * t + 176) * Real.exp (2 * t) +
      (-(2 * t) + -16) * Real.exp t + (-(6250 / 81 * t) + -(12500 / 81)) * e
    nlinarith only [h₄, h₅, h₆, hPos]
  have h := expGuard_remainder h0 hD hN hs
  norm_num [P, boseDecayGuardD, expQuad] at h
  rw [two_mul, Real.exp_add] at h
  linear_combination h

theorem boseC_le_decaySharp {s : ℝ} (hs : 0 < s) :
    BoseShape.C s < (1 / 2 + s / 6) * Real.exp (-(2 / 3) * s) := by
  have hE : Real.exp (-(2 / 3) * s) * Real.exp ((2 / 3) * s) = 1 := by
    rw [← Real.exp_add, show -(2 / 3 : ℝ) * s + (2 / 3) * s = 0 by ring, Real.exp_zero]
  have hE' : Real.exp s * Real.exp ((2 / 3) * s) = Real.exp ((5 / 3) * s) := by
    rw [← Real.exp_add, show s + (2 / 3 : ℝ) * s = (5 / 3) * s by ring]
  have hEq : ((1 / 2 + s / 6) * Real.exp (-(2 / 3) * s) - BoseShape.C s) *
      (6 * (Real.exp s - 1) ^ 2 * Real.exp ((2 / 3) * s)) =
        (s + 3) * (Real.exp s - 1) ^ 2 -
          6 * ((s - 1) * Real.exp ((5 / 3) * s) + Real.exp ((2 / 3) * s)) := by
    have hC : BoseShape.C s * (Real.exp s - 1) ^ 2 = (s - 1) * Real.exp s + 1 := by
      unfold BoseShape.C
      exact div_mul_cancel₀ _ (pow_ne_zero _ (expTail_den_pos hs).ne')
    linear_combination (s + 3) * (Real.exp s - 1) ^ 2 * hE -
      6 * Real.exp ((2 / 3) * s) * hC - 6 * (s - 1) * hE'
  exact sub_pos.mp (pos_of_mul_pos_left (hEq.symm ▸ boseDecayGuard_pos hs) (by positivity))

private theorem boseDecay_weight_lt {s : ℝ} (hs : 0 < s) :
    s * (1 / 2 + s / 6) * Real.exp (-(13 / 24) * s) < 3 / 5 := by
  let t := (9 + 15 * Real.sqrt 17) / 26
  let f (x : ℝ) := x * (1 / 2 + x / 6) * Real.exp (-(13 / 24) * x)
  let D (x : ℝ) := Real.exp (-(13 / 24) * x) * (72 + 9 * x - 13 * x ^ 2) / 144
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 17)
  have hsqrtL : (103 / 25 : ℝ) < Real.sqrt 17 := by
    nlinarith only [hsqrt, Real.sqrt_nonneg 17, sq_nonneg (Real.sqrt 17 - 103 / 25)]
  have hsqrtU : Real.sqrt 17 < 33 / 8 := by
    nlinarith only [hsqrt, Real.sqrt_nonneg 17, sq_nonneg (Real.sqrt 17 - 33 / 8)]
  have ht : 0 < t := by dsimp only [t]; linarith only [hsqrtL]
  have htE : 72 + 9 * t - 13 * t ^ 2 = 0 := by dsimp only [t]; nlinarith only [hsqrt]
  have htL : (59 / 40 : ℝ) < (13 / 24) * t := by dsimp only [t]; linarith only [hsqrtL]
  have htU : t * (1 / 2 + t / 6) < 879 / 338 := by
    have h := hsqrtU
    change Real.sqrt 17 < (33 / 8 : ℝ) at h
    have hU : t < (9 + 15 * (33 / 8 : ℝ)) / 26 := by dsimp only [t]; linarith only [h]
    nlinarith only [htE,hU]
  have hd (x : ℝ) : HasDerivAt f (D x) x := by
    have h := hasDerivAt_id x
    convert (h.mul ((h.div_const 6).const_add (1/2))).mul ((h.const_mul (-(13/24))).exp) using 1
    simp only [D, Pi.mul_apply, id_eq, mul_one, one_mul]
    ring
  have hP (x : ℝ) : 72 + 9 * x - 13 * x ^ 2 = (t - x) * (13 * (t + x) - 9) := by
    nlinarith only [htE]
  have hT₀ : 9 ≤ 13 * t := by linarith only [htL]
  have hMono : MonotoneOn f (Icc 0 t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun x _ => (hd x).continuousAt.continuousWithinAt
    · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Icc (0 : ℝ) t := interior_subset hx
      rw [(hd x).deriv]
      dsimp only [D]
      rw [hP x]
      exact div_nonneg (mul_nonneg (Real.exp_pos _).le (mul_nonneg (sub_nonneg.mpr hx'.2)
        (by linarith only [hx'.1, hT₀]))) (by norm_num)
  have hAnti : AntitoneOn f (Ici t) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · exact fun x _ => (hd x).continuousAt.continuousWithinAt
    · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : t ≤ x := show x ∈ Ici t from interior_subset hx
      rw [(hd x).deriv]
      dsimp only [D]
      rw [hP x]
      exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx') (by linarith only [ht, hx', hT₀]))) (by norm_num)
  have hMax : f s ≤ f t := by
    rcases le_total s t with h | h
    · exact hMono ⟨hs.le,h⟩ ⟨ht.le,le_rfl⟩ h
    · exact hAnti (show t ∈ Ici t from mem_Ici.mpr le_rfl) (show s ∈ Ici t from mem_Ici.mpr h) h
  have hE : Real.exp (-(13 / 24) * t) ≤ Real.exp (-(59 / 40)) := Real.exp_le_exp.mpr (by linarith only [htL])
  have hExp : (1465 / 338 : ℝ) < Real.exp (59 / 40) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 59 / 40) 6
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith only [h]
  have hInv : (879 / 338 : ℝ) * Real.exp (-(59 / 40)) < 3 / 5 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ (Real.exp_pos _)]
    linarith only [hExp]
  exact hMax.trans_lt ((mul_le_mul htU.le hE (Real.exp_pos _).le (by norm_num)).trans_lt hInv)

theorem boseC_exp_weight_lt {s : ℝ} (hs : 0 < s) :
    s * Real.exp (s / 8) * BoseShape.C s < 3 / 5 := by
  have h := mul_lt_mul_of_pos_left (boseC_le_decaySharp hs) (mul_pos hs (Real.exp_pos (s / 8)))
  have hEq : s * Real.exp (s / 8) * ((1 / 2 + s / 6) * Real.exp (-(2 / 3) * s)) =
      s * (1 / 2 + s / 6) * Real.exp (-(13 / 24) * s) := by
    have hE : Real.exp (s / 8) * Real.exp (-(2 / 3) * s) = Real.exp (-(13 / 24) * s) := by
      rw [← Real.exp_add]
      congr 1
      ring
    linear_combination s * (1 / 2 + s / 6) * hE
  exact h.trans (hEq.symm ▸ boseDecay_weight_lt hs)

private noncomputable def fourthGuardD (n : ℕ) (s : ℝ) : ℝ :=
  expQuad 3 0 0 (3 ^ n) s +
    expQuad 2 (-3 * 2 ^ n) (-3 * 2 ^ n * (n - 2))
      (-3 * 2 ^ n * (2 - n + (n : ℝ) * (n - 1) / 4)) s +
    expQuad 1 0 (-6) (9 - 6 * n) s

private noncomputable def fourthGuardP : ℝ[X] :=
  ∑ j ∈ Finset.range 8, C
    (match j with
      | 0 => 4
      | 1 => 0
      | 2 => 0
      | 3 => 1
      | 4 => 3 / 4
      | 5 => 1 / 4
      | 6 => 1 / 24
      | _ => 1 / 120 : ℝ) * X ^ j

private theorem fourthGuard_pos {s : ℝ} (hs : 0 < s) :
    0 < (Real.exp s - 1) ^ 3 - 3 * ((s - 1) * Real.exp s + 1) ^ 2 := by
  have hD (n : ℕ) (t : ℝ) : HasDerivAt (fourthGuardD n) (fourthGuardD (n + 1) t) t := by
    unfold fourthGuardD
    convert ((expQuad_deriv 3 0 0 (3 ^ n) t).add
      (expQuad_deriv 2 (-3 * 2 ^ n) (-3 * 2 ^ n * (n - 2))
        (-3 * 2 ^ n * (2 - n + (n : ℝ) * (n - 1) / 4)) t)).add
      (expQuad_deriv 1 0 (-6) (9 - 6 * n) t) using 1
    simp only [expQuad, pow_succ, Nat.cast_add, Nat.cast_one]
    ring
  have h0 (n : ℕ) (hn : n < 8) : fourthGuardD n 0 = (derivative^[n] fourthGuardP).eval 0 := by
    interval_cases n <;> norm_num [fourthGuardD, expQuad, fourthGuardP, Finset.sum_range_succ, iterate_derivative_sum, iterate_derivative_X_pow_eq_C_mul,
      Nat.descFactorial_succ, Nat.descFactorial_zero]
  have hN (t : ℝ) (ht : 0 < t) : (derivative^[8] fourthGuardP).eval t < fourthGuardD 8 t := by
    have hP : (derivative^[8] fourthGuardP).eval t = 0 := by
      norm_num [fourthGuardP, Finset.sum_range_succ, iterate_derivative_sum, iterate_derivative_X_pow_eq_C_mul,
        Nat.descFactorial_succ, Nat.descFactorial_zero]
    rw [hP]
    have hE : Real.exp (3 * t) = Real.exp (2 * t) * Real.exp t := by
      rw [← Real.exp_add, show 2 * t + t = 3 * t by ring]
    have hE₁ : Real.exp t ≤ Real.exp (2 * t) := Real.exp_le_exp.mpr (by linarith only [ht])
    have h₁ := mul_le_mul_of_nonneg_left hE₁ (show 0 ≤ 6 * t + 39 by positivity)
    have h₂ := mul_le_mul_of_nonneg_left (Real.quadratic_le_exp_of_nonneg ht.le)
      (show 0 ≤ 6561 * Real.exp (2 * t) by positivity)
    have hPos := mul_pos (Real.exp_pos (2 * t)) (show 0 < 6561 * (1 + t + t ^ 2 / 2) -
      768 * (t ^ 2 + 6 * t + 8) - (6 * t + 39) by nlinarith only [ht, sq_nonneg t])
    norm_num [fourthGuardD, expQuad, one_mul, hE]
    nlinarith only [h₁,h₂,hPos]
  have h := expGuard_remainder h0 hD hN hs
  norm_num [fourthGuardD, expQuad, fourthGuardP, Finset.sum_range_succ] at h
  have h2 : Real.exp (2 * s) = Real.exp s ^ 2 := by rw [two_mul, Real.exp_add, sq]
  have h3 : Real.exp (3 * s) = Real.exp s ^ 3 := by
    rw [show 3 * s = 2 * s + s by ring, Real.exp_add, h2]
    ring
  rw [h2,h3] at h
  have hP : 0 < s ^ 3 + (3 / 4) * s ^ 4 + (1 / 4) * s ^ 5 + (1 / 24) * s ^ 6 + (1 / 120) * s ^ 7 :=
    by positivity
  linear_combination h + hP

theorem polyBC_lt_third {s : ℝ} (hs : 0 < s) :
    polyB s * BoseShape.C s < (1 - Real.exp (-s)) / 3 := by
  have hEq : ((1 - Real.exp (-s)) / 3 - polyB s * BoseShape.C s) *
      (3 * Real.exp s * (Real.exp s - 1) ^ 2) =
      (Real.exp s - 1) ^ 3 - 3 * ((s - 1) * Real.exp s + 1) ^ 2 := by
    unfold polyB BoseShape.C
    rw [Real.exp_neg]
    field_simp [(expTail_den_pos hs).ne', Real.exp_ne_zero s]
  exact sub_pos.mp (pos_of_mul_pos_left (hEq.symm ▸ fourthGuard_pos hs) (by positivity))

end ACS12.GammaMeasure

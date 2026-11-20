import ACS12.PeanoExponentPrices

/-! One-peak shape and exact height bounds for the adverse Peano curvature. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN Set
open scoped BigOperators

noncomputable def peanoExponentQuadratic (p y : ℝ) : ℝ :=
  2 * (2 * p + 1) * y - p * (p + 1) * y ^ 2 - 2

noncomputable def peanoExponentBad (p x : ℝ) : ℝ :=
  x ^ (-(p + 2)) * max 0 (peanoExponentQuadratic p (Real.log x))

theorem peanoExponentBad_nonneg {p x : ℝ} (hx : 0 < x) :
    0 ≤ peanoExponentBad p x := mul_nonneg (Real.rpow_nonneg hx.le _) (le_max_left _ _)

theorem peanoExponentBad_continuousOn (p : ℝ) : ContinuousOn (peanoExponentBad p) (Ioi 0) := by
  have hlog : ContinuousOn Real.log (Ioi 0) :=
    fun x hx => (Real.continuousAt_log (mem_Ioi.mp hx).ne').continuousWithinAt
  have hq : Continuous (peanoExponentQuadratic p) := by unfold peanoExponentQuadratic; fun_prop
  have hC := hq.comp_continuousOn hlog
  exact (continuousOn_id.rpow_const (fun x hx => Or.inl (mem_Ioi.mp hx).ne')).mul
    (continuousOn_const.sup hC)

private theorem peanoQuadratic_concave {p : ℝ} (hp : 0 ≤ p) :
    ConcaveOn ℝ univ (peanoExponentQuadratic p) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  have hE : peanoExponentQuadratic p (a * x + b * y) -
      (a * peanoExponentQuadratic p x + b * peanoExponentQuadratic p y) =
      p * (p + 1) * (a * b) * (x - y) ^ 2 := by
    unfold peanoExponentQuadratic
    linear_combination (2 - p * (p + 1) * (a * x ^ 2 + b * y ^ 2)) * hab
  exact sub_nonneg.mp (hE ▸ (by positivity : 0 ≤ p * (p + 1) * (a * b) * (x - y) ^ 2))

theorem peanoExponentBad_min {p a b c : ℝ} (hp : 0 ≤ p) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) :
    min (peanoExponentBad p a) (peanoExponentBad p c) ≤ peanoExponentBad p b := by
  have hb := ha.trans_le hab
  have hc := hb.trans_le hbc
  by_cases h₁ : 0 < peanoExponentQuadratic p (Real.log a)
  · by_cases h₂ : 0 < peanoExponentQuadratic p (Real.log c)
    · let S := {y : ℝ | 0 < peanoExponentQuadratic p y}
      let Q := peanoExponentQuadratic p
      have hQ := peanoQuadratic_concave hp
      have hS : Convex ℝ S := by
        intro x hx y hy α β hα hβ hαβ
        have hP : 0 < α * Q x + β * Q y := by
          have hx' : 0 < Q x := hx
          have hy' : 0 < Q y := hy
          have hMin := add_le_add (mul_le_mul_of_nonneg_left (min_le_left (Q x) (Q y)) hα)
            (mul_le_mul_of_nonneg_left (min_le_right (Q x) (Q y)) hβ)
          have hM : α * min (Q x) (Q y) + β * min (Q x) (Q y) = min (Q x) (Q y) := by
            linear_combination min (Q x) (Q y) * hαβ
          rw [hM] at hMin
          exact (lt_min hx' hy').trans_le hMin
        exact hP.trans_le (hQ.2 (mem_univ _) (mem_univ _) hα hβ hαβ)
      have hQ' : ConcaveOn ℝ S Q := hQ.subset (subset_univ _) hS
      have hyA := Real.log_le_log ha hab
      have hyC := Real.log_le_log hb hbc
      by_cases hAC : Real.log a = Real.log c
      · have hAB : a = b := by
          by_contra! h
          exact (Real.log_lt_log ha (lt_of_le_of_ne hab h)).not_ge (hyC.trans_eq hAC.symm)
        rw [← hAB]
        exact min_le_left _ _
      · let α := (Real.log c - Real.log b) / (Real.log c - Real.log a)
        let β := (Real.log b - Real.log a) / (Real.log c - Real.log a)
        have hΔ : 0 < Real.log c - Real.log a :=
          sub_pos.mpr (lt_of_le_of_ne (hyA.trans hyC) hAC)
        have hα : 0 ≤ α := div_nonneg (sub_nonneg.mpr hyC) hΔ.le
        have hβ : 0 ≤ β := div_nonneg (sub_nonneg.mpr hyA) hΔ.le
        have hαβ : α + β = 1 := by dsimp only [α, β]; field_simp [hΔ.ne']; ring
        have hMid : α * Real.log a + β * Real.log c = Real.log b := by
          dsimp only [α, β]
          field_simp [hΔ.ne']
          ring
        have hqb : 0 < Q (Real.log b) := by
          have h := hS (show Real.log a ∈ S from h₁) (show Real.log c ∈ S from h₂) hα hβ hαβ
          change 0 < Q (α * Real.log a + β * Real.log c) at h
          rwa [hMid] at h
        have hCmb := hQ'.2 (show Real.log a ∈ S from h₁) (show Real.log c ∈ S from h₂) hα hβ hαβ
        simp only [smul_eq_mul, hMid] at hCmb
        have hP : 0 < α * Q (Real.log a) + β * Q (Real.log c) := by
          have hM := add_le_add (mul_le_mul_of_nonneg_left (min_le_left (Q (Real.log a)) (Q (Real.log c))) hα)
            (mul_le_mul_of_nonneg_left (min_le_right (Q (Real.log a)) (Q (Real.log c))) hβ)
          have hPos := lt_min h₁ h₂
          nlinarith only [hM, hPos, congrArg (fun t => min (Q (Real.log a)) (Q (Real.log c)) * t) hαβ]
        have hL := strictConcaveOn_log_Ioi.concaveOn.2 h₁ h₂ hα hβ hαβ
        simp only [smul_eq_mul] at hL
        have hJ := hL.trans (Real.log_le_log hP hCmb)
        have hEq (x : ℝ) (hx : 0 < x) (hxQ : 0 < Q (Real.log x)) :
            peanoExponentBad p x =
              Real.exp (-(p + 2) * Real.log x + Real.log (Q (Real.log x))) := by
          rw [peanoExponentBad, max_eq_right hxQ.le, Real.rpow_def_of_pos hx,
            Real.exp_add, Real.exp_log hxQ, mul_comm (Real.log x)]
        rw [hEq a ha h₁, hEq b hb hqb, hEq c hc h₂]
        let A := -(p + 2) * Real.log a + Real.log (Q (Real.log a))
        let B := -(p + 2) * Real.log b + Real.log (Q (Real.log b))
        let C := -(p + 2) * Real.log c + Real.log (Q (Real.log c))
        have hE : α * A + β * C ≤ B := by
          dsimp only [A, B, C]
          nlinarith only [hJ, congrArg (fun z => -(p + 2) * z) hMid]
        have hMin := add_le_add (mul_le_mul_of_nonneg_left (min_le_left A C) hα)
          (mul_le_mul_of_nonneg_left (min_le_right A C) hβ)
        have hMin' : min A C ≤ B := by
          nlinarith only [hE, hMin, congrArg (fun z => min A C * z) hαβ]
        rcases le_total A C with h | h
        · have h' := Real.exp_le_exp.mpr (min_eq_left h ▸ hMin')
          exact (min_le_left _ _).trans h'
        · have h' := Real.exp_le_exp.mpr (min_eq_right h ▸ hMin')
          exact (min_le_right _ _).trans h'
    · have hZero : peanoExponentBad p c = 0 := by
        rw [peanoExponentBad, max_eq_left (le_of_not_gt h₂), mul_zero]
      exact (min_le_right _ _).trans (hZero.symm ▸ peanoExponentBad_nonneg hb)
  · have hZero : peanoExponentBad p a = 0 := by
      rw [peanoExponentBad, max_eq_left (le_of_not_gt h₁), mul_zero]
    exact (min_le_left _ _).trans (hZero.symm ▸ peanoExponentBad_nonneg hb)

private theorem exp_log_linear_price {x A k c : ℝ} (hx : 0 < x) (hA : 0 < A) (hk : 0 < k) :
    x ^ (-k) * max 0 (A * Real.log x - c) ≤ (A / k) * Real.exp (-(1 + k * c / A)) := by
  by_cases h : A * Real.log x - c ≤ 0
  · rw [max_eq_left h, mul_zero]
    positivity
  · let w := k * (Real.log x - c / A)
    have hW := mul_exp_neg_le_inv_e w
    have hE : x ^ (-k) * (A * Real.log x - c) =
        ((A / k) * Real.exp (-(k * c / A))) * (w * Real.exp (-w)) := by
      rw [Real.rpow_def_of_pos hx]
      have hExp : Real.exp (-(k * c / A)) * Real.exp (-w) = Real.exp (Real.log x * -k) := by
        rw [← Real.exp_add]
        congr 1
        dsimp only [w]
        ring
      have hArg : (A / k) * w = A * Real.log x - c := by
        dsimp only [w]
        field_simp [hA.ne', hk.ne']
      linear_combination (Real.exp (-(k * c / A)) * Real.exp (-w)) * (-hArg) +
        (A * Real.log x - c) * (-hExp)
    rw [max_eq_right (le_of_not_ge h), hE]
    refine (mul_le_mul_of_nonneg_left hW (by positivity)).trans_eq ?_
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring

private theorem peanoQuadratic_le_log_linear {p x : ℝ} (hp : 1 ≤ p) (hx : 0 < x) :
    max 0 (peanoExponentQuadratic p (Real.log x)) ≤
      max 0 (2 * (2 * p + 1) * Real.log x - 20 / 9) := by
  by_cases h : 0 ≤ peanoExponentQuadratic p (Real.log x)
  · rw [max_eq_right h]
    apply le_max_of_le_right
    let y := Real.log x
    have hp₀ := zero_lt_one.trans_le hp
    have hS : 0 ≤ p * (p + 1) * y ^ 2 := by positivity
    have hY : 1 ≤ (2 * p + 1) * y := by unfold peanoExponentQuadratic at h; linarith only [h, hS]
    have hY' : 1 / (2 * p + 1) ≤ y := (div_le_iff₀ (by positivity)).mpr (by linarith only [hY])
    have hYY := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / (2 * p + 1)) hY' 2
    have hB : 2 / 9 ≤ p * (p + 1) * y ^ 2 := by
      have hM := mul_le_mul_of_nonneg_left hYY (by positivity : 0 ≤ p * (p + 1))
      refine le_trans ?_ hM
      rw [div_pow, one_pow, ← mul_div_assoc]
      apply (le_div_iff₀ (by positivity : 0 < (2 * p + 1) ^ 2)).mpr
      nlinarith only [hp, mul_nonneg (sub_nonneg.mpr hp) hp₀.le]
    unfold peanoExponentQuadratic
    dsimp only [y] at hB
    linarith only [hB]
  · rw [max_eq_left (le_of_not_ge h)]
    exact le_max_left _ _

theorem peanoExponentBad_le {p x : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) (hx : 0 < x) :
    peanoExponentBad p x ≤ 9 / 25 := by
  let A := 2 * (2 * p + 1)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hK : 0 < p + 2 := by positivity
  have h := (mul_le_mul_of_nonneg_left (peanoQuadratic_le_log_linear hp hx)
    (Real.rpow_nonneg hx.le (-(p + 2)))).trans (exp_log_linear_price (c := 20 / 9) hx hA hK)
  have hR : A / (p + 2) ≤ 46 / 19 := (div_le_iff₀ hK).mpr (by dsimp only [A]; linarith)
  have hS : 19 / 46 ≤ (p + 2) / A := (le_div_iff₀ hA).mpr (by dsimp only [A]; linarith)
  have hE : Real.exp (-(1 + (p + 2) * (20 / 9) / A)) ≤ Real.exp (-(397 / 207)) :=
    Real.exp_le_exp.mpr (by rw [show (p + 2) * (20 / 9) / A = (20 / 9) * ((p + 2) / A) by ring]; linarith only [hS])
  have hE' : Real.exp (-(397 / 207)) < 4 / 27 := by
    have hSum := Real.sum_le_exp_of_nonneg (x := 397 / 207) (by norm_num) 7
    have hP' : (27 / 4 : ℝ) < Real.exp (397 / 207) := by norm_num [Finset.sum_range_succ] at hSum; linarith
    rw [Real.exp_neg, ← one_div]
    exact (div_lt_div_of_pos_left zero_lt_one (by norm_num) hP').trans_eq (by norm_num)
  refine h.trans (le_trans (mul_le_mul hR (hE.trans hE'.le) (Real.exp_pos _).le (by norm_num)) ?_)
  norm_num

theorem mul_peanoExponentBad_le {p x : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) (hx : 0 < x) :
    x * peanoExponentBad p x ≤ 31 / 50 := by
  let A := 2 * (2 * p + 1)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hK : 0 < p + 1 := by positivity
  have hEq : x * x ^ (-(p + 2)) = x ^ (-(p + 1)) := by
    rw [mul_comm, show -(p + 2) = -(p + 1) - 1 by ring, Real.rpow_sub_one hx.ne',
      div_mul_cancel₀ _ hx.ne']
  rw [peanoExponentBad, ← mul_assoc, hEq]
  have h := (mul_le_mul_of_nonneg_left (peanoQuadratic_le_log_linear hp hx)
    (Real.rpow_nonneg hx.le (-(p + 1)))).trans (exp_log_linear_price (c := 20 / 9) hx hA hK)
  have hR : A / (p + 1) ≤ 23 / 7 := (div_le_iff₀ hK).mpr (by dsimp only [A]; linarith)
  have hS : 7 / 23 ≤ (p + 1) / A := (le_div_iff₀ hA).mpr (by dsimp only [A]; linarith)
  have hE : Real.exp (-(1 + (p + 1) * (20 / 9) / A)) ≤ Real.exp (-(347 / 207)) :=
    Real.exp_le_exp.mpr (by rw [show (p + 1) * (20 / 9) / A = (20 / 9) * ((p + 1) / A) by ring]; linarith only [hS])
  have hE' : Real.exp (-(347 / 207)) < 10 / 53 := by
    have hSum := Real.sum_le_exp_of_nonneg (x := 347 / 207) (by norm_num) 6
    have hP' : (53 / 10 : ℝ) < Real.exp (347 / 207) := by norm_num [Finset.sum_range_succ] at hSum; linarith
    rw [Real.exp_neg, ← one_div]
    exact (div_lt_div_of_pos_left zero_lt_one (by norm_num) hP').trans_eq (by norm_num)
  refine h.trans (le_trans (mul_le_mul hR (hE.trans hE'.le) (Real.exp_pos _).le (by norm_num)) ?_)
  norm_num

end ACS12.GammaMeasure

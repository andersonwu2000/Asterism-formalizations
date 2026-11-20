import ACS12.JointFarSourceJet
import ACS12.NativeLiteralRows

/-! The W42 signed third-moment cost over the whole exponent band. -/
namespace ACS12.GammaMeasure

private theorem farLog_sq_le {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ^ 2 ≤ (9 / 16) * x := by
  let u := Real.log x
  have hu : 0 ≤ u := Real.log_nonneg hx
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (u / 2 - 1)) (Real.exp_pos 1).le
  rw [← Real.exp_add,show 1 + (u / 2 - 1) = u / 2 by ring,
    show u / 2 - 1 + 1 = u / 2 by ring] at h
  have he : (8 / 3 : ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
  have hU := (mul_le_mul_of_nonneg_right he (show 0 ≤ u / 2 by positivity)).trans h
  have hU' : u ≤ (3 / 4) * Real.exp (u / 2) := by linarith only [hU]
  have hSq := pow_le_pow_left₀ hu hU' 2
  rw [mul_pow,pow_two (Real.exp _),← Real.exp_add,show u / 2 + u / 2 = u by ring,
    show Real.exp u = x by exact Real.exp_log (zero_lt_one.trans_le hx)] at hSq
  convert hSq using 1 <;> ring

private theorem farTail4_lt : powerTail 4 2 < (824 / 10000 : ℝ) := by
  change powerTail 4 (1 + 1) < _
  rw [powerTail_shift (by norm_num : (1 : ℝ) < 4),
    NativeCells.powerTail_four_eq]
  simp only [Nat.cast_one,Real.one_rpow]
  have h := pow_lt_pow_left₀ Real.pi_lt_d6 Real.pi_pos.le (by decide : 4 ≠ 0)
  linarith only [h]

private theorem farTail3_lt : powerTail 3 2 < (2021 / 10000 : ℝ) := by
  change powerTail 3 (1 + 1) < _
  rw [powerTail_shift (by norm_num : (1 : ℝ) < 3)]
  simp only [Nat.cast_one,Real.one_rpow]
  linarith only [powerTail_three_bounds.2]

theorem farM2Jet_zero_nonneg {p : ℝ} (hp : 1 ≤ p) : 0 ≤ farM2Jet 0 p := by
  have hq : 1 < p + 2 := by linarith only [hp]
  have h := powerTail_shift hq 1
  norm_num only [Nat.reduceAdd,Nat.cast_one,Real.one_rpow] at h
  unfold farM2Jet pureQ
  change 0 ≤ p * (p + 1) * powerTail (p + 2) 1 - p * (p + 1)
  rw [← mul_sub_one,h.symm]
  exact mul_nonneg (by positivity) (powerTail_pos hq (by decide : 0 < 2)).le

theorem farM3Jet_bounds {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    farM3Jet 0 p ≤ 8 / 5 ∧ farM3Jet 1 p ≤ 19 / 10 ∧ farM3Jet 2 p ≤ 11 / 5 := by
  let T := p * (p + 1) * (p + 2)
  let D := 3 * p ^ 2 + 6 * p + 2
  let A := 6 * p + 6
  let L (j : ℕ) := powerLogTail (p + 3) j 2
  let x (i : ℕ) := (2 : ℝ) + i
  let f (j i : ℕ) := x i ^ (-(p + 3)) * Real.log (x i) ^ j
  have hq : 1 < p + 3 := by linarith only [hp]
  have hS (j : ℕ) : HasSum (f j) (L j) := (powerLogTail_summable hq j 2 (by decide)).hasSum
  have hx (i : ℕ) : 2 ≤ x i := by unfold x; exact le_add_of_nonneg_right (Nat.cast_nonneg i)
  have hLog (i : ℕ) : (69 / 100 : ℝ) ≤ Real.log (x i) := by
    exact (by linarith only [Real.log_two_gt_d9] : (69 / 100 : ℝ) ≤ Real.log 2).trans
      (Real.log_le_log (by norm_num) (hx i))
  have hT : 0 ≤ T := by unfold T; positivity
  have hTU : T ≤ 19152 / 1000 := by
    have hA : p * (p + 1) ≤ (9 / 5) * (14 / 5) :=
      mul_le_mul hP (by linarith only [hP] : p + 1 ≤ 14 / 5) (by positivity) (by norm_num)
    exact (mul_le_mul hA (by linarith only [hP] : p + 2 ≤ 19 / 5) (by positivity) (by norm_num)).trans (by norm_num)
  have hD : 0 ≤ D := by unfold D; positivity
  have hDU : D ≤ 2252 / 100 := by
    unfold D
    have hSq := pow_le_pow_left₀ (zero_le_one.trans hp) hP 2
    linarith only [hP,hSq]
  have hL₀ : 0 ≤ L 0 := (hS 0).tsum_eq ▸ tsum_nonneg (fun i => by
    unfold f
    exact mul_nonneg (Real.rpow_nonneg (by linarith only [hx i]) _) (pow_nonneg (by linarith only [hLog i]) _))
  have hL₁ : 0 ≤ L 1 := (hS 1).tsum_eq ▸ tsum_nonneg (fun i => by
    unfold f
    exact mul_nonneg (Real.rpow_nonneg (by linarith only [hx i]) _) (pow_nonneg (by linarith only [hLog i]) _))
  have hL₀U : L 0 ≤ 824 / 10000 := by
    have h := (hS 0).summable.tsum_le_tsum (g := fun i => x i ^ (-(4 : ℝ)))
      (fun i => by
        simp only [f,pow_zero,mul_one]
        exact Real.rpow_le_rpow_of_exponent_le ((by norm_num : (1 : ℝ) ≤ 2).trans (hx i)) (by linarith only [hp]))
      (powerTail_summable (by norm_num : (1 : ℝ) < 4) 2)
    rw [(hS 0).tsum_eq] at h
    exact h.trans farTail4_lt.le
  have hL₂U : L 2 ≤ (9 / 16) * (2021 / 10000) := by
    have hg : HasSum (fun i => (9 / 16) * x i ^ (-(3 : ℝ))) ((9 / 16) * powerTail 3 2) :=
      (powerTail_summable (by norm_num : (1 : ℝ) < 3) 2).hasSum.mul_left (9 / 16 : ℝ)
    have h := (hS 2).summable.tsum_le_tsum (g := fun i => (9 / 16) * x i ^ (-(3 : ℝ))) (fun i => by
      have hX₁ := (by norm_num : (1 : ℝ) ≤ 2).trans (hx i)
      have hX := zero_lt_one.trans_le hX₁
      have ha := Real.rpow_le_rpow_of_exponent_le hX₁ (show -(p + 3) ≤ -(4 : ℝ) by linarith only [hp])
      have hb := farLog_sq_le hX₁
      calc
        f 2 i ≤ x i ^ (-(4 : ℝ)) * ((9 / 16) * x i) :=
          mul_le_mul ha hb (sq_nonneg _) (Real.rpow_nonneg hX.le _)
        _ = _ := by
          change _ = (9 / 16) * x i ^ (-(3 : ℝ))
          rw [show x i ^ (-(3 : ℝ)) = x i ^ (-(4 : ℝ)) * x i by
            rw [← Real.rpow_add_one hX.ne']; norm_num]
          ring) hg.summable
    rw [(hS 2).tsum_eq,hg.tsum_eq] at h
    exact h.trans (mul_le_mul_of_nonneg_left farTail3_lt.le (by norm_num))
  have hAD : A * L 0 ≤ 2 * D * L 1 := by
    have ha := (hS 0).mul_left A
    have hb := (hS 1).mul_left (2 * D)
    have h := ha.summable.tsum_le_tsum (fun i => by
      have hA : A ≤ 2 * D * (69 / 100) := by
        have hZ := sq_nonneg (p - 1)
        unfold A D
        nlinarith only [hp,hZ]
      have hB := hA.trans (mul_le_mul_of_nonneg_left (hLog i) (by positivity : 0 ≤ 2 * D))
      have hXi : 0 ≤ x i := (by norm_num : (0 : ℝ) ≤ 2).trans (hx i)
      have hC := mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg hXi (-(p + 3)))
      simp only [f,pow_zero,mul_one,pow_one]
      nlinarith only [hC]) hb.summable
    rwa [ha.tsum_eq,hb.tsum_eq] at h
  have h₀ := mul_le_mul hTU hL₀U hL₀ (by norm_num : (0 : ℝ) ≤ 19152 / 1000)
  have h₁ := mul_le_mul hDU hL₀U hL₀ (by norm_num : (0 : ℝ) ≤ 2252 / 100)
  have h₂ := (mul_le_mul_of_nonneg_left hL₂U hT).trans
    (mul_le_mul_of_nonneg_right hTU (by norm_num : (0 : ℝ) ≤ (9 / 16) * (2021 / 10000)))
  exact ⟨by change T * L 0 ≤ _; linarith only [h₀],
    by change D * L 0 - T * L 1 ≤ _; linarith only [h₁,mul_nonneg hT hL₁],
    by change A * L 0 - 2 * D * L 1 + T * L 2 ≤ _; linarith only [hAD,h₂]⟩

end ACS12.GammaMeasure

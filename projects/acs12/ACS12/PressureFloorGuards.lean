import ACS12.PressureLineDebit
import ACS12.PureZetaEnvelope

/-! Complete series and inverse-scale guards for the pressure floor. -/
namespace ACS12.Pressure

open Set
open GammaMeasure (powerTail powerTail_B2 powerTail_summable powerTail_trapezoid_lower
  powerTail_exponent_antitone powerTail_shift fifth_rpow_upper fifth_rpow_lower)

theorem pressure_zeta_lt_two {p : ℝ} (hp : 7 / 4 ≤ p) : powerTail p 1 < 2 := by
  have h := powerTail_B2 (q := 7 / 4) (m := 1) (by norm_num) (by decide)
  have h' := powerTail_exponent_antitone (by norm_num : (1 : ℝ) < 7 / 4) hp (m := 1) (by decide)
  norm_num [Real.one_rpow] at h
  linarith only [h,h']

private theorem boseDebitSeries {p : ℝ} (hp : 1 < p) :
    let D (j : ℕ) := ((j : ℝ) + 1) * (p * ((j : ℝ) + 2) ^ (-(p + 1)))
    Summable D ∧ (∑' j, D j) = boseDebit p := by
  let D (j : ℕ) := ((j : ℝ) + 1) * (p * ((j : ℝ) + 2) ^ (-(p + 1)))
  let T (q : ℝ) (j : ℕ) := ((2 : ℕ) + (j : ℝ)) ^ (-q)
  have hS₁ : Summable (T p) := powerTail_summable hp 2
  have hS₂ : Summable (T (p + 1)) := powerTail_summable (by linarith only [hp]) 2
  have hPoint (j : ℕ) : D j = p * (T p j - T (p + 1) j) := by
    dsimp only [D,T]
    norm_num
    rw [show -p = -(p + 1) + 1 by ring,Real.rpow_add_one (by positivity : (2 : ℝ) + j ≠ 0)]
    have hE : (2 : ℝ) + j = j + 2 := by ring
    rw [hE]
    ring
  have hS : Summable D := ((hS₁.sub hS₂).mul_left p).congr (fun j => (hPoint j).symm)
  refine ⟨hS,?_⟩
  change (∑' j, D j) = _
  simp_rw [hPoint]
  rw [tsum_mul_left,hS₁.tsum_sub hS₂]
  change p * (powerTail p 2 - powerTail (p + 1) 2) = _
  rw [powerTail_shift hp 1,powerTail_shift (by linarith only [hp] : 1 < p + 1) 1,boseDebit]
  simp only [Nat.cast_one,Real.one_rpow]
  ring

private theorem boseDebit_antitone : AntitoneOn boseDebit (Ici (7 / 4 : ℝ)) := by
  have hTerm (x : ℝ) (hx : 2 ≤ x) :
      AntitoneOn (fun p : ℝ => p * x ^ (-(p + 1))) (Ici (7 / 4)) := by
    have hx₀ : 0 < x := zero_lt_two.trans_le hx
    have hLog : 2 / 3 < Real.log x :=
      (by linarith only [Real.log_two_gt_d9] : (2 : ℝ) / 3 < Real.log 2).trans_le
        (Real.log_le_log zero_lt_two hx)
    have hD (p : ℝ) : HasDerivAt (fun q => q * x ^ (-(q + 1)))
        (x ^ (-(p + 1)) * (1 - p * Real.log x)) p := by
      have h := hasDerivAt_id p
      convert h.mul ((h.add_const 1).neg.const_rpow hx₀) using 1
      simp only [Pi.neg_apply,id_eq,one_mul]
      ring
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · exact fun p _ => (hD p).continuousAt.continuousWithinAt
    · exact fun p _ => (hD p).differentiableAt.differentiableWithinAt
    · intro p hp
      have hp' : 7 / 4 ≤ p := interior_subset hp
      have h := mul_le_mul hLog.le hp' (by norm_num : (0 : ℝ) ≤ 7 / 4) (by linarith only [hLog])
      rw [(hD p).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hx₀.le _) (by linarith only [h])
  intro p hp q hq hpq
  have hp₀ : 1 < p := (by norm_num : (1 : ℝ) < 7 / 4).trans_le hp
  have hq₀ := hp₀.trans_le hpq
  obtain ⟨hPS,hPE⟩ := boseDebitSeries hp₀
  obtain ⟨hQS,hQE⟩ := boseDebitSeries hq₀
  rw [← hPE,← hQE]
  apply hQS.tsum_le_tsum _ hPS
  intro j
  exact mul_le_mul_of_nonneg_left (hTerm ((j : ℝ) + 2) (le_add_of_nonneg_left (Nat.cast_nonneg j)) hp hq hpq)
    (by positivity)

theorem pressure_boseDebit_lt_twentyThirds {p : ℝ} (hp : 9 / 5 ≤ p) :
    boseDebit p < 23 / 20 := by
  let P : ℝ := 9 / 5
  have hD := boseDebit_antitone (show P ∈ Ici (7 / 4 : ℝ) by norm_num [P])
    (show p ∈ Ici (7 / 4 : ℝ) from (by norm_num : (7 / 4 : ℝ) ≤ 9 / 5).trans hp) hp
  apply hD.trans_lt
  have hUpper := powerTail_B2 (q := 9 / 5) (m := 4) (by norm_num) (by decide)
  have hLower := powerTail_trapezoid_lower (q := 14 / 5) (m := 4) (by norm_num) (by decide)
  have hU (b x : ℝ) (k : ℕ) (hb : 0 < b) (hx : 0 ≤ x) (h : (b ^ k)⁻¹ < x ^ 5) :
      b ^ (-(k : ℝ) / 5) < x := fifth_rpow_upper hb hx h
  have hL (b x : ℝ) (k : ℕ) (hb : 0 < b) (hx : 0 ≤ x) (h : x ^ 5 < (b ^ k)⁻¹) :
      x < b ^ (-(k : ℝ) / 5) := fifth_rpow_lower hb hx h
  have h₂ := hU 2 (28717459 / 10^8) 9 (by norm_num) (by norm_num) (by norm_num)
  have h₃ := hU 3 (13841455 / 10^8) 9 (by norm_num) (by norm_num) (by norm_num)
  have h₄₁ := hU 4 (32987698 / 10^8) 4 (by norm_num) (by norm_num) (by norm_num)
  have h₄₂ := hU 4 (8246925 / 10^8) 9 (by norm_num) (by norm_num) (by norm_num)
  have h₄₃ := hU 4 (2061732 / 10^8) 14 (by norm_num) (by norm_num) (by norm_num)
  have h₂' := hL 2 (14358729 / 10^8) 14 (by norm_num) (by norm_num) (by norm_num)
  have h₃' := hL 3 (4613818 / 10^8) 14 (by norm_num) (by norm_num) (by norm_num)
  have h₄₂' := hL 4 (8246924 / 10^8) 9 (by norm_num) (by norm_num) (by norm_num)
  have h₄₃' := hL 4 (2061731 / 10^8) 14 (by norm_num) (by norm_num) (by norm_num)
  have hUS (m : ℕ) := powerTail_shift (q := 9 / 5) (by norm_num) m
  have hLS (m : ℕ) := powerTail_shift (q := 14 / 5) (by norm_num) m
  have h1 := hUS 1
  have h2 := hUS 2
  have h3 := hUS 3
  have h1' := hLS 1
  have h2' := hLS 2
  have h3' := hLS 3
  norm_num [Real.one_rpow,neg_div] at hUpper hLower h₂ h₃ h₄₁ h₄₂ h₄₃ h₂' h₃' h₄₂' h₄₃' h1 h2 h3 h1' h2' h3'
  have hZU : powerTail (9 / 5) 1 < 470565647 / 250000000 := by
    linarith only [hUpper,h₂,h₃,h₄₁,h₄₂,h₄₃,h1,h2,h3]
  have hZL : 448506133 / 360000000 < powerTail (14 / 5) 1 := by
    linarith only [hLower,h₂',h₃',h₄₂',h₄₃',h1',h2',h3']
  unfold boseDebit P
  norm_num
  linarith only [hZU,hZL]

end ACS12.Pressure

import ACS12.PureZetaEnvelope

/-! Complete joint-source moment prices on the closed band, including literal p = 1. -/

namespace ACS12.GammaMeasure

open scoped BigOperators

private def jointQLowerPrefix (j : Fin 19) : ℕ :=
  ![9999999999999, 717936471872, 153793943161, 51543277763, 22075674582, 11041428093, 6146493799, 3700479897, 2365257694, 1584893191, 1103336018, 792704392, 584810633, 441279206, 339510503, 265670947, 211005656, 169810475, 138272658] j

private theorem jointQ_prefix_lt (j : Fin 19) :
    (jointQLowerPrefix j : ℝ) / 10000000000000 < (1 + (j.val : ℝ)) ^ (-(19 / 5 : ℝ)) := by
  rw [← neg_div]
  apply fifth_rpow_lower (k := 19) (by positivity) (by positivity)
  fin_cases j <;> norm_num [jointQLowerPrefix]

private theorem canonicalQ_lower : (109751 / 100000 : ℝ) < powerTail (19 / 5) 1 := by
  have hTail := powerTail_trapezoid_lower (q := 19 / 5) (m := 20) (by norm_num) (by decide)
  norm_num at hTail
  have hP : (2275705252 / 10000000000000 : ℝ) < (20 : ℝ) ^ (-(14 / 5 : ℝ)) := by
    rw [← neg_div]
    exact fifth_rpow_lower (k := 14) (by norm_num) (by norm_num) (by norm_num)
  have hQ : (113785261 / 10000000000000 : ℝ) < (20 : ℝ) ^ (-(19 / 5 : ℝ)) := by
    rw [← neg_div]
    exact fifth_rpow_lower (k := 19) (by norm_num) (by norm_num) (by norm_num)
  have hS := (powerTail_summable (q := 19 / 5) (by norm_num) 1).sum_add_tsum_nat_add 19
  have hT : (∑' j : ℕ, ((1 : ℝ) + ((j + 19 : ℕ) : ℝ)) ^ (-(19 / 5 : ℝ))) = powerTail (19 / 5) 20 := by
    unfold powerTail
    apply tsum_congr
    intro j
    push_cast
    congr 1
    ring
  norm_num only [Nat.cast_one] at hS
  rw [hT, ← Fin.sum_univ_eq_sum_range] at hS
  have hSum : powerTail (19 / 5) 1 = ∑' j : ℕ, (1 + (j : ℝ)) ^ (-(19 / 5 : ℝ)) := by
    simp only [powerTail, Nat.cast_one]
  rw [← hSum] at hS
  have hC := Finset.sum_le_sum (s := Finset.univ) (fun j _ => (jointQ_prefix_lt j).le)
  have hE : (∑ j : Fin 19, (jointQLowerPrefix j : ℝ) / 10000000000000) =
      (10974234320539 / 10000000000000 : ℝ) := by
    norm_num [Fin.sum_univ_succ, jointQLowerPrefix]
  rw [hE] at hC
  linarith only [hTail, hP, hQ, hS, hC]

theorem jointQ_lower {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    (109751 / 100000) * (p * (p + 1)) < pureQ p := by
  have h := powerTail_exponent_antitone (q := p + 2) (r := 19 / 5) (by linarith only [hp])
    (by linarith only [hP]) (by decide : 0 < (1 : ℕ))
  unfold pureQ
  have hN : 0 < p * (p + 1) := by have hp₀ := zero_lt_one.trans_le hp; positivity
  exact (mul_lt_mul_of_pos_right (canonicalQ_lower.trans_le h) hN).trans_eq (mul_comm _ _)

noncomputable def pureP (p : ℝ) : ℝ := p * (p - 1) * powerTail (p + 1) 1

theorem pureP_nonneg {p : ℝ} (hp : 1 ≤ p) : 0 ≤ pureP p := by
  unfold pureP
  have hp₀ := zero_lt_one.trans_le hp
  exact mul_nonneg (mul_nonneg hp₀.le (sub_nonneg.mpr hp))
    (powerTail_pos (by linarith only [hp]) (by decide : 0 < (1 : ℕ))).le

theorem jointSource_Q_sub_twoP_gt {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    6 / 7 < pureQ p - 2 * pureP p - 1 := by
  let t := p - 1
  have ht : 0 ≤ t := sub_nonneg.mpr hp
  have ht' : t ≤ 4 / 5 := by dsimp only [t]; linarith only [hP]
  have ht₂ := pow_le_pow_left₀ ht ht' 2
  have hE : (109751 / 100000) * (p * (p + 1)) - 2 * middlePowerUpper p - 1 =
      (59751 / 50000) + (259 / 300000) * t ^ 1 + (-(422207 / 800000)) * t ^ 2 + (27923 / 192000) * t ^ 3 + (3547 / 320000) * t ^ 4 := by
    unfold middlePowerUpper
    dsimp only [t]
    ring
  have h := middle_powerMoment_le hp hP
  have hQ := jointQ_lower hp hP
  change pureP p ≤ middlePowerUpper p at h
  have hL : (109751 / 100000) * (p * (p + 1)) - 2 * middlePowerUpper p - 1 > 6 / 7 := by
    rw [hE]
    nlinarith only [ht, ht₂, pow_nonneg ht 3, pow_nonneg ht 4]
  linarith only [h, hQ, hL]

theorem jointSource_c0_lt {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    (1 + 2 * p + 2 * pureP p - pureQ p + (2 : ℝ) ^ (-p)) / (pureQ p - pureP p) < 4 / 5 := by
  let t := p - 1
  let T : ℝ := 4 / 5
  have ht : 0 ≤ t := sub_nonneg.mpr hp
  have ht' : t ≤ T := by dsimp only [t, T]; linarith only [hP]
  let e (s : ℝ) := (112759 / 250000) + (-(156011 / 375000)) * s ^ 1 + (-(1199433 / 4000000)) * s ^ 2 + (195461 / 960000) * s ^ 3 + (24829 / 1600000) * s ^ 4
  have hE : (9 / 5) * ((109751 / 100000) * (p * (p + 1))) - (14 / 5) * middlePowerUpper p -
      2 * p - 1 - (1 / 2 - (1063 / 4000) * t) = e t := by
    unfold middlePowerUpper
    dsimp only [t, e]
    ring
  let S := -(-(156011 / 375000)) - (-(1199433 / 4000000)) * (T + t) -
    (195461 / 960000) * (T ^ 2 + T * t + t ^ 2) -
    (24829 / 1600000) * (T ^ 3 + T ^ 2 * t + T * t ^ 2 + t ^ 3)
  have hD : e t = e T + (T - t) * S := by dsimp only [e, S]; ring
  have hT₀ : 0 ≤ T := by norm_num [T]
  have ht₂ := pow_le_pow_left₀ ht ht' 2
  have ht₃ := pow_le_pow_left₀ ht ht' 3
  have hS₂ : T ^ 2 + T * t + t ^ 2 ≤ 3 * T ^ 2 := by
    nlinarith only [ht₂, mul_le_mul_of_nonneg_left ht' hT₀]
  have hS₃ : T ^ 3 + T ^ 2 * t + T * t ^ 2 + t ^ 3 ≤ 4 * T ^ 3 := by
    nlinarith only [ht₃, mul_le_mul_of_nonneg_left ht' (sq_nonneg T),
      mul_le_mul_of_nonneg_left ht₂ hT₀]
  have hS : 0 ≤ S := by
    have h₂ := mul_le_mul_of_nonneg_left hS₂ (show 0 ≤ (195461 / 960000) by norm_num)
    have h₃ := mul_le_mul_of_nonneg_left hS₃ (show 0 ≤ (24829 / 1600000) by norm_num)
    dsimp only [S, T] at h₂ h₃ ⊢
    nlinarith only [h₂, h₃, ht]
  have hL : 0 < e t := by
    rw [hD]
    exact add_pos_of_pos_of_nonneg (by norm_num [e, T]) (mul_nonneg (sub_nonneg.mpr ht') hS)
  have hP' := middle_powerMoment_le hp hP
  change pureP p ≤ middlePowerUpper p at hP'
  have hQ := jointQ_lower hp hP
  have hX := two_neg_rpow_chord hp hP
  change (2 : ℝ) ^ (-p) ≤ 1 / 2 - (1063 / 4000) * t at hX
  have hPos : 0 < pureQ p - pureP p := by
    linarith only [jointSource_Q_sub_twoP_gt hp hP, pureP_nonneg hp]
  apply (div_lt_iff₀ hPos).mpr
  linarith only [hE, hL, hP', hQ, hX]

theorem jointCone_inner_moment_lt {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    1 + pureP p < (3 / 4) * (pureQ p - pureP p) := by
  let t := 9 / 5 - p
  have ht : 0 ≤ t := sub_nonneg.mpr hP
  have htU : t ≤ 4 / 5 := by unfold t; linarith only [hp]
  have hP' := middle_powerMoment_le hp hP
  change pureP p ≤ middlePowerUpper p at hP'
  have hQ := jointQ_lower hp hP
  have hE : (3 / 4) * ((109751 / 100000) * (p * (p + 1))) -
      (7 / 4) * middlePowerUpper p - 1 =
      169847 / 50000000 + (33149569 / 30000000) * t -
        (8202443 / 32000000) * t ^ 2 - (6078317 / 38400000) * t ^ 3 +
        (24829 / 2560000) * t ^ 4 := by
    unfold middlePowerUpper t
    ring
  have ht₂ := mul_le_mul_of_nonneg_right htU ht
  have ht₃ := mul_le_mul_of_nonneg_right htU (sq_nonneg t)
  have ht₃' := mul_le_mul_of_nonneg_left ht₂ (show (0 : ℝ) ≤ 4 / 5 by norm_num)
  have hL : 0 < (3 / 4) * ((109751 / 100000) * (p * (p + 1))) -
      (7 / 4) * middlePowerUpper p - 1 := by
    rw [hE]
    nlinarith only [ht,ht₂,ht₃,ht₃',pow_nonneg ht 4]
  linarith only [hL,hQ,hP']

end ACS12.GammaMeasure

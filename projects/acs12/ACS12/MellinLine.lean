import ACS12.LowScalar
import CenteredCircle.ScalarTail

/-! The fixed-ratio scalar Mellin sign, with the entire convergent tail. -/

namespace ACS12.LowScalar

open Set MeasureTheory Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

/-- The smooth form of the Bose difference at the only mass ratio needed
for the selected Mellin transport, namely (b=2/3). -/
noncomputable def boseTwoThirds (s : ℝ) : ℝ :=
  let x := Real.exp (s / 3)
  x ^ 3 * (2 * x + 1) / (3 * (x + 1) * (x ^ 2 + x + 1))

theorem boseTwoThirds_eq {s : ℝ} (hs : 0 < s) :
    boseTwoThirds s =
      Real.exp s * ((2 / 3 : ℝ) / (Real.exp (2 / 3 * s) - 1) -
        1 / (Real.exp s - 1)) := by
  let x := Real.exp (s / 3)
  have hx : 1 < x := Real.one_lt_exp_iff.mpr (by positivity)
  have h1 : Real.exp s = x ^ 3 := by
    dsimp only [x]
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h2 : Real.exp (2 / 3 * s) = x ^ 2 := by
    dsimp only [x]
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hxp : 0 < x := zero_lt_one.trans hx
  have ha : x ^ 2 - 1 ≠ 0 := by nlinarith
  have hb : x ^ 3 - 1 ≠ 0 := by
    have h := pow_lt_pow_left₀ hx (by norm_num : (0 : ℝ) ≤ 1) (by decide : 3 ≠ 0)
    norm_num at h
    exact (sub_pos.mpr h).ne'
  unfold boseTwoThirds
  rw [h1, h2]
  change x ^ 3 * (2 * x + 1) / (3 * (x + 1) * (x ^ 2 + x + 1)) =
    x ^ 3 * ((2 / 3 : ℝ) / (x ^ 2 - 1) - 1 / (x ^ 3 - 1))
  field_simp [ha, hb, show x + 1 ≠ 0 by positivity, show x ^ 2 + x + 1 ≠ 0 by positivity]
  ring

private theorem bose_pos (s : ℝ) : 0 < boseTwoThirds s := by
  unfold boseTwoThirds
  positivity

private theorem bose_factor (s : ℝ) :
    boseTwoThirds s =
      let x := Real.exp (s / 3)
      (2 - 1 / (x + 1)) * (x / (1 + 1 / x + 1 / x ^ 2)) / 3 := by
  unfold boseTwoThirds
  let x := Real.exp (s / 3)
  have hx : 0 < x := Real.exp_pos _
  change x ^ 3 * (2 * x + 1) / (3 * (x + 1) * (x ^ 2 + x + 1)) =
    (2 - 1 / (x + 1)) * (x / (1 + 1 / x + 1 / x ^ 2)) / 3
  field_simp [hx.ne', show x + 1 ≠ 0 by positivity, show x ^ 2 + x + 1 ≠ 0 by positivity,
    show 1 + 1 / x + 1 / x ^ 2 ≠ 0 by positivity]
  ring

private theorem bose_monotone : Monotone boseTwoThirds := by
  intro s t hst
  rw [bose_factor, bose_factor]
  let x := Real.exp (s / 3)
  let y := Real.exp (t / 3)
  have hx : 0 < x := Real.exp_pos _
  have hy : 0 < y := Real.exp_pos _
  have hxy : x ≤ y := Real.exp_le_exp.mpr (by linarith)
  have h₁ : 2 - 1 / (x + 1) ≤ 2 - 1 / (y + 1) :=
    sub_le_sub_left (one_div_le_one_div_of_le (by positivity) (by linarith)) _
  have h₁p : 0 ≤ 2 - 1 / (y + 1) := by
    have hh : 1 / (y + 1) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).mpr
      linarith
    linarith
  have hden : 1 + 1 / y + 1 / y ^ 2 ≤ 1 + 1 / x + 1 / x ^ 2 :=
    add_le_add (add_le_add_right (one_div_le_one_div_of_le hx hxy) 1)
      (one_div_le_one_div_of_le (pow_pos hx _) (pow_le_pow_left₀ hx.le hxy _))
  have h₂ : x / (1 + 1 / x + 1 / x ^ 2) ≤ y / (1 + 1 / y + 1 / y ^ 2) :=
    (div_le_div_of_nonneg_right hxy (by positivity)).trans
      (div_le_div_of_nonneg_left hy.le (by positivity) hden)
  exact div_le_div_of_nonneg_right (mul_le_mul h₁ h₂ (by positivity) h₁p) (by norm_num)

private theorem bose_lower {s : ℝ} (hs : 0 ≤ s) : Real.exp (s / 3) / 9 ≤ boseTwoThirds s := by
  let x := Real.exp (s / 3)
  have hx : 0 < x := Real.exp_pos _
  have hx1 : 1 ≤ x := Real.one_le_exp_iff.mpr (by linarith)
  change x / 9 ≤ x ^ 3 * (2 * x + 1) / (3 * (x + 1) * (x ^ 2 + x + 1))
  apply (le_div_iff₀ (by positivity)).mpr
  have hsq : x ^ 2 + x + 1 ≤ 3 * x ^ 2 := by nlinarith [sq_nonneg (x - 1)]
  calc
    x / 9 * (3 * (x + 1) * (x ^ 2 + x + 1)) ≤ x / 9 * (3 * (x + 1) * (3 * x ^ 2)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq (by positivity)) (by positivity)
    _ = x ^ 3 * (x + 1) := by ring
    _ ≤ x ^ 3 * (2 * x + 1) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

private noncomputable def ratio (s : ℝ) : ℝ := 4 - 25 / (s + 5) + Real.exp (-s)

private theorem ratio_deriv {s : ℝ} (hs : 0 ≤ s) :
    HasDerivAt ratio (25 / (s + 5) ^ 2 - Real.exp (-s)) s := by
  have hden := (hasDerivAt_id s).add_const 5
  have hd : s + 5 ≠ 0 := by positivity
  have hq := (hasDerivAt_const s (25 : ℝ)).div hden hd
  have he := (Real.hasDerivAt_exp (-s)).comp s (hasDerivAt_id s).neg
  have h := ((hasDerivAt_const s (4 : ℝ)).sub hq).add he
  convert h using 1
  simp only [id_eq, zero_mul, mul_one, mul_neg]
  ring

private theorem ratio_strictMono : StrictMonoOn ratio (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · exact fun s hs => (ratio_deriv hs).continuousAt.continuousWithinAt
  · intro s hs
    have hs0 : 0 < s := by simpa only [interior_Ici, mem_Ioi] using hs
    rw [(ratio_deriv hs0.le).deriv, sub_pos, Real.exp_neg]
    have hpos : 0 < (s + 5) ^ 2 / 25 := by positivity
    have hsmall : (s + 5) / 5 < Real.exp (s / 2) := by
      linarith only [Real.add_one_lt_exp (show s / 2 ≠ 0 by positivity), hs0]
    have hsq : ((s + 5) / 5) ^ 2 < Real.exp (s / 2) ^ 2 :=
      pow_lt_pow_left₀ hsmall (by positivity) (by decide)
    rw [← Real.exp_nat_mul, show (2 : ℕ) * (s / 2) = s by push_cast; ring] at hsq
    have hE : (s + 5) ^ 2 / 25 < Real.exp s := by
      rw [div_pow, show (5 : ℝ) ^ 2 = 25 by norm_num] at hsq
      exact hsq
    have hInv := (inv_lt_inv₀ (Real.exp_pos s) hpos).mpr hE
    simpa only [inv_div] using hInv

private theorem ratio_zero : ratio 0 = 0 := by norm_num [ratio]

private noncomputable def crossValue (s : ℝ) : ℝ := boseTwoThirds s * ratio s

private theorem crossValue_strictMono : StrictMonoOn crossValue (Ici 0) := by
  intro s hs t ht hst
  have hnon : 0 ≤ ratio s := by
    rw [← ratio_zero]
    exact ratio_strictMono.monotoneOn (by simp) hs hs
  unfold crossValue
  calc
    _ ≤ boseTwoThirds t * ratio s := mul_le_mul_of_nonneg_right (bose_monotone hst.le) hnon
    _ < _ := mul_lt_mul_of_pos_left (ratio_strictMono hs ht hst) (bose_pos t)

private theorem crossValue_at_five : (1 / 3 : ℝ) < crossValue 5 := by
  have hE : (8 / 27 : ℝ) < boseTwoThirds 5 := by
    have h := Real.add_one_lt_exp (show (5 : ℝ) / 3 ≠ 0 by norm_num)
    linarith only [bose_lower (show 0 ≤ (5 : ℝ) by norm_num), h]
  have hR : (3 / 2 : ℝ) < ratio 5 := by
    unfold ratio
    linarith only [Real.exp_pos (-(5 : ℝ))]
  have h := mul_lt_mul_of_pos_right hE (show 0 < (3 / 2 : ℝ) by norm_num)
  have h' := mul_lt_mul_of_pos_left hR (bose_pos 5)
  unfold crossValue
  linarith

private theorem crossValue_continuousOn : ContinuousOn crossValue (Ici 0) := by
  have hE : Continuous (fun s : ℝ => Real.exp (s / 3)) :=
    Real.continuous_exp.comp (continuous_id.div_const 3)
  have hC : Continuous boseTwoThirds := by
    unfold boseTwoThirds
    exact ((hE.pow 3).mul ((continuous_const.mul hE).add continuous_const)).div
      ((continuous_const.mul (hE.add continuous_const)).mul
        (((hE.pow 2).add hE).add continuous_const)) (fun _ => by positivity)
  have hR : ContinuousOn ratio (Ici 0) := fun s hs => (ratio_deriv hs).continuousAt.continuousWithinAt
  exact hC.continuousOn.mul hR

/-- The exact signed integrand factor used at (b=2/3,lambda=1/4). -/
noncomputable def mellinDefect (s : ℝ) : ℝ :=
  (s / 4 + 5 / 4) * (crossValue s - 1 / 3)

theorem mellinDefect_eq {s : ℝ} (hs : 0 < s) :
    mellinDefect s = Real.exp s *
      (s - 1 + Real.exp (-s) - (1 / 4) * (1 - (1 + s) * Real.exp (-s))) *
      ((2 / 3 : ℝ) / (Real.exp (2 / 3 * s) - 1) - 1 / (Real.exp s - 1)) -
      (1 / 3) * (s / 4 + 5 / 4) := by
  rw [mellinDefect, crossValue, boseTwoThirds_eq hs, ratio]
  field_simp [show s + 5 ≠ 0 by positivity]
  ring

/-- The actual fixed-ratio Mellin factor changes sign exactly once. -/
theorem mellinDefect_crossing :
    ∃ c ∈ Ioo (0 : ℝ) 5, mellinDefect c = 0 ∧
      (∀ s ∈ Ioo 0 c, mellinDefect s < 0) ∧ (∀ s ∈ Ioi c, 0 < mellinDefect s) := by
  have hz : crossValue 0 = 0 := by simp [crossValue, ratio_zero]
  have hs : ContinuousOn crossValue (Icc 0 5) :=
    crossValue_continuousOn.mono fun _ h => h.1
  have hex : (1 / 3 : ℝ) ∈ crossValue '' Icc 0 5 :=
    intermediate_value_Icc (by norm_num) hs ⟨by rw [hz]; norm_num, crossValue_at_five.le⟩
  obtain ⟨c, hc, hC⟩ := hex
  have hc0 : 0 < c := lt_of_le_of_ne hc.1 (by intro h; rw [← h, hz] at hC; norm_num at hC)
  have hc5 : c < 5 := lt_of_le_of_ne hc.2 (by intro h; rw [h] at hC; linarith [crossValue_at_five])
  refine ⟨c, ⟨hc0, hc5⟩, ?_, ?_, ?_⟩
  · rw [mellinDefect, hC, sub_self, mul_zero]
  · intro s hs'
    have h := crossValue_strictMono hs'.1.le hc0.le hs'.2
    rw [hC] at h
    exact mul_neg_of_pos_of_neg (by have := hs'.1; positivity) (sub_neg.mpr h)
  · intro s hs'
    have hs0 : 0 < s := hc0.trans hs'
    have h := crossValue_strictMono hc0.le hs0.le hs'
    rw [hC] at h
    exact mul_pos (by positivity) (sub_pos.mpr h)

private theorem bose_upper (s : ℝ) : boseTwoThirds s ≤ Real.exp (s / 3) := by
  let x := Real.exp (s / 3)
  have hx : 0 < x := Real.exp_pos _
  change x ^ 3 * (2 * x + 1) / (3 * (x + 1) * (x ^ 2 + x + 1)) ≤ x
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith only [pow_nonneg hx.le 4, pow_nonneg hx.le 3, sq_nonneg x, hx.le]

private theorem defect_bound {s : ℝ} (hs : 0 ≤ s) :
    |mellinDefect s| ≤ 8 * (s + 1) * Real.exp (s / 3) := by
  have hR0 : 0 ≤ ratio s := by
    rw [← ratio_zero]
    exact ratio_strictMono.monotoneOn (by simp) hs hs
  have hR5 : ratio s ≤ 5 := by
    unfold ratio
    linarith only [show 0 ≤ 25 / (s + 5) by positivity,
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs)]
  have hE0 := (bose_pos s).le
  have hX : 1 ≤ Real.exp (s / 3) := Real.one_le_exp_iff.mpr (by positivity)
  have hP0 : 0 ≤ crossValue s := mul_nonneg hE0 hR0
  have hP5 : crossValue s ≤ 5 * Real.exp (s / 3) := by
    rw [crossValue, mul_comm (5 : ℝ)]
    exact mul_le_mul (bose_upper s) hR5 hR0 (by positivity)
  rw [mellinDefect, abs_mul, abs_of_nonneg (by positivity : 0 ≤ s / 4 + 5 / 4)]
  have habs : |crossValue s - 1 / 3| ≤ 6 * Real.exp (s / 3) := by
    rw [abs_le]
    constructor <;> linarith
  calc
    _ ≤ (s / 4 + 5 / 4) * (6 * Real.exp (s / 3)) :=
      mul_le_mul_of_nonneg_left habs (by positivity)
    _ = (6 * (s / 4 + 5 / 4)) * Real.exp (s / 3) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

noncomputable def mellinIntegrand (p s : ℝ) : ℝ :=
  s ^ (p - 1) * (Real.exp (-s) * mellinDefect s)

/-- The weighted actual Mellin integrand is integrable at zero and infinity
for every positive power. -/
theorem mellinIntegrand_integrable {p : ℝ} (hp : 0 < p) :
    IntegrableOn (mellinIntegrand p) (Ioi 0) := by
  have h1 := CenteredCircle.AllN.integrable_gamma_laplace hp (r := 2 / 3) (by norm_num)
  have h2 := CenteredCircle.AllN.integrable_gamma_laplace (a := p + 1)
    (by positivity) (r := 2 / 3) (by norm_num)
  have hdom : IntegrableOn (fun s : ℝ =>
      8 * (s ^ (p - 1) * Real.exp (-(2 / 3 * s)) + s ^ p * Real.exp (-(2 / 3 * s)))) (Ioi 0) := by
    simpa only [add_sub_cancel_right] using (h1.add h2).const_mul 8
  have hmeas : Measurable (mellinIntegrand p) := by
    unfold mellinIntegrand mellinDefect crossValue boseTwoThirds ratio
    fun_prop
  apply hdom.mono' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs0 : 0 < s := hs
  have hx := Real.rpow_nonneg hs0.le (p - 1)
  rw [Real.norm_eq_abs, mellinIntegrand, abs_mul, abs_mul, abs_of_nonneg hx,
    abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ s ^ (p - 1) * (Real.exp (-s) * (8 * (s + 1) * Real.exp (s / 3))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (defect_bound hs0.le) (by positivity)) hx
    _ = 8 * (s ^ (p - 1) + s ^ p) * (Real.exp (-s) * Real.exp (s / 3)) := by
      rw [show s ^ p = s ^ (p - 1) * s by
        rw [show s ^ p = s ^ ((p - 1) + 1) by congr 1; ring,
          Real.rpow_add hs0, Real.rpow_one]]
      ring
    _ = _ := by rw [← Real.exp_add, show -s + s / 3 = -(2 / 3 * s) by ring]; ring

/-- The signed crossing transports negativity of the literal-one integral
to each lower positive power. -/
theorem actual_mellin_neg_of_endpoint {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hend : (∫ s in Ioi (0 : ℝ), Real.exp (-s) * mellinDefect s) < 0) :
    (∫ s in Ioi (0 : ℝ), mellinIntegrand p s) < 0 := by
  obtain ⟨c, hc, _, hl, hr⟩ := mellinDefect_crossing
  have h1 : IntegrableOn (fun s : ℝ => Real.exp (-s) * mellinDefect s) (Ioi 0) := by
    have he : mellinIntegrand 1 = (fun s : ℝ => Real.exp (-s) * mellinDefect s) := by
      funext s
      simp only [mellinIntegrand, sub_self, Real.rpow_zero, one_mul]
    rw [← he]
    exact mellinIntegrand_integrable one_pos
  exact mellin_crossing_neg hc.1 hp1 h1 (mellinIntegrand_integrable hp)
    (fun s hs => (mul_neg_of_pos_of_neg (Real.exp_pos _) (hl s hs)).le)
    (fun s hs => (mul_pos (Real.exp_pos _) (hr s hs)).le) hend

open CenteredCircle.AllN

private theorem weightedDefect_eq_residual {s : ℝ} (hs : 0 < s) :
    Real.exp (-s) * mellinDefect s = lineResidualDensity s (2 / 3) := by
  have hv : rightMixPolynomial s =
      s - 1 + Real.exp (-s) - (1 / 4) * (1 - (1 + s) * Real.exp (-s)) := by
    unfold rightMixPolynomial polyA polyB
    ring
  have hΔ : ((2 / 3 : ℝ) / (Real.exp (2 / 3 * s) - 1) - 1 / (Real.exp s - 1)) =
      scaledExpTail s (2 / 3) - scaledExpTail s 1 := by
    simp only [scaledExpTail, mul_one, mul_comm (2 / 3 : ℝ) s]
  have hE : Real.exp (-s) * Real.exp s = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hsum : leftMixPolynomial s * scaledExpTail s 1 + rightMixPolynomial s * scaledExpTail s 1 =
      (3 / 4 : ℝ) * s * Real.exp (-s) := by
    rw [← add_mul]
    exact polynomial_total_sample hs
  rw [mellinDefect_eq hs, ← hv, hΔ]
  calc
    _ = rightMixPolynomial s * (scaledExpTail s (2 / 3) - scaledExpTail s 1) -
        Real.exp (-s) * (1 / 3) * (s / 4 + 5 / 4) := by
      rw [mul_sub, ← mul_assoc, ← mul_assoc, hE, one_mul]
      ring
    _ = _ := by
      unfold lineResidualDensity
      linear_combination -hsum

private theorem cubic_tail_general (N : ℕ) (hN : 0 < N) :
    (∑' j : ℕ, 1 / ((j : ℝ) + N + 1) ^ 3) ≤ 1 / (2 * (N : ℝ) ^ 2) := by
  have hS : Summable (fun j : ℕ => 1 / ((j : ℝ) + N + 1) ^ 3) := by
    have h := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (3 : ℕ))
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using (summable_nat_add_iff (N + 1)).mpr h
  have hprefix (k : ℕ) : (∑ j ∈ Finset.range k, 1 / ((j : ℝ) + N + 1) ^ 3) ≤
      1 / (2 * (N : ℝ) ^ 2) - 1 / (2 * ((k : ℝ) + N) ^ 2) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      have hP : 0 < (k : ℝ) + (N : ℝ) := by
        have : 0 < (N : ℝ) := by exact_mod_cast hN
        positivity
      have h := cubic_step_bound hP
      rw [show ((k + 1 : ℕ) : ℝ) + (N : ℝ) = (k : ℝ) + (N : ℝ) + 1 by push_cast; ring]
      linarith only [h, ih]
  apply le_of_tendsto hS.hasSum.tendsto_sum_nat
  exact Eventually.of_forall fun k => (hprefix k).trans (sub_le_self _ (by positivity))

private theorem rational_tail_general {b : ℝ} (hb : 0 < b) (N : ℕ) (hN : 0 < N) :
    (∑' j : ℕ, rationalPair b (j + N)) ≤ (1 + b⁻¹ ^ 2) / (2 * (N : ℝ) ^ 2) := by
  have hs := (summable_nat_add_iff N).mpr (rationalPair_summable hb)
  have hS : Summable (fun j : ℕ => 1 / ((j : ℝ) + N + 1) ^ 3) := by
    have h := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (3 : ℕ))
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using (summable_nat_add_iff (N + 1)).mpr h
  have hcomp (j : ℕ) : rationalPair b (j + N) ≤ (1 + b⁻¹ ^ 2) * (1 / ((j : ℝ) + N + 1) ^ 3) := by
    have h := comparison_pair_cubic_bound (t := (j : ℝ) + N + 1) hb (by positivity)
    simpa only [rationalPair, Nat.cast_add, mul_one_div] using h
  have hh := hs.tsum_le_tsum hcomp (hS.mul_left (1 + b⁻¹ ^ 2))
  rw [tsum_mul_left] at hh
  exact hh.trans (by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left (cubic_tail_general N hN) (by positivity))

set_option maxHeartbeats 2500000 in
private theorem lineTwoThirds_neg : lineScalar (2 / 3) < 0 := by
  have hb : 0 < (2 / 3 : ℝ) := by norm_num
  have htail := rational_tail_general hb 12 (by decide)
  have hseries := (rationalPair_summable hb).sum_add_tsum_nat_add 12
  rw [lineScalar_eq_rational hb, ← hseries]
  have hcert : (∑ j ∈ Finset.range 12, rationalPair (2 / 3) j) +
      (1 + (2 / 3 : ℝ)⁻¹ ^ 2) / (2 * (12 : ℝ) ^ 2) - 9 / 4 + (3 / 2) * (2 / 3) < 0 := by
    norm_num [rationalPair, comparisonF, comparisonG, Finset.sum_range_succ]
  norm_num at htail ⊢
  norm_num at hcert
  linarith only [htail, hcert]

/-- The literal-one integral is negative by a twelve-term rational
certificate and the telescoping cubic bound on the full tail. -/
theorem literalOneMellin_neg :
    (∫ s in Ioi (0 : ℝ), Real.exp (-s) * mellinDefect s) < 0 := by
  have he : (∫ s in Ioi (0 : ℝ), Real.exp (-s) * mellinDefect s) = lineScalar (2 / 3) := by
    rw [(lineScalar_integral (by norm_num : (0 : ℝ) < 2 / 3)).2]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact weightedDefect_eq_residual hs
  rw [he]
  exact lineTwoThirds_neg

/-- Negativity of the actual Mellin integral throughout the low band. -/
theorem actual_mellin_neg {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    (∫ s in Ioi (0 : ℝ), mellinIntegrand p s) < 0 :=
  actual_mellin_neg_of_endpoint hp hp1 literalOneMellin_neg

end ACS12.LowScalar

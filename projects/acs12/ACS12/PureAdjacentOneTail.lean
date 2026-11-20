import ACS12.PurePeanoIntegral
import ACS12.PureZetaEnvelope

/-! Entire endpoint tails for the normalized p = 1 adjacent source. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN Set
open scoped BigOperators

private noncomputable def oneATerm (τ : ℝ) (j : ℕ) : ℝ :=
  1 / (((j : ℝ) + 1) * (((j : ℝ) + 1) * τ + 1) ^ 2)

theorem powerTail_three_eq (m : ℕ) :
    powerTail 3 m = ∑' j : ℕ, 1 / (((m : ℝ) + j) ^ 3) := by
  unfold powerTail
  apply tsum_congr
  intro j
  rw [Real.rpow_neg (by positivity), show (3 : ℝ) = (3 : ℕ) by norm_num,
    Real.rpow_natCast, inv_eq_one_div]

theorem cubic_samples_summable (m : ℕ) :
    Summable (fun j : ℕ => (1 : ℝ) / (((m : ℝ) + j) ^ 3)) := by
  apply (powerTail_summable (by norm_num : (1 : ℝ) < 3) m).congr
  intro j
  rw [Real.rpow_neg (by positivity), show (3 : ℝ) = (3 : ℕ) by norm_num,
    Real.rpow_natCast, inv_eq_one_div]

private theorem oneATerm_le {τ r : ℝ} (hτ : 0 < τ) (hr : 0 < r) :
    1 / (r * (r * τ + 1) ^ 2) ≤ (1 / τ ^ 2) * (1 / r ^ 3) := by
  have hD : 0 < r * (r * τ) ^ 2 := by positivity
  calc
    _ ≤ 1 / (r * (r * τ) ^ 2) := by
      apply div_le_div_of_nonneg_left zero_le_one hD
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_pos hr hτ).le (le_add_of_nonneg_right zero_le_one) 2) hr.le
    _ = _ := by field_simp [hτ.ne', hr.ne']

private theorem oneATerm_summable {τ : ℝ} (hτ : 0 < τ) :
    Summable (oneATerm τ) := by
  have h := (cubic_samples_summable 1).mul_left (1 / τ ^ 2)
  apply h.of_nonneg_of_le
  · intro j
    unfold oneATerm
    positivity
  · intro j
    simp only [Nat.cast_one]
    change _ ≤ (1 / τ ^ 2) * (1 / ((1 : ℝ) + j) ^ 3)
    rw [add_comm (1 : ℝ) (j : ℝ)]
    exact oneATerm_le hτ (by positivity)

private theorem oneAStack_eq {τ : ℝ} (hτ : 0 < τ) :
    samplingHead (purePeanoA 1 1) τ τ = ∑' j : ℕ, oneATerm τ j := by
  unfold samplingHead
  rw [← tsum_mul_left]
  apply tsum_congr
  intro j
  have hx : 0 < τ + j * τ := by positivity
  have hEq : τ + (j : ℝ) * τ = ((j : ℝ) + 1) * τ := by ring
  rw [purePeanoA_one zero_lt_one hx, hEq, oneATerm]
  field_simp [hτ.ne']

theorem oneAStack_reference_lt :
    samplingHead (purePeanoA 1 1) (146 / 175) (146 / 175) < 87 / 200 := by
  let c : ℝ := 146 / 175
  have hc : 0 < c := by norm_num [c]
  rw [oneAStack_eq hc]
  have hS := oneATerm_summable hc
  have hSplit := hS.sum_add_tsum_nat_add 12
  have hT : (∑' j : ℕ, oneATerm c (j + 12)) ≤ (1 / c ^ 2) * powerTail 3 13 := by
    rw [powerTail_three_eq, ← tsum_mul_left]
    apply ((summable_nat_add_iff 12).mpr hS).tsum_le_tsum _ ((cubic_samples_summable 13).mul_left _)
    intro j
    have hE : (((j + 12 : ℕ) : ℝ) + 1) = (13 : ℝ) + j := by push_cast; ring
    rw [oneATerm, hE]
    exact oneATerm_le hc (by positivity)
  have hB := powerTail_B2 (q := 3) (m := 13) (by norm_num) (by decide)
  have hE : powerTail 3 13 < 1 / (2 * 13 ^ 2) + 1 / (2 * 13 ^ 3) + 1 / (4 * 13 ^ 4) := by
    norm_num at hB ⊢
    exact hB
  have hFin : (∑ j ∈ Finset.range 12, oneATerm c j) +
      (1 / c ^ 2) * (1 / (2 * 13 ^ 2) + 1 / (2 * 13 ^ 3) + 1 / (4 * 13 ^ 4)) < 87 / 200 := by
    norm_num [oneATerm, c, Finset.sum_range_succ]
  have hT' := hT.trans_lt (mul_lt_mul_of_pos_left hE (by positivity : 0 < 1 / c ^ 2))
  linarith only [hSplit, hFin, hT']

theorem powerTail_three_gt_six_fifths : (6 / 5 : ℝ) < powerTail 3 1 := by
  have hA := powerTail_trapezoid_lower (q := 3) (m := 4) (by norm_num) (by decide)
  have hB := powerTail_shift (q := 3) (by norm_num) 1
  have hC := powerTail_shift (q := 3) (by norm_num) 2
  have hD := powerTail_shift (q := 3) (by norm_num) 3
  norm_num at hA hB hC hD
  linarith only [hA, hB, hC, hD]

theorem oneAStack_le_reference_drop {τ : ℝ} (hτ : 146 / 175 ≤ τ) (hτ₁ : τ ≤ 1) :
    samplingHead (purePeanoA 1 1) τ τ ≤ 87 / 200 - (2 / 5) * (τ - 146 / 175) := by
  let c : ℝ := 146 / 175
  have hc : 0 < c := by norm_num [c]
  have hτ₀ := hc.trans_le hτ
  have hPoint (j : ℕ) : oneATerm τ j + 2 * (τ - c) * (1 / (((2 : ℝ) + j) ^ 3)) ≤ oneATerm c j := by
    let r := (j : ℝ) + 1
    let f (x : ℝ) := 1 / (r * (r * x + 1) ^ 2)
    let K := 2 / (r + 1) ^ 3
    have hr : 0 < r := by dsimp only [r]; positivity
    have hd (x : ℝ) (hx : 0 < x) : HasDerivAt f (-2 / (r * x + 1) ^ 3) x := by
      have hDen := ((((hasDerivAt_id x).const_mul r).add_const 1).pow 2).const_mul r
      have hN : r * (r * x + 1) ^ 2 ≠ 0 := by positivity
      convert (hasDerivAt_const x (1 : ℝ)).div hDen hN using 1
      simp only [id_eq, Nat.cast_ofNat, mul_one]
      norm_num
      field_simp [(show r * x + 1 ≠ 0 by positivity), hr.ne']
    have hD (x : ℝ) (hx : 0 < x) :
        HasDerivAt (fun y => f y + K * y) (-2 / (r * x + 1) ^ 3 + K) x := by
      simpa only [mul_one] using (hd x hx).add ((hasDerivAt_id x).const_mul K)
    have hAnti : AntitoneOn (fun y => f y + K * y) (Icc c τ) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      · exact fun x hx => (hD x (hc.trans_le hx.1)).continuousAt.continuousWithinAt
      · exact fun x hx => (hD x (hc.trans_le (interior_subset hx).1)).differentiableAt.differentiableWithinAt
      · intro x hx
        have hx' : x ∈ Icc c τ := interior_subset hx
        have hx₀ := hc.trans_le hx'.1
        rw [(hD x hx₀).deriv]
        have hR : r * x + 1 ≤ r + 1 := by
          exact add_le_add_left (mul_le_of_le_one_right hr.le (hx'.2.trans hτ₁)) 1
        have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
          (by positivity : 0 < (r * x + 1) ^ 3) (pow_le_pow_left₀ (by positivity) hR 3)
        dsimp only [K]
        rw [neg_div, add_comm]
        exact sub_nonpos.mpr h
    have h := hAnti ⟨le_rfl, hτ⟩ ⟨hτ, le_rfl⟩ hτ
    have hK : K = 2 * (1 / (((2 : ℝ) + j) ^ 3)) := by
      dsimp only [K, r]
      rw [show (j : ℝ) + 1 + 1 = 2 + j by ring]
      ring
    change f τ + 2 * (τ - c) * (1 / (((2 : ℝ) + j) ^ 3)) ≤ f c
    change f τ + K * τ ≤ f c + K * c at h
    rw [show 2 * (τ - c) * (1 / (((2 : ℝ) + j) ^ 3)) =
      (τ - c) * (2 * (1 / (((2 : ℝ) + j) ^ 3))) by ring, ← hK, sub_mul]
    linarith only [h]
  let W (j : ℕ) := 1 / (((2 : ℝ) + j) ^ 3)
  have hW : Summable W := by simpa only [W, Nat.cast_ofNat] using cubic_samples_summable 2
  have hS := oneATerm_summable hτ₀
  have hTW := hW.mul_left (2 * (τ - c))
  have hSum := (hS.add hTW).tsum_le_tsum hPoint (oneATerm_summable hc)
  change (∑' j : ℕ, (oneATerm τ j + 2 * (τ - c) * W j)) ≤ (∑' j : ℕ, oneATerm c j) at hSum
  rw [hS.tsum_add hTW, tsum_mul_left, ← oneAStack_eq hτ₀, ← oneAStack_eq hc] at hSum
  have hWE : (∑' j : ℕ, W j) = powerTail 3 2 := by
    simpa only [W, Nat.cast_ofNat] using (powerTail_three_eq 2).symm
  rw [hWE] at hSum
  have hZ := powerTail_shift (q := 3) (by norm_num) 1
  norm_num at hZ
  have hZ' : (1 / 5 : ℝ) ≤ powerTail 3 2 := by
    linarith only [hZ, powerTail_three_gt_six_fifths]
  have hcτ : c ≤ τ := hτ
  have hDrop := mul_le_mul_of_nonneg_left hZ' (mul_nonneg zero_le_two (sub_nonneg.mpr hcτ))
  have hDrop' : (2 / 5) * (τ - c) ≤ 2 * (τ - c) * powerTail 3 2 := by
    convert hDrop using 1 <;> ring
  have hRef : samplingHead (purePeanoA 1 1) c c < 87 / 200 := oneAStack_reference_lt
  change samplingHead (purePeanoA 1 1) τ τ ≤ 87 / 200 - (2 / 5) * (τ - c)
  exact (le_sub_iff_add_le).mpr ((add_le_add_right hDrop' _).trans (hSum.trans hRef.le))

end ACS12.GammaMeasure

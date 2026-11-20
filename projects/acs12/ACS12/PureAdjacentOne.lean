import ACS12.PureAdjacentOneTail
import ACS12.AdjacentCapMass

/-! The literal p = 1 end of the common adjacent source ceiling. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN Set
open scoped BigOperators

theorem oneBStack_le {u : ℝ} (hu : 0 < u) (hu' : u ≤ 7 / 8) :
    samplingTail (purePeanoB 1 u) 0 1 ≤
      u ^ 2 * (1 / (1 + u) + 1011 / 5000 - (59 / 1000) * u) := by
  let f (j : ℕ) := 1 / (((1 : ℝ) + j) ^ 2 * ((1 : ℝ) + j + u))
  let g (j : ℕ) := 1 / (((2 : ℝ) + j) ^ 2 * ((2 : ℝ) + j + u))
  let W (j : ℕ) := 1 / (((2 : ℝ) + j) ^ 3 * ((2 : ℝ) + j + 7 / 8))
  let h (j : ℕ) := 1 / (((2 : ℝ) + j) ^ 3)
  have hS (k : ℕ) (hk : 0 < k) :
      Summable (fun j : ℕ => (1 : ℝ) / (((k : ℝ) + j) ^ 2 * ((k : ℝ) + j + u))) := by
    apply (cubic_samples_summable k).of_nonneg_of_le
    · exact fun _ => by positivity
    · intro j
      have hK : 0 < ((k : ℝ) + j) := add_pos_of_pos_of_nonneg (Nat.cast_pos.mpr hk) (Nat.cast_nonneg _)
      apply div_le_div_of_nonneg_left zero_le_one (by positivity)
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hu.le) (sq_nonneg _)
  have hf : Summable f := by simpa only [f, Nat.cast_one] using hS 1 (by decide)
  have hg : Summable g := by simpa only [g, Nat.cast_ofNat] using hS 2 (by decide)
  have hH : Summable h := by simpa only [h, Nat.cast_ofNat] using cubic_samples_summable 2
  have hW : Summable W := by
    apply hH.of_nonneg_of_le
    · intro j; unfold W; positivity
    · intro j
      unfold W h
      apply div_le_div_of_nonneg_left zero_le_one (by positivity)
      apply le_mul_of_one_le_right (by positivity)
      linarith only [Nat.cast_nonneg (α := ℝ) j]
  have hF : samplingTail (purePeanoB 1 u) 0 1 = u ^ 2 * ∑' j : ℕ, f j := by
    unfold samplingTail
    rw [one_mul, ← tsum_mul_left]
    apply tsum_congr
    intro j
    simp only [Nat.cast_add, Nat.cast_one, mul_one, zero_add]
    rw [purePeanoB_one hu (by positivity)]
    unfold f
    rw [add_comm (j : ℝ) 1]
    ring
  have hEq (j : ℕ) : f (j + 1) = g j := by dsimp only [f, g]; push_cast; ring
  have hZero := hf.tsum_eq_zero_add
  simp_rw [hEq] at hZero
  have hWlower : (59 / 1000 : ℝ) < ∑' j : ℕ, W j := by
    have h0 := hW.sum_le_tsum (Finset.range 8) (fun j _ => by unfold W; positivity)
    exact (by norm_num [W, Finset.sum_range_succ] : (59 / 1000 : ℝ) < ∑ j ∈ Finset.range 8, W j).trans_le h0
  have hCubic : ∑' j : ℕ, h j < 1011 / 5000 := by
    have hHE : (∑' j : ℕ, h j) = powerTail 3 2 := by
      simpa only [h, Nat.cast_ofNat] using (powerTail_three_eq 2).symm
    rw [hHE]
    have h' := powerTail_shift (q := 3) (by norm_num) 1
    norm_num at h'
    linarith only [h', powerTail_three_lt]
  have hPoint (j : ℕ) : g j ≤ h j - u * W j := by
    let r := (2 : ℝ) + j
    have hr : 0 < r := by dsimp only [r]; positivity
    have hr' : 0 < r + u := by positivity
    have hX := div_le_div_of_nonneg_left (by positivity : 0 ≤ u)
      (show 0 < r ^ 3 * (r + u) by positivity)
      (mul_le_mul_of_nonneg_left (add_le_add_right hu' r) (pow_nonneg hr.le _))
    have hE : 1 / (r ^ 2 * (r + u)) = 1 / r ^ 3 - u / (r ^ 3 * (r + u)) := by
      field_simp [hr.ne', hr'.ne']
      ring
    change 1 / (r ^ 2 * (r + u)) ≤ 1 / r ^ 3 - u * (1 / (r ^ 3 * (r + 7 / 8)))
    rw [hE, mul_one_div]
    exact sub_le_sub_left hX _
  have hBound := hg.tsum_le_tsum hPoint (hH.sub (hW.mul_left u))
  rw [hH.tsum_sub (hW.mul_left u), tsum_mul_left] at hBound
  have hW' := mul_le_mul_of_nonneg_left hWlower.le hu.le
  have hB : (∑' j : ℕ, g j) ≤ 1011 / 5000 - (59 / 1000) * u := by
    linarith only [hBound, hCubic, hW']
  rw [hF, hZero]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg u)
  simpa only [f, Nat.cast_zero, add_zero, one_pow, one_mul, ← add_sub_assoc] using
    add_le_add_right hB (1 / (1 + u))

private theorem oneSource_polynomial_lt {u : ℝ} (hu : 0 < u) (hu' : u ≤ 7 / 8) :
    u ^ 2 * (1 / (1 + u) - (2213 / 5000) - (59 / 1000) * u) < 27 / 500 := by
  let f (x : ℝ) := x ^ 2 * (1 / (1 + x) - (2213 / 5000) - (59 / 1000) * x)
  by_cases h : u ≤ 1 / 2
  · let D (x : ℝ) := x * ((2 + x) / (1 + x) ^ 2 - (2213 / 2500) - (177 / 1000) * x)
    have hD (x : ℝ) (hx : 0 ≤ x) : HasDerivAt f (D x) x := by
      have hId := hasDerivAt_id x
      have hx₁ : 0 < 1 + x := by positivity
      have hInv := (hasDerivAt_const x (1 : ℝ)).div (hId.const_add 1) hx₁.ne'
      convert (hId.pow 2).mul ((hInv.sub_const (2213 / 5000)).sub (hId.const_mul (59 / 1000))) using 1
      simp only [D, id_eq, one_mul, mul_one]
      norm_num
      field_simp [hx₁.ne']
      ring
    have hMono : MonotoneOn f (Icc 0 (1 / 2)) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      · exact fun x hx => (hD x hx.1).continuousAt.continuousWithinAt
      · exact fun x hx => (hD x (interior_subset hx).1).differentiableAt.differentiableWithinAt
      · intro x hx
        have hx' : x ∈ Icc (0 : ℝ) (1 / 2) := interior_subset hx
        rw [(hD x hx'.1).deriv]
        have hR : 10 / 9 ≤ (2 + x) / (1 + x) ^ 2 := by
          have hx₀ : 0 ≤ x := hx'.1
          apply (le_div_iff₀ (by positivity : 0 < (1 + x) ^ 2)).mpr
          nlinarith only [mul_nonneg hx₀ (sub_nonneg.mpr hx'.2), hx'.2]
        dsimp only [D]
        exact mul_nonneg hx'.1 (by linarith only [hR, hx'.2])
    have hMax := hMono ⟨hu.le, h⟩ (show (1 / 2 : ℝ) ∈ Icc 0 (1 / 2) by constructor <;> norm_num) h
    exact hMax.trans_lt (by norm_num [f])
  · let v := u - 3 / 5
    have hv : -(1 / 10) ≤ v := by dsimp only [v]; linarith
    have hCub := mul_nonneg (sq_nonneg v) (show 0 ≤ v + 1 / 10 by linarith)
    have hFour := pow_nonneg (sq_nonneg v) 2
    have hSq := sq_nonneg (v - 154 / 5675)
    have hPoly : 0 < (27 / 500) * (1 + u) -
        u ^ 2 * (1 - ((2213 / 5000) + (59 / 1000) * u) * (1 + u)) := by
      have hE : u = v + 3 / 5 := by dsimp only [v]; ring
      rw [hE]
      nlinarith only [hCub, hFour, hSq]
    apply (lt_of_mul_lt_mul_right _ (by positivity : 0 ≤ 1 + u))
    have hE : u ^ 2 * (1 / (1 + u) - 2213 / 5000 - 59 / 1000 * u) * (1 + u) =
        u ^ 2 * (1 - (2213 / 5000 + (59 / 1000) * u) * (1 + u)) := by
      field_simp [(show 1 + u ≠ 0 by positivity)]
      ring
    rw [hE]
    linarith only [hPoly]

theorem pureAdjacentCap_one_neg {L u : ℝ} (hL : 0 < L) (hu : 0 < u) (hu' : u ≤ 7 / 8)
    (hCap : adjacentCap 1 u ≤ u) :
    adjacentDiagonal 1 L 0 u (adjacentCap 1 u) < -(7 / 40) := by
  let m := adjacentCap 1 u
  let τ := m / u
  have hu₁ := hu'.trans_lt (by norm_num : (7 / 8 : ℝ) < 1)
  have hm := adjacentCap_pos (by norm_num : (1 : ℝ) ≤ 9 / 5) hu
  have hτ : τ = 146 / 175 + (2304 / 8575) * u ^ 2 := by
    dsimp only [τ, m, adjacentCap]
    rw [mul_div_cancel_left₀ _ hu.ne']
    ring
  have hτ₀ : 146 / 175 ≤ τ := by rw [hτ]; exact le_add_of_nonneg_right (by positivity)
  have hτ₁ : τ ≤ 1 := (div_le_one hu).mpr hCap
  have hA := oneAStack_le_reference_drop hτ₀ hτ₁
  have hB := oneBStack_le hu hu'
  have hPoly := oneSource_polynomial_lt hu hu'
  have hEq := pureAdjacent_normalized (p := 1) le_rfl (by norm_num) hL hu hm
  simp only [sub_self, Real.rpow_zero, one_mul] at hEq
  change adjacentDiagonal 1 L 0 u m =
    samplingHead (purePeanoA 1 1) τ τ + samplingTail (purePeanoB 1 u) 0 1 + 1 - (1 + 1) * τ at hEq
  rw [hτ] at hA hEq
  nlinarith only [hEq, hA, hB, hPoly, sq_nonneg u]

end ACS12.GammaMeasure

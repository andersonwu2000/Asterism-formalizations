import ACS12.QuarticRegularMoments
import Mathlib.Analysis.Convex.Jensen

/-! The finite regular rank moments after removing the two nearest neighbors. -/
namespace ACS12.NativeCells

open Finset Set

noncomputable section

def quarticFarRanks (n : ℕ) [NeZero n] : Finset (Fin n) :=
  ((univ.erase (0 : Fin n)).erase 1).erase (-1)

def quarticRegularGap {n : ℕ} (i : Fin n) : ℝ :=
  Real.log (Real.sin (Real.pi * (i : ℝ) / (n : ℝ)) / Real.sin (Real.pi / (n : ℝ)))

private theorem first_rank_nat {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    ((1 : Fin n) : ℕ) = 1 :=
  (Fin.val_one' n).trans (Nat.mod_eq_of_lt (by omega))

private theorem last_rank_nat {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    ((-1 : Fin n) : ℕ) = n - 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp

theorem rank_sine_pos {n : ℕ} [NeZero n] {i : Fin n} (hi : i ≠ 0) :
    0 < Real.sin (Real.pi * (i : ℝ) / (n : ℝ)) := by
  have hN : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hi0 : 0 < (i : ℝ) := by
    exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero (fun h => hi (Fin.ext h)))
  have hiN : (i : ℝ) < (n : ℝ) := Nat.cast_lt.mpr i.isLt
  exact Real.sin_pos_of_pos_of_lt_pi (by positivity)
    ((div_lt_iff₀ hN).mpr (mul_lt_mul_of_pos_left hiN Real.pi_pos))

theorem nearest_sine_pos {n : ℕ} (hn : 2 ≤ n) : 0 < Real.sin (Real.pi / (n : ℝ)) := by
  have hN : (1 : ℝ) < (n : ℝ) := Nat.one_lt_cast.mpr (by omega)
  exact Real.sin_pos_of_pos_of_lt_pi (by positivity)
    ((div_lt_iff₀ (zero_lt_one.trans hN)).mpr (by nlinarith [Real.pi_pos]))

theorem exp_neg_regular_gap {n : ℕ} [NeZero n] (hn : 2 ≤ n) {i : Fin n} (hi : i ≠ 0) :
    Real.exp (-quarticRegularGap i) =
      Real.sin (Real.pi / (n : ℝ)) / Real.sin (Real.pi * (i : ℝ) / (n : ℝ)) := by
  rw [quarticRegularGap, Real.exp_neg,
    Real.exp_log (div_pos (rank_sine_pos hi) (nearest_sine_pos hn)), inv_div]

theorem nearest_sines {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    Real.sin (Real.pi * ((1 : Fin n) : ℝ) / (n : ℝ)) = Real.sin (Real.pi / (n : ℝ)) ∧
    Real.sin (Real.pi * ((-1 : Fin n) : ℝ) / (n : ℝ)) = Real.sin (Real.pi / (n : ℝ)) := by
  have hN : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h1 : ((1 : Fin n) : ℝ) = 1 := by exact_mod_cast first_rank_nat hn
  have hM : ((-1 : Fin n) : ℝ) = (n : ℝ) - 1 := by
    change (((-1 : Fin n) : ℕ) : ℝ) = (n : ℝ) - 1
    rw [last_rank_nat hn, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  constructor
  · rw [h1, mul_one]
  · rw [hM, show Real.pi * ((n : ℝ) - 1) / (n : ℝ) = Real.pi - Real.pi / (n : ℝ) by
      field_simp [hN], Real.sin_pi_sub]

private theorem regular_rank_full_sum {n k : ℕ} [NeZero n] (hn : 2 ≤ n) (hk : 0 < k) :
    ∑ i ∈ (univ : Finset (Fin n)).erase 0, (Real.exp (-quarticRegularGap i)) ^ k =
      Real.sin (Real.pi / (n : ℝ)) ^ k * analyticRow (k : ℝ) (n : ℝ) := by
  rw [analyticRow_integer hn (Nat.cast_pos.mpr hk), mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [exp_neg_regular_gap hn (mem_erase.mp hi).1, ACS12.angularCost,
    Real.rpow_natCast, div_pow, mul_one_div]

private theorem regular_rank_far_sum {n k : ℕ} [NeZero n] (hn : 5 ≤ n) (hk : 0 < k) :
    (∑ i ∈ quarticFarRanks n, (Real.exp (-quarticRegularGap i)) ^ k) + 2 =
      Real.sin (Real.pi / (n : ℝ)) ^ k * analyticRow (k : ℝ) (n : ℝ) := by
  have hN : 2 ≤ n := by omega
  have h1 := first_rank_nat hN
  have hM := last_rank_nat hN
  have h10 : (1 : Fin n) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero] at hv
    omega
  have hM0 : (-1 : Fin n) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero] at hv
    omega
  have hM1 : (-1 : Fin n) ≠ 1 := by
    intro h
    have hv := congrArg Fin.val h
    omega
  let w (i : Fin n) := (Real.exp (-quarticRegularGap i)) ^ k
  let T : Finset (Fin n) := univ.erase 0
  have hmem1 : (1 : Fin n) ∈ T := mem_erase.mpr ⟨h10, mem_univ _⟩
  have hmemM : (-1 : Fin n) ∈ T.erase 1 :=
    mem_erase.mpr ⟨hM1, mem_erase.mpr ⟨hM0, mem_univ _⟩⟩
  obtain ⟨hs1, hsM⟩ := nearest_sines hN
  have hW1 : w 1 = 1 := by
    unfold w
    rw [exp_neg_regular_gap hN h10, hs1, div_self (nearest_sine_pos hN).ne', one_pow]
  have hWM : w (-1) = 1 := by
    unfold w
    rw [exp_neg_regular_gap hN hM0, hsM, div_self (nearest_sine_pos hN).ne', one_pow]
  change (∑ i ∈ (T.erase 1).erase (-1), w i) + 2 = _
  rw [← regular_rank_full_sum hN hk]
  change (∑ i ∈ (T.erase 1).erase (-1), w i) + 2 = ∑ i ∈ T, w i
  calc
    _ = ((∑ i ∈ (T.erase 1).erase (-1), w i) + w (-1)) + w 1 := by rw [hWM, hW1]; ring
    _ = _ := by rw [sum_erase_add _ _ hmemM, sum_erase_add _ _ hmem1]

/-- The second and fourth moments of the far ranks, with the same half weights
as the full regular row. -/
theorem quarticRegular_moments {n : ℕ} [NeZero n] (hn : 5 ≤ n) :
    (∑ i ∈ quarticFarRanks n, (Real.exp (-quarticRegularGap i)) ^ 2) / 2 ≤ 13 / 20 ∧
    (∑ i ∈ quarticFarRanks n, (Real.exp (-quarticRegularGap i)) ^ 4) / 2 ≤ 3 / 20 := by
  have hN : (1 : ℝ) < (n : ℝ) := Nat.one_lt_cast.mpr (by omega)
  have hN5 : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h₂ := regular_rank_far_sum hn (by decide : 0 < (2 : ℕ))
  have h₄ := regular_rank_far_sum hn (by decide : 0 < (4 : ℕ))
  simp only [Nat.cast_ofNat, analyticRow_two_eq hN] at h₂
  simp only [Nat.cast_ofNat, analyticRow_four_eq hN] at h₄
  exact ⟨by linarith only [h₂, quartic_regular_second_bound hN5],
    by linarith only [h₄, quartic_regular_fourth_bound hN5]⟩

/-- A far rank has at least a quarter unit of logarithmic separation from a
nearest rank. -/
theorem quarticRegularGap_lower {n : ℕ} [NeZero n] (hn : 5 ≤ n) {i : Fin n}
    (hi : i ∈ quarticFarRanks n) : (1 / 4 : ℝ) ≤ quarticRegularGap i := by
  have hN : 2 ≤ n := by omega
  have hiM := (mem_erase.mp hi).1
  have hi1 := (mem_erase.mp (mem_erase.mp hi).2).1
  have hi0 := (mem_erase.mp (mem_erase.mp (mem_erase.mp hi).2).2).1
  have hiLo : 2 ≤ i.val := by
    have h0 : i.val ≠ 0 := fun h => hi0 (Fin.ext (h.trans (Fin.val_zero n).symm))
    have h1 : i.val ≠ 1 := fun h => hi1 (Fin.ext (h.trans (first_rank_nat hN).symm))
    omega
  have hiHi : i.val ≤ n - 2 := by
    have hM : i.val ≠ n - 1 := fun h => hiM (Fin.ext (h.trans (last_rank_nat hN).symm))
    have h := i.isLt
    omega
  have hN0 : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hN5 : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hiLo' : (2 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hiLo
  have hiHi' : (i : ℝ) ≤ (n : ℝ) - 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ← Nat.cast_sub hN]
    exact_mod_cast hiHi
  let t := Real.pi / (n : ℝ)
  let a := Real.pi * (i : ℝ) / (n : ℝ)
  have ht0 : 0 < t := by dsimp [t]; positivity
  have ht5 : t ≤ Real.pi / 5 := by dsimp [t]; gcongr
  have htPi : 2 * t ≤ Real.pi := by linarith [Real.pi_pos]
  have ha_eq : a = t * (i : ℝ) := by dsimp [a, t]; ring
  have haL : 2 * t ≤ a := by rw [ha_eq, mul_comm 2]; gcongr
  have haU : a ≤ Real.pi - 2 * t := by
    calc
      a ≤ t * ((n : ℝ) - 2) := by rw [ha_eq]; gcongr
      _ = Real.pi - 2 * t := by
        dsimp [t]
        field_simp [hN0.ne']
  have hsin : Real.sin (2 * t) ≤ Real.sin a := by
    have hh := strictConcaveOn_sin_Icc.concaveOn.min_le_of_mem_Icc
      (show 2 * t ∈ Icc 0 Real.pi from ⟨by positivity, htPi⟩)
      (show Real.pi - 2 * t ∈ Icc 0 Real.pi from ⟨by linarith, by linarith⟩)
      (show a ∈ Icc (2 * t) (Real.pi - 2 * t) from ⟨haL, haU⟩)
    simpa only [Real.sin_pi_sub, min_self] using hh
  have hCos : 3 / 4 ≤ Real.cos t := by
    have hs : (2 : ℝ) ≤ Real.sqrt 5 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    have h := Real.cos_le_cos_of_nonneg_of_le_pi ht0.le
      (show Real.pi / 5 ≤ Real.pi by linarith [Real.pi_pos]) ht5
    rw [Real.cos_pi_div_five] at h
    linarith
  have htSin : 0 < Real.sin t := nearest_sine_pos hN
  have hquot : (3 / 2 : ℝ) ≤ Real.sin a / Real.sin t := by
    apply (le_div_iff₀ htSin).mpr
    have hMul := mul_le_mul_of_nonneg_left hCos (show 0 ≤ 2 * Real.sin t by positivity)
    rw [Real.sin_two_mul] at hsin
    linarith only [hMul, hsin]
  have hlog : (1 / 4 : ℝ) ≤ Real.log (3 / 2) := by
    have h := Real.one_sub_inv_le_log_of_pos (x := 3 / 2) (by norm_num)
    norm_num at h
    linarith
  exact hlog.trans (Real.log_le_log (by norm_num) hquot)

end

end ACS12.NativeCells

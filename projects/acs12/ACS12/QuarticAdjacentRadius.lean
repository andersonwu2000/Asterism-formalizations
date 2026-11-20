import ACS12.Rank
import ACS12.FiveAngle

/-! The two adjacent ranks give the required radius bound in the unit row. -/
namespace ACS12.Configuration

open Finset

/-- Keep both nearest ranks in the regular comparison to the normalized
physical row. Each has mass-root weight at least the minimum mass. -/
theorem quartic_adjacent_radius {n : ℕ} [NeZero n] {p : ℝ} (F : Configuration n p)
    (hn : 5 ≤ n) (hp : 0 < p) {q : ℝ} (hq : 0 < q) (hMin : ∀ j, q ≤ F.mass j)
    (hLevel : 2 * F.coefficient * F.radius ^ 2 = 1) :
    (1 / (2 * F.radius) ^ 2) * (2 * q) ^ (2 / p) ≤ Real.sin (Real.pi / (n : ℝ)) ^ 2 := by
  have hN : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hN₁ : (1 : ℝ) < (n : ℝ) := Nat.one_lt_cast.mpr (by omega)
  have hp₁ : 0 < p + 1 := by linarith
  have hR : 0 < 2 * F.radius := mul_pos zero_lt_two F.radius_pos
  let D := 2 * F.radius * Real.sin (Real.pi / (n : ℝ))
  have hD : 0 < D := by
    unfold D
    apply mul_pos hR
    exact Real.sin_pos_of_pos_of_lt_pi (by positivity)
      ((div_lt_iff₀ hN).mpr (by nlinarith only [mul_pos Real.pi_pos (sub_pos.mpr hN₁)]))
  have hFirst : ((1 : Fin n) : ℕ) = 1 :=
    (Fin.val_one' n).trans (Nat.mod_eq_of_lt (by omega))
  have hLast : ((-1 : Fin n) : ℕ) = n - 1 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp
  have hFirst0 : (1 : Fin n) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero] at hv
    omega
  have hLast0 : (-1 : Fin n) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero] at hv
    omega
  have hDistinct : (1 : Fin n) ≠ -1 := by
    intro h
    have hv := congrArg Fin.val h
    omega
  have hFirstReal : ((1 : Fin n) : ℝ) = 1 := by exact_mod_cast hFirst
  have hLastReal : ((-1 : Fin n) : ℝ) = (n : ℝ) - 1 := by
    change (((-1 : Fin n) : ℕ) : ℝ) = (n : ℝ) - 1
    rw [hLast, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  let A (k : Fin n) := Rank.meanRoot p F.mass ^ (p + 1) /
    (2 * F.radius * Real.sin (Real.pi * (k : ℝ) / (n : ℝ))) ^ p
  have hAFirst : A 1 = Rank.meanRoot p F.mass ^ (p + 1) / D ^ p := by
    simp only [A, D, hFirstReal, mul_one]
  have hALast : A (-1) = Rank.meanRoot p F.mass ^ (p + 1) / D ^ p := by
    unfold A D
    rw [hLastReal, show Real.pi * ((n : ℝ) - 1) / (n : ℝ) = Real.pi - Real.pi / (n : ℝ) by
      field_simp [hN.ne'], Real.sin_pi_sub]
  have hRoot : q ^ (1 / (p + 1)) ≤ Rank.meanRoot p F.mass := by
    unfold Rank.meanRoot
    apply (le_div_iff₀ hN).mpr
    calc
      q ^ (1 / (p + 1)) * (n : ℝ) = ∑ _ : Fin n, q ^ (1 / (p + 1)) := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
      _ ≤ _ := sum_le_sum fun i _ => Real.rpow_le_rpow hq.le (hMin i) (by positivity)
  have hWeight : q ≤ Rank.meanRoot p F.mass ^ (p + 1) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hq.le _) hRoot hp₁.le
    rwa [← Real.rpow_mul hq.le, one_div_mul_cancel hp₁.ne', Real.rpow_one] at h
  have hNonneg (k : Fin n) : 0 ≤ A k := by
    have ht0 : 0 ≤ Real.pi * (k : ℝ) / (n : ℝ) := by positivity
    have htπ : Real.pi * (k : ℝ) / (n : ℝ) ≤ Real.pi := by
      apply (div_le_iff₀ hN).mpr
      exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr k.isLt.le) Real.pi_pos.le
    exact div_nonneg
      (Real.rpow_nonneg ((Real.rpow_nonneg hq.le _).trans hRoot) _)
      (Real.rpow_nonneg (mul_nonneg hR.le (Real.sin_nonneg_of_nonneg_of_le_pi ht0 htπ)) _)
  have hSub : ({1, -1} : Finset (Fin n)) ⊆ univ.erase 0 := by
    intro k hk
    simp only [mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact mem_erase.mpr ⟨hFirst0, mem_univ _⟩
    · exact mem_erase.mpr ⟨hLast0, mem_univ _⟩
  have hPair := sum_le_sum_of_subset_of_nonneg (f := A) hSub fun k _ _ => hNonneg k
  rw [sum_pair hDistinct, hAFirst, hALast] at hPair
  have hRow := Rank.referenceRow_le hp.le F
  rw [hLevel] at hRow
  change (∑ k ∈ (univ : Finset (Fin n)).erase 0, A k) ≤ 1 at hRow
  have hDP : 0 < D ^ p := Real.rpow_pos_of_pos hD _
  have hTerm := div_le_div_of_nonneg_right hWeight hDP.le
  have hUpper : (2 * q) / D ^ p ≤ 1 := by
    rw [two_mul, add_div]
    exact (add_le_add hTerm hTerm).trans (hPair.trans hRow)
  have hPower : 2 * q ≤ D ^ p := by
    simpa using (div_le_iff₀ hDP).mp hUpper
  have hSquare := Real.rpow_le_rpow (show 0 ≤ 2 * q by positivity) hPower
    (show 0 ≤ 2 / p by positivity)
  rw [← Real.rpow_mul hD.le, show p * (2 / p) = 2 by field_simp [hp.ne'], Real.rpow_two] at hSquare
  rw [one_div_mul_eq_div, div_le_iff₀ (sq_pos_of_pos hR)]
  simpa only [D, mul_pow, mul_comm] using hSquare

/-- The exact five-label cap follows from monotonicity of the nearest sine. -/
theorem quartic_adjacent_radius_five {n : ℕ} [NeZero n] {p : ℝ} (F : Configuration n p)
    (hn : 5 ≤ n) (hp : 0 < p) {q : ℝ} (hq : 0 < q) (hMin : ∀ j, q ≤ F.mass j)
    (hLevel : 2 * F.coefficient * F.radius ^ 2 = 1) :
    (1 / (2 * F.radius) ^ 2) * (2 * q) ^ (2 / p) ≤ (5 - Real.sqrt 5) / 8 := by
  have hN : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ht0 : 0 ≤ Real.pi / (n : ℝ) := by positivity
  have ht5 : Real.pi / (n : ℝ) ≤ Real.pi / 5 := by gcongr
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi / 2) ≤ Real.pi / (n : ℝ) by linarith [Real.pi_pos])
    (show Real.pi / 5 ≤ Real.pi / 2 by linarith [Real.pi_pos]) ht5
  rw [← five_sin_sq]
  exact (F.quartic_adjacent_radius hn hp hq hMin hLevel).trans
    (pow_le_pow_left₀ (Real.sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith [Real.pi_pos])) hs 2)

end ACS12.Configuration

import ACS12.QuarticAdjacentRadius
import ACS12.QuarticBarycenterPrices
import ACS12.QuarticCountTariff
import ACS12.QuarticCountTransfer
import ACS12.HighDirectRowRadius
import ACS12.HighPhysicalReweightedMoment

/-! The original physical row and the two-sided current force mass total above four. -/
namespace ACS12.Configuration

open Finset HighCurrent Pressure
set_option backward.isDefEq.respectTransparency false

private theorem quartic_count_reweighted_radius {p U x W : ℝ}
    (hp : 0 < p) (hU : 1 ≤ U) (hU3 : U ≤ 3) (hx : 0 ≤ x)
    (hW : W ≤ U ^ (4 / p))
    (hRow : 2 * x ≤ (U + 1) / (1 + 3 * U / 4) ^ (1 + 2 / p)) :
    x ^ 2 * W ≤ 64 / 169 := by
  let T := 1 + 3 * U / 4
  have hU0 : 0 < U := by linarith
  have hT : 0 < T := by unfold T; positivity
  have hUT : U ≤ T := by unfold T; linarith
  have hPow := Real.rpow_le_rpow hU0.le hUT (show 0 ≤ 2 / p by positivity)
  have hX : x * T ^ (2 / p) ≤ 8 / 13 := by
    have hPaid := (le_div_iff₀ (Real.rpow_pos_of_pos hT (1 + 2 / p))).mp hRow
    change 2 * x * T ^ (1 + 2 / p) ≤ U + 1 at hPaid
    rw [Real.rpow_add hT, Real.rpow_one] at hPaid
    apply (mul_le_mul_iff_left₀ (show 0 < 2 * T by positivity)).mp
    calc
      x * T ^ (2 / p) * (2 * T) = 2 * x * (T * T ^ (2 / p)) := by ring
      _ ≤ U + 1 := hPaid
      _ ≤ (8 / 13) * (2 * T) := by unfold T; linarith
  have hXU := (mul_le_mul_of_nonneg_left hPow hx).trans hX
  have hSq := pow_le_pow_left₀ (show 0 ≤ x * U ^ (2 / p) by positivity) hXU 2
  rw [mul_pow, ← Real.rpow_mul_natCast hU0.le,
    show (2 / p) * (2 : ℕ) = 4 / p by push_cast; ring] at hSq
  exact (mul_le_mul_of_nonneg_left hW (sq_nonneg x)).trans
    (by norm_num at hSq ⊢; exact hSq)

/-- With exponent at least four, the total mass strictly exceeds four times
the maximum label mass. The current bounds use one maximum and one minimum
of the original configuration. -/
theorem quartic_massTotal_div_mass_gt_four {n : ℕ} {p : ℝ} (F : Configuration n p)
    (hn : 5 ≤ n) (hp : 4 ≤ p) (o : Fin n) (hMax : ∀ j, F.mass j ≤ F.mass o) :
    4 < massTotal F.mass / F.mass o := by
  have hn₂ : 2 ≤ n := by omega
  have hp₀ : 0 < p := by linarith
  let G := F.radialUnitSource hn₂ o
  let M := massTotal G.mass
  let U := M - 1
  let x := 1 / (2 * G.radius) ^ 2
  let oRank := G.currentOrder.symm o
  let W := G.currentReweightedTotal oRank
  let k := x ^ 2 * W
  let r := 4 / p
  have hMOrig : M = massTotal F.mass / F.mass o := by
    dsimp [M, G, massTotal]
    simp_rw [F.radialUnitSource_mass]
    rw [← sum_div]
  rw [← hMOrig]
  by_contra! hM4
  have hM2 : 2 ≤ M := F.radialUnitSource_totalMass_ge_two hn₂ o
  have hU1 : 1 ≤ U := by unfold U; linarith
  have hU3 : U ≤ 3 := by unfold U; linarith
  have hU0 : 0 < U := by linarith
  have hx : 0 < x := one_div_pos.mpr (sq_pos_of_pos (mul_pos zero_lt_two G.radius_pos))
  have hRoot : G.mass o = 1 := F.radialUnitSource_root hn₂ o
  obtain ⟨i, _, hi⟩ := (univ : Finset (Fin n)).exists_min_image G.mass
    ⟨⟨0, by omega⟩, mem_univ _⟩
  let q := G.mass i
  let z := x * (2 * q) ^ (2 / p)
  let iRank := G.currentOrder.symm i
  have hMin (j : Fin n) : q ≤ G.mass j := hi j (mem_univ _)
  have hq : 0 < q := G.mass_pos i
  have hqU : q ≤ U / 4 := by
    have hSum := sum_le_sum (fun j (_ : j ∈ univ.erase o) => hMin j)
    rw [sum_const, nsmul_eq_mul, sum_erase_eq_sub (mem_univ o), hRoot] at hSum
    have hCard : (4 : ℝ) ≤ ((univ.erase o).card : ℝ) := by
      exact_mod_cast (show 4 ≤ (univ.erase o).card by simp; omega)
    have hScale := mul_le_mul_of_nonneg_right hCard hq.le
    change ((univ.erase o).card : ℝ) * q ≤ U at hSum
    linarith only [hSum, hScale]
  have hq₃₄ : q ≤ 3 / 4 := by linarith
  have hW : W ≤ U ^ (4 / p) := F.radialUnitSource_reweightedTotal_holder hn₂ hp o
  have hW0 : 0 ≤ W := sum_nonneg fun j hj => reweightedMass_nonneg (G.mass_pos _).le
    (G.currentChord_pos (mem_erase.mp hj).1).le
  have hRow : 2 * x ≤ (U + 1) / (1 + 3 * U / 4) ^ (1 + 2 / p) := by
    have h := F.radialUnitSource_row_moment_radius hn₂ hp₀ o i
    change 2 * x ≤ M / (M - q) ^ (1 + 2 / p) at h
    have hT0 : 0 < 1 + 3 * U / 4 := by positivity
    have hT : 1 + 3 * U / 4 ≤ M - q := by unfold U at hqU ⊢; linarith
    have hPow := Real.rpow_le_rpow hT0.le hT (show 0 ≤ 1 + 2 / p by positivity)
    rw [show U + 1 = M by unfold U; ring]
    exact h.trans (div_le_div_of_nonneg_left (show 0 ≤ M by linarith)
      (Real.rpow_pos_of_pos hT0 _) hPow)
  have hk₀ : 0 ≤ k := mul_nonneg (sq_nonneg x) hW0
  have hkU : k ≤ 64 / 169 := quartic_count_reweighted_radius hp₀ hU1 hU3 hx.le hW hRow
  have hr : r ∈ Set.Icc 0 1 := ⟨by unfold r; positivity, (div_le_one hp₀).mpr hp⟩
  have hLevel : 2 * G.coefficient * G.radius ^ 2 = 1 := by
    rw [← G.radial_row o]
    exact F.radialUnitSource_radial hn₂ hp₀ o o
  letI : NeZero n := ⟨by omega⟩
  have hzFive : z ≤ (5 - Real.sqrt 5) / 8 :=
    G.quartic_adjacent_radius_five hn hp₀ hq hMin hLevel
  have hzU : z ≤ 691 / 2000 := hzFive.trans (by linarith only [sqrt_five_guards.1])
  have hz : z ∈ Set.Icc 0 (691 / 2000) :=
    ⟨mul_nonneg hx.le (Real.rpow_nonneg (by positivity [hq]) _), hzU⟩
  have hqTwo : 0 < 2 * q := mul_pos zero_lt_two hq
  have hqRatio : 0 < q / (3 / 4) := div_pos hq (by norm_num)
  have hW3 : W ≤ (3 : ℝ) ^ r := hW.trans (Real.rpow_le_rpow hU0.le hU3 hr.1)
  have hzSq : z ^ 2 = x ^ 2 * (2 * q) ^ r := by
    unfold z r
    rw [mul_pow, ← Real.rpow_mul_natCast hqTwo.le]
    congr 2
    push_cast
    ring
  have hCorr : (q / (3 / 4)) ^ r * k ≤ (2 : ℝ) ^ r * z ^ 2 := by
    calc
      _ ≤ (q / (3 / 4)) ^ r * (x ^ 2 * (3 : ℝ) ^ r) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hW3 (sq_nonneg x))
          (Real.rpow_nonneg hqRatio.le _)
      _ = x ^ 2 * ((q / (3 / 4)) ^ r * (3 : ℝ) ^ r) := by ring
      _ = x ^ 2 * (4 * q) ^ r := by
        rw [← Real.mul_rpow hqRatio.le (by norm_num : (0 : ℝ) ≤ 3)]
        congr 2
        ring
      _ = (2 : ℝ) ^ r * z ^ 2 := by
        rw [hzSq, mul_left_comm, ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hqTwo.le]
        congr 2
        ring
  have hH : 0 < 1 - k := by linarith
  obtain ⟨β, hβ, hId, hHarm, hJ⟩ := F.radialUnitSource_quartic_barycenter hn₂ hp o hH
  have hHarm' := hHarm.trans (mul_le_of_le_one_right (hx.trans hβ).le
    (show (massTotal G.mass - 2) / 2 ≤ 1 by change (M - 2) / 2 ≤ 1; linarith))
  have hLower := quarticBarycenter_count_lower hx.le hβ hH hId hHarm' hJ
  have hMass : G.currentMasses iRank = q := by
    simp only [currentMasses, Function.comp_apply, iRank, Equiv.apply_symm_apply, q]
  have hMinimum (j : Fin n) : G.currentMasses iRank ≤ G.currentMasses j := by
    rw [hMass]
    exact hMin _
  have hUpper := F.radialUnitSource_quartic_count_upper hn₂ hp o hMax iRank (fun j => hMinimum j)
    (by
      change x * (2 * G.currentMasses iRank) ^ (2 / p) ≤ 691 / 2000
      rw [hMass]
      exact hzU)
  dsimp only at hUpper
  rw [hMass] at hUpper
  change 2 * G.commonCurrent ≤ q * (2 * q) ^ (-(1 / p)) * Real.sqrt (1 - z) +
    (1 / 16 - 5 * z ^ 2 / 64) at hUpper
  have hExp : -(1 / p) = -(r / 4) := by unfold r; ring
  rw [hExp] at hUpper
  exact quarticCount_transfer hr hz ⟨hk₀, hkU⟩ hq hq₃₄ hCorr hLower hUpper

end ACS12.Configuration

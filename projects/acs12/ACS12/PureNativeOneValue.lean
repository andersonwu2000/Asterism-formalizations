import ACS12.PureNativeExponent

/-! The exact p = 1 native function and its directed moment lower. -/

namespace ACS12.GammaMeasure

open Set

theorem pureZ_one_eq : pureZ 1 = Real.pi ^ 2 / 6 := by
  have h := hasSum_zeta_two.tsum_eq
  have hE : (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) = fun n : ℕ => (n : ℝ) ^ (-2 : ℝ) := by
    funext n
    rw [Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_two, one_div]
  rw [hE] at h
  have hS := (Real.summable_nat_rpow (p := (-2 : ℝ))).mpr (by norm_num)
  have hT := hS.tsum_eq_zero_add
  simp only [Nat.cast_zero, Real.zero_rpow (by norm_num : (-2 : ℝ) ≠ 0), zero_add] at hT
  have hPow : pureZ 1 = (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) := by
    simp only [pureZ, powerTail, one_mul, Nat.cast_one, Nat.cast_add, add_comm]
    norm_num
  rw [hPow, ← hT, h]

theorem pureZ_one_gt : (16449 / 10000 : ℝ) < pureZ 1 := by
  rw [pureZ_one_eq]
  have hPi := pow_lt_pow_left₀ Real.pi_gt_d6 (by norm_num : (0 : ℝ) ≤ 3.141592) (by decide : 2 ≠ 0)
  linarith only [hPi]

theorem pureRight_one_native_mono : MonotoneOn (fun u => pureRight 1 u u) (Ioc 0 1) := by
  let f (u : ℝ) := (37 * u ^ 2 + 7 * u - 12) / (25 * u * (1 + u) ^ 2)
  let d (u : ℝ) := (-37 * u ^ 3 + 23 * u ^ 2 + 36 * u + 12) / (25 * u ^ 2 * (1 + u) ^ 3)
  have hD (u : ℝ) (hu : 0 < u) : HasDerivAt f (d u) u := by
    have h := hasDerivAt_id u
    have hN := (((h.pow 2).const_mul 37).add (h.const_mul 7)).sub_const 12
    have hQ := (h.const_mul 25).mul ((h.const_add 1).pow 2)
    convert hN.div hQ (show 25 * id u * (1 + id u) ^ 2 ≠ 0 by dsimp; positivity) using 1
    norm_num [d, id_eq, Pi.pow_apply]
    field_simp [hu.ne', (show 0 < 1 + u by positivity).ne']
    ring
  have hM : MonotoneOn f (Ioc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioc _ _)
    · exact fun u hu => (hD u hu.1).continuousAt.continuousWithinAt
    · exact fun u hu => (hD u (interior_subset hu).1).differentiableAt.differentiableWithinAt
    · intro u hu
      have hu' : u ∈ Ioc (0 : ℝ) 1 := interior_subset hu
      rw [(hD u hu'.1).deriv]
      unfold d
      have h₁ := mul_le_mul_of_nonneg_right hu'.2 (sq_nonneg u)
      have h₂ := mul_le_mul_of_nonneg_right hu'.2 hu'.1.le
      have hu₀ : 0 < u := hu'.1
      exact div_nonneg (by nlinarith only [h₁, h₂, hu₀.le]) (by positivity)
  intro x hx y hy hxy
  change pureRight 1 x x ≤ pureRight 1 y y
  rw [pureRight_one_at_u hx.1, pureRight_one_at_u hy.1]
  exact hM hx hy hxy

theorem pureNativeBand_one_mono : MonotoneOn (fun u => pureNativeBand u 1) (Icc (1 / 2) (7 / 8)) := by
  intro x hx y hy hxy
  have hx₀ := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hx.1
  have hy₀ := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hy.1
  have hX : x ∈ Ioc (0 : ℝ) 1 := ⟨hx₀, hx.2.trans (by norm_num)⟩
  have hY : y ∈ Ioc (0 : ℝ) 1 := ⟨hy₀, hy.2.trans (by norm_num)⟩
  have hG := pureRight_one_native_mono hX hY hxy
  have hG₀ : 0 ≤ pureRight 1 x x := by
    rw [pureRight_one_at_u hx₀]
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hx.1 2
    exact div_nonneg (by nlinarith only [h, hx.1]) (by positivity)
  have hA : middleA x ≤ middleA y := by
    unfold middleA
    have h := mul_nonneg (sub_nonneg.mpr hxy) (show 0 ≤ 2 - x - y by linarith only [hX.2, hY.2])
    nlinarith only [h]
  have hT : adjacentRatio x 1 ≤ adjacentRatio y 1 := by
    have h := pow_le_pow_left₀ hx₀.le hxy 2
    unfold adjacentRatio
    linarith only [h]
  have hB := mul_le_mul hT hG hG₀ (adjacentRatio_pos (u := y) (p := 1) (by norm_num)).le
  unfold pureNativeBand
  linarith only [hA, hB]

theorem pureNativeBand_one_low_neg {u : ℝ} (hu : 0 < u) (hu' : u ≤ 1 / 2) :
    pureNativeBand u 1 - pureZ 1 < 0 := by
  have hA : middleA u ≤ 9 / 50 := by
    unfold middleA
    have h := mul_nonneg (sub_nonneg.mpr hu') (show 0 ≤ 3 / 2 - u by linarith only [hu'])
    nlinarith only [h]
  have hT : adjacentRatio u 1 ≤ 451 / 500 := by
    unfold adjacentRatio
    have h := pow_le_pow_left₀ hu.le hu' 2
    linarith only [h]
  have hG := pureRight_one_native_mono
    (show u ∈ Ioc (0 : ℝ) 1 from ⟨hu, hu'.trans (by norm_num)⟩)
    (show (1 / 2 : ℝ) ∈ Ioc 0 1 by constructor <;> norm_num) hu'
  change pureRight 1 u u ≤ pureRight 1 (1 / 2) (1 / 2) at hG
  rw [pureRight_one_at_u (by norm_num : (0 : ℝ) < 1 / 2)] at hG
  norm_num at hG
  have h₁ := mul_le_mul_of_nonneg_left hG (adjacentRatio_pos (u := u) (p := 1) (by norm_num)).le
  have h₂ := mul_le_mul_of_nonneg_right hT (by norm_num : (0 : ℝ) ≤ 2 / 75)
  unfold pureNativeBand
  nlinarith only [hA, h₁, h₂, pureZ_one_gt]

end ACS12.GammaMeasure

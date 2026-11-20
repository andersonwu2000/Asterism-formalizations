import ACS12.QuarticPhysicalBarycenter
import ACS12.QuarticCountScalar

/-! The same barycenter yields both the ratio and the physical count current prices. -/
namespace ACS12.HighCurrent

open Set

theorem quarticBarycenter_current {x β D H J : ℝ}
    (hx : 0 ≤ x) (hβ : x < β) (hH : 0 < H) (hId : D * (β + x) = H)
    (hBounds : D * β ^ 2 / Real.sqrt (β - x) ≤ J) :
    0 ≤ J ∧ H ^ 2 * β ≤ J ^ 2 * ((1 - x / β) * (1 + x / β) ^ 2) := by
  have hβ₀ : 0 < β := hx.trans_lt hβ
  have hDx : 0 < β + x := add_pos_of_pos_of_nonneg hβ₀ hx
  have hD : 0 < D := pos_of_mul_pos_left (hId.symm ▸ hH) hDx.le
  have hS := Real.sqrt_pos.mpr (sub_pos.mpr hβ)
  have hJ₀ : 0 ≤ J := (div_pos (mul_pos hD (sq_pos_of_pos hβ₀)) hS).le.trans hBounds
  have hSq := pow_le_pow_left₀ (by positivity : 0 ≤ D * β ^ 2 / Real.sqrt (β - x)) hBounds 2
  rw [div_pow, Real.sq_sqrt (sub_nonneg.mpr hβ.le), div_le_iff₀ (sub_pos.mpr hβ)] at hSq
  refine ⟨hJ₀, ?_⟩
  apply (mul_le_mul_iff_left₀ (pow_pos hβ₀ 3)).mp
  rw [← hId]
  have h := mul_le_mul_of_nonneg_right hSq (sq_nonneg (β + x))
  convert h using 1
  · ring
  · field_simp [hβ₀.ne']

private theorem ratio_denominator_bound {v : ℝ} (hv : 0 ≤ v) :
    (1 - v) * (1 + v) ^ 2 ≤ 32 / 27 := by
  nlinarith only [mul_nonneg (sq_nonneg (v - 1 / 3)) (show 0 ≤ v + 5 / 3 by linarith)]

theorem quarticBarycenter_ratio_mean {x β D H J : ℝ}
    (hx : 0 ≤ x) (hβ : x < β) (hH : 56 / 81 ≤ H) (hId : D * (β + x) = H)
    (hBounds : D * β ^ 2 / Real.sqrt (β - x) ≤ J) (hJ : J < 629 / 2000) :
    β < 1 / 4 := by
  have hH₀ : 0 < H := by linarith only [hH]
  have hβ₀ := hx.trans_lt hβ
  have hV := quarticBarycenter_current hx hβ hH₀ hId hBounds
  have hDen := ratio_denominator_bound (div_nonneg hx hβ₀.le)
  have hSqJ := pow_lt_pow_left₀ hJ hV.1 (by decide : (2 : ℕ) ≠ 0)
  have hSqH := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 56 / 81) hH 2
  by_contra! hBad
  have hLo := mul_le_mul hSqH hBad (by norm_num : (0 : ℝ) ≤ 1 / 4) (sq_nonneg H)
  have hHi := mul_le_mul_of_nonneg_left hDen (sq_nonneg J)
  nlinarith only [hV.2, hSqJ, hLo, hHi]

private theorem count_denominator_bound {v : ℝ} (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1) :
    (1 - v) ^ 2 * (1 + v) ^ 5 ≤ (4 / 7 : ℝ) ^ 2 * (10 / 7 : ℝ) ^ 5 := by
  let f (v : ℝ) := (1 - v) ^ 2 * (1 + v) ^ 5
  have hD (v : ℝ) : HasDerivAt f ((1 - v) * (1 + v) ^ 4 * (3 - 7 * v)) v := by
    have h₁ := ((hasDerivAt_id v).const_sub 1).pow 2
    have h₂ := ((hasDerivAt_id v).const_add 1).pow 5
    convert h₁.mul h₂ using 1
    simp only [id_eq, Pi.pow_apply, Nat.reduceSub, Nat.cast_ofNat, mul_one, pow_one]
    ring
  have hM : MonotoneOn f (Icc 0 (3 / 7)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun z _ => (hD z).continuousAt.continuousWithinAt
    · exact fun z _ => (hD z).differentiableAt.differentiableWithinAt
    · intro z hz
      have hz' : z ∈ Icc (0 : ℝ) (3 / 7) := interior_subset hz
      rw [(hD z).deriv]
      exact mul_nonneg (mul_nonneg (by linarith only [hz'.2]) (by positivity)) (by linarith only [hz'.2])
  have hA : AntitoneOn f (Icc (3 / 7) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · exact fun z _ => (hD z).continuousAt.continuousWithinAt
    · exact fun z _ => (hD z).differentiableAt.differentiableWithinAt
    · intro z hz
      have hz' : z ∈ Icc (3 / 7 : ℝ) 1 := interior_subset hz
      rw [(hD z).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by linarith only [hz'.2]) (by positivity))
        (by linarith only [hz'.1])
  have hTop : f v ≤ f (3 / 7) := by
    rcases le_total v (3 / 7) with h | h
    · exact hM ⟨hv₀, h⟩ (by norm_num) h
    · exact hA (by norm_num) ⟨h, hv₁⟩ h
  change f v ≤ _
  simpa only [f, show 1 - (3 / 7 : ℝ) = 4 / 7 by norm_num, show 1 + (3 / 7 : ℝ) = 10 / 7 by norm_num] using hTop

theorem quarticBarycenter_count_lower {x β D H J : ℝ}
    (hx : 0 ≤ x) (hβ : x < β) (hH : 0 < H) (hId : D * (β + x) = H)
    (hHarm : D ≤ β) (hBounds : D * β ^ 2 / Real.sqrt (β - x) ≤ J) :
    quarticCountConstant * H ^ (5 / 4 : ℝ) ≤ J := by
  let v := x / β
  let A := (1 - v) * (1 + v) ^ 2
  let C := (4 / 7 : ℝ) ^ 2 * (10 / 7 : ℝ) ^ 5
  have hβ₀ := hx.trans_lt hβ
  have hv₀ : 0 ≤ v := div_nonneg hx hβ₀.le
  have hv₁ : v < 1 := (div_lt_one hβ₀).mpr hβ
  have hA : 0 ≤ A := by dsimp only [A]; positivity [sub_nonneg.mpr hv₁.le]
  obtain ⟨hJ, hHJ⟩ := quarticBarycenter_current hx hβ hH hId hBounds
  change H ^ 2 * β ≤ J ^ 2 * A at hHJ
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤ H ^ 2 * β) hHJ 2
  have hDen := count_denominator_bound hv₀ hv₁.le
  have hId' : D * (β + x) = H := hId
  have hHβ : H ≤ β ^ 2 * (1 + v) := by
    have hβEq : β ^ 2 * (1 + v) = β * (β + x) := by
      dsimp only [v]
      field_simp [hβ₀.ne']
    rw [← hId', hβEq]
    have h := mul_le_mul_of_nonneg_right hHarm (show 0 ≤ β + x by positivity)
    exact h
  have h₁ := mul_le_mul_of_nonneg_left hHβ (show 0 ≤ H ^ 4 by positivity)
  have h₂ := mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ 1 + v)
  have h₃ := mul_le_mul_of_nonneg_left hDen (show 0 ≤ J ^ 4 by positivity)
  have hJ4 : H ^ 5 ≤ J ^ 4 * C := by
    dsimp only [A] at h₂
    change J ^ 4 * ((1 - v) ^ 2 * (1 + v) ^ 5) ≤ J ^ 4 * C at h₃
    linarith only [h₁, h₂, h₃]
  have hC : 0 < C := by dsimp only [C]; positivity
  have hC₄ : quarticCountConstant ^ 4 * C = 1 := by
    unfold quarticCountConstant
    dsimp only [C]
    rw [mul_pow, show Real.sqrt (7 / 4) ^ 4 = ((Real.sqrt (7 / 4)) ^ 2) ^ 2 by ring,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7 / 4),
      ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 7 / 10)]
    norm_num [Real.rpow_natCast]
  have hPow : (quarticCountConstant * H ^ (5 / 4 : ℝ)) ^ 4 * C = H ^ 5 := by
    rw [mul_pow, ← Real.rpow_mul_natCast hH.le, show (5 / 4 : ℝ) * (4 : ℕ) = 5 by norm_num,
      Real.rpow_ofNat, mul_right_comm, hC₄, one_mul]
  have hUpper := (mul_le_mul_iff_left₀ hC).mp (hPow.trans_le hJ4)
  have hPos : 0 ≤ quarticCountConstant * H ^ (5 / 4 : ℝ) := by
    unfold quarticCountConstant
    positivity
  exact (pow_le_pow_iff_left₀ hPos hJ (by decide : (4 : ℕ) ≠ 0)).mp hUpper

end ACS12.HighCurrent

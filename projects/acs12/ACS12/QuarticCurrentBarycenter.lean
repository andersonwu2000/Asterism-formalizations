import ACS12.HighPhysicalReweight

/-! The maximum-source quartic measure furnishes one mean for both incident currents. -/
namespace ACS12.HighCurrent

open Finset

private theorem barycenter_support {x b z : ℝ} (hb : 0 < b) (hz : 0 < z) :
    (x + b ^ 2) ^ 2 / b + (3 * b ^ 4 + 2 * x * b ^ 2 - x ^ 2) / (2 * b ^ 3) *
      (z ^ 2 - b ^ 2) ≤ (x + z ^ 2) ^ 2 / z := by
  have hDen : 0 < 2 * z * b ^ 3 := by positivity
  apply (mul_le_mul_iff_left₀ hDen).mp
  have hEq :
      ((x + z ^ 2) ^ 2 / z -
        ((x + b ^ 2) ^ 2 / b + (3 * b ^ 4 + 2 * x * b ^ 2 - x ^ 2) / (2 * b ^ 3) *
         (z ^ 2 - b ^ 2))) * (2 * z * b ^ 3) =
      (z - b) ^ 2 * (z * (b ^ 2 - x) ^ 2 + 2 * b ^ 3 * z ^ 2 + 2 * b * x ^ 2) := by
    field_simp [hb.ne', hz.ne']
    ring
  have h₀ : 0 ≤ (z - b) ^ 2 * (z * (b ^ 2 - x) ^ 2 + 2 * b ^ 3 * z ^ 2 + 2 * b * x ^ 2) := by
    positivity
  rw [← hEq, sub_mul, sub_nonneg] at h₀
  exact h₀

/-- Jensen's inequality in the quartic measure weighted by the squared current mark.
The tangent formula treats zero marks by multiplication by their zero weight. -/
theorem quarticCurrent_barycenter {ι : Type*} (s : Finset ι)
    (ν z : ι → ℝ) {x H J : ℝ}
    (hx : 0 ≤ x) (hH : 0 < H)
    (hν : ∀ j ∈ s, 0 ≤ ν j) (hz : ∀ j ∈ s, 0 ≤ z j)
    (hMoment : (∑ j ∈ s, ν j * ((x + z j ^ 2) ^ 2 - x ^ 2)) = H)
    (hJ : (∑ j ∈ s, ν j * (x + z j ^ 2) ^ 2 * z j) ≤ J) :
    ∃ β : ℝ, x < β ∧
      (∑ j ∈ s, ν j * z j ^ 2) * (β + x) = H ∧
      (∑ j ∈ s, ν j * z j ^ 2) ≤ β * (∑ j ∈ s, ν j * z j ^ 2 / (x + z j ^ 2)) ∧
      (∑ j ∈ s, ν j * z j ^ 2) * β ^ 2 / Real.sqrt (β - x) ≤ J := by
  let σ (j : ι) := ν j * z j ^ 2
  let D := ∑ j ∈ s, σ j
  have hσ (j : ι) (hj : j ∈ s) : 0 ≤ σ j := mul_nonneg (hν j hj) (sq_nonneg _)
  have hD : 0 < D := by
    by_contra! hBad
    have hZero : D = 0 := le_antisymm hBad (sum_nonneg hσ)
    have h := (sum_eq_zero_iff_of_nonneg hσ).mp hZero
    have hTerm (j : ι) (hj : j ∈ s) :
        ν j * ((x + z j ^ 2) ^ 2 - x ^ 2) = 0 := by
      rw [show ν j * ((x + z j ^ 2) ^ 2 - x ^ 2) = σ j * (2 * x + z j ^ 2) by
        dsimp [σ]; ring, h j hj, zero_mul]
    rw [sum_congr rfl hTerm, sum_const_zero] at hMoment
    exact hH.ne' hMoment.symm
  let A := ∑ j ∈ s, σ j * z j ^ 2
  have hA : 0 < A := by
    by_contra! hBad
    have hZero : A = 0 := le_antisymm hBad (sum_nonneg fun j hj => mul_nonneg (hσ j hj) (sq_nonneg _))
    have h := (sum_eq_zero_iff_of_nonneg (fun j hj => mul_nonneg (hσ j hj) (sq_nonneg _))).mp hZero
    have hTerm (j : ι) (hj : j ∈ s) : σ j = 0 := by
      rcases mul_eq_zero.mp (h j hj) with hZ | hZ
      · exact hZ
      · dsimp [σ]
        simp [hZ]
    have h := sum_congr rfl hTerm
    rw [sum_const_zero] at h
    exact hD.ne' h
  let β := x + A / D
  let b := Real.sqrt (β - x)
  have hβ : x < β := by
    dsimp [β]
    linarith only [div_pos hA hD]
  have hβ₀ : 0 < β := hx.trans_lt hβ
  have hb : 0 < b := Real.sqrt_pos.mpr (sub_pos.mpr hβ)
  have hb₂ : b ^ 2 = A / D := by
    dsimp only [b, β]
    rw [show x + A / D - x = A / D by ring, Real.sq_sqrt (div_pos hA hD).le]
  have hBalance : D * b ^ 2 = A := by rw [hb₂, mul_div_cancel₀ _ hD.ne']
  have hIdentity : D * (β + x) = H := by
    rw [← hMoment]
    calc
      _ = (2 * x) * D + A := by dsimp only [β]; field_simp [hD.ne']; ring
      _ = _ := by
        dsimp only [D, A]
        rw [mul_sum, ← sum_add_distrib]
        apply sum_congr rfl
        intro j _
        dsimp only [σ]
        ring
  have hCentered : (∑ j ∈ s, σ j * (z j ^ 2 - b ^ 2)) = 0 := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul]
    change A - D * b ^ 2 = 0
    rw [hBalance, sub_self]
  have hPoint (j : ι) (hj : j ∈ s) :
      σ j * ((x + b ^ 2) ^ 2 / b + (3 * b ^ 4 + 2 * x * b ^ 2 - x ^ 2) / (2 * b ^ 3) *
        (z j ^ 2 - b ^ 2)) ≤ ν j * (x + z j ^ 2) ^ 2 * z j := by
    rcases (hz j hj).eq_or_lt with hZero | hPos
    · simp [σ, ← hZero]
    · have h := mul_le_mul_of_nonneg_left (barycenter_support (x := x) hb hPos) (hσ j hj)
      convert h using 1
      dsimp only [σ]
      field_simp [hPos.ne']
  have hLower := sum_le_sum hPoint
  have hLeft :
      (∑ j ∈ s, σ j * ((x + b ^ 2) ^ 2 / b + (3 * b ^ 4 + 2 * x * b ^ 2 - x ^ 2) / (2 * b ^ 3) *
        (z j ^ 2 - b ^ 2))) = D * β ^ 2 / b := by
    rw [show β = x + b ^ 2 by rw [hb₂]]
    simp only [mul_add, show ∀ j : ι, σ j * ((3 * b ^ 4 + 2 * x * b ^ 2 - x ^ 2) /
      (2 * b ^ 3) * (z j ^ 2 - b ^ 2)) =
        (σ j * (z j ^ 2 - b ^ 2)) * ((3 * b ^ 4 + 2 * x * b ^ 2 - x ^ 2) / (2 * b ^ 3))
      from fun j => by ring, sum_add_distrib, ← sum_mul, hCentered, zero_mul, add_zero]
    unfold D
    ring
  rw [hLeft] at hLower
  refine ⟨β, hβ, hIdentity, ?_, hLower.trans hJ⟩
  have hInvPoint (j : ι) (hj : j ∈ s) :
      σ j * (2 * β - (x + z j ^ 2)) ≤ β ^ 2 * (σ j / (x + z j ^ 2)) := by
    rcases (hz j hj).eq_or_lt with hZero | hPos
    · simp [σ, ← hZero]
    · have hy : 0 < x + z j ^ 2 := add_pos_of_nonneg_of_pos hx (sq_pos_of_pos hPos)
      apply (mul_le_mul_iff_left₀ hy).mp
      rw [mul_assoc (β ^ 2), div_mul_cancel₀ _ hy.ne']
      nlinarith only [mul_nonneg (hσ j hj) (sq_nonneg (β - (x + z j ^ 2)))]
  have hInv := sum_le_sum hInvPoint
  have hInvLeft : (∑ j ∈ s, σ j * (2 * β - (x + z j ^ 2))) = β * D := by
    calc
      _ = (∑ j ∈ s, σ j * β) - ∑ j ∈ s, σ j * (z j ^ 2 - b ^ 2) := by
        rw [← sum_sub_distrib]
        apply sum_congr rfl
        intro j _
        rw [show β = x + b ^ 2 by rw [hb₂]]
        ring
      _ = _ := by rw [hCentered, sub_zero, ← sum_mul, mul_comm]
  rw [hInvLeft, ← mul_sum, pow_two, mul_assoc] at hInv
  exact (mul_le_mul_iff_right₀ hβ₀).mp hInv

end ACS12.HighCurrent

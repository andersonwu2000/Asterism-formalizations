import ACS12.PureRightExponent
import ACS12.PureAdjacentCapConvex

/-! Exact native exponent derivatives before subtracting the complete Z moment. -/

namespace ACS12.GammaMeasure

open Set

noncomputable def nativeS (u : ℝ) : ℝ := 13 / 25 + (6 / 25) * u
noncomputable def nativeA (u : ℝ) : ℝ := middleA u / (1 + u)
noncomputable def nativeL (u : ℝ) : ℝ := -Real.log u
noncomputable def nativeT (u : ℝ) : ℝ := Real.log (1 + u)

theorem pureRight_native_eq {p u : ℝ} (hu : 0 < u) :
    pureRight p u u = u ^ (-p) * (p * nativeS u - 1) +
      (1 + u) ^ (-p) * (1 + p * nativeA u) := by
  rw [pureRight_two_powers hu, add_comm u 1]
  have h : middleZ u / u = nativeS u := by
    unfold middleZ middleA nativeS
    field_simp [hu.ne']
    ring
  unfold nativeA
  rw [mul_div_assoc, h]
  ring

noncomputable def pureNativeG1 (u p : ℝ) : ℝ :=
  u ^ (-p) * (nativeS u + (p * nativeS u - 1) * nativeL u) -
    (1 + u) ^ (-p) * ((1 + p * nativeA u) * nativeT u - nativeA u)

noncomputable def pureNativeG2 (u p : ℝ) : ℝ :=
  u ^ (-p) * (2 * nativeS u * nativeL u + (p * nativeS u - 1) * nativeL u ^ 2) +
    (1 + u) ^ (-p) * ((1 + p * nativeA u) * nativeT u ^ 2 - 2 * nativeA u * nativeT u)

noncomputable def pureNativeG3 (u p : ℝ) : ℝ :=
  u ^ (-p) * (3 * nativeS u * nativeL u ^ 2 + (p * nativeS u - 1) * nativeL u ^ 3) +
    (1 + u) ^ (-p) * (3 * nativeA u * nativeT u ^ 2 - (1 + p * nativeA u) * nativeT u ^ 3)

theorem pureNativeG_deriv {u p : ℝ} (hu : 0 < u) :
    HasDerivAt (fun q => pureRight q u u) (pureNativeG1 u p) p := by
  have h := hasDerivAt_id p
  have hU := h.neg.const_rpow hu
  have hY := h.neg.const_rpow (show 0 < 1 + u by positivity)
  have hS := (h.const_mul (nativeS u)).sub_const 1
  have hA := (h.const_mul (nativeA u)).const_add 1
  convert (hU.mul hS).add (hY.mul hA) using 1
  · funext q
    simp only [pureRight_native_eq hu, id_eq, Pi.neg_apply, Pi.add_apply, Pi.mul_apply]
    ring
  · simp only [pureNativeG1, nativeL, nativeT, id_eq, Pi.neg_apply]
    ring

theorem pureNativeG1_deriv {u p : ℝ} (hu : 0 < u) :
    HasDerivAt (pureNativeG1 u) (pureNativeG2 u p) p := by
  have h := hasDerivAt_id p
  have hU := h.neg.const_rpow hu
  have hY := h.neg.const_rpow (show 0 < 1 + u by positivity)
  have hS := (((h.const_mul (nativeS u)).sub_const 1).mul_const (nativeL u)).const_add (nativeS u)
  have hA := (((h.const_mul (nativeA u)).const_add 1).mul_const (nativeT u)).sub_const (nativeA u)
  convert (hU.mul hS).sub (hY.mul hA) using 1
  · funext q
    simp only [pureNativeG1, id_eq, Pi.neg_apply, Pi.sub_apply, Pi.mul_apply]
    ring
  · simp only [pureNativeG2, nativeL, nativeT, id_eq, Pi.neg_apply]
    ring

theorem pureNativeG2_deriv {u p : ℝ} (hu : 0 < u) :
    HasDerivAt (pureNativeG2 u) (pureNativeG3 u p) p := by
  have h := hasDerivAt_id p
  have hU := h.neg.const_rpow hu
  have hY := h.neg.const_rpow (show 0 < 1 + u by positivity)
  have hS := (((h.const_mul (nativeS u)).sub_const 1).mul_const (nativeL u ^ 2)).const_add
    (2 * nativeS u * nativeL u)
  have hA := (((h.const_mul (nativeA u)).const_add 1).mul_const (nativeT u ^ 2)).sub_const
    (2 * nativeA u * nativeT u)
  convert (hU.mul hS).add (hY.mul hA) using 1
  · funext q
    simp only [pureNativeG2, id_eq, Pi.neg_apply, Pi.add_apply, Pi.mul_apply]
    ring
  · simp only [pureNativeG3, nativeL, nativeT, id_eq, Pi.neg_apply]
    ring

theorem pureNativeG1_eq {p u : ℝ} (hu : 0 < u) :
    pureNativeG1 u p = pureRightExponentD p u u :=
  (pureNativeG_deriv hu).unique (pureRight_exponent_deriv hu)

noncomputable def pureNativeBand (u p : ℝ) : ℝ :=
  1 + middleA u * p + adjacentRatio u p * pureRight p u u

noncomputable def pureNativeBandD (u p : ℝ) : ℝ :=
  middleA u + adjacentRatio u p * pureNativeG1 u p - (3 / 20) * pureRight p u u

noncomputable def pureNativeBandDD (u p : ℝ) : ℝ :=
  adjacentRatio u p * pureNativeG2 u p - (3 / 10) * pureNativeG1 u p

theorem adjacentRatio_exponent_deriv (u p : ℝ) :
    HasDerivAt (adjacentRatio u) (-(3 / 20)) p := by
  have h := (((hasDerivAt_id p).const_sub (9 / 5)).const_mul (3 / 20)).const_add
    (5 / 7 + (2304 / 8575) * u ^ 2)
  simpa only [adjacentRatio, mul_neg, mul_one, id_eq] using h

theorem pureNativeBand_deriv {u p : ℝ} (hu : 0 < u) :
    HasDerivAt (pureNativeBand u) (pureNativeBandD u p) p := by
  have h := ((hasDerivAt_id p).const_mul (middleA u)).const_add 1
  convert h.add ((adjacentRatio_exponent_deriv u p).mul (pureNativeG_deriv hu)) using 1
  simp only [pureNativeBandD, id_eq]
  ring

theorem pureNativeBandD_deriv {u p : ℝ} (hu : 0 < u) :
    HasDerivAt (pureNativeBandD u) (pureNativeBandDD u p) p := by
  have h := ((adjacentRatio_exponent_deriv u p).mul (pureNativeG1_deriv hu)).const_add (middleA u)
  convert h.sub ((pureNativeG_deriv hu).const_mul (3 / 20)) using 1
  simp only [pureNativeBandDD]
  ring

theorem pureNativeBandDD_deriv {u p : ℝ} (hu : 0 < u) :
    HasDerivAt (pureNativeBandDD u)
      (adjacentRatio u p * pureNativeG3 u p - (9 / 20) * pureNativeG2 u p) p := by
  have h := (adjacentRatio_exponent_deriv u p).mul (pureNativeG2_deriv hu)
  convert h.sub ((pureNativeG1_deriv hu).const_mul (3 / 10)) using 1
  ring

theorem nativeT_gt_twoA {u : ℝ} (hu : 0 < u) :
    2 * nativeA u < nativeT u := by
  have hY : 0 < 1 + u := by positivity
  have hT := Real.one_sub_inv_le_log_of_pos hY
  have hE : 1 - (1 + u)⁻¹ = u / (1 + u) := by field_simp [hY.ne']; ring
  rw [hE] at hT
  apply lt_of_lt_of_le _ hT
  unfold nativeA middleA
  have h : 2 * ((6 / 25) * u * (2 - u) / (1 + u)) = (12 / 25) * u * (2 - u) / (1 + u) := by ring
  rw [h]
  apply (div_lt_div_iff_of_pos_right hY).mpr
  nlinarith only [hu, sq_nonneg u]

theorem pureNativeBandDD_unshifted_le {p u : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hu : 0 < u) (hu' : u ≤ 1) :
    u ^ (-p) * (nativeS u * (2 * (adjacentRatio u p * nativeL u) - 3 / 10) +
      (p * nativeS u - 1) * nativeL u * (adjacentRatio u p * nativeL u - 3 / 10)) ≤
        pureNativeBandDD u p := by
  let A := nativeA u
  let t := nativeT u
  let τ := adjacentRatio u p
  have hA : 0 ≤ A := div_nonneg (middleA_pos hu hu').le (by positivity)
  have ht : 0 < t := Real.log_pos (by linarith)
  have hT := nativeT_gt_twoA hu
  have hC : 1 ≤ 1 + p * A := le_add_of_nonneg_right (mul_nonneg (zero_le_one.trans hp) hA)
  have h₁ : 0 ≤ (1 + p * A) * t ^ 2 - 2 * A * t := by
    have h' := mul_le_mul_of_nonneg_right hC (sq_nonneg t)
    have h'' := mul_le_mul_of_nonneg_right hT.le ht.le
    nlinarith only [h', h'']
  have h₂ : 0 ≤ (1 + p * A) * t - A := by
    have h' := mul_le_mul_of_nonneg_right hC ht.le
    linarith only [h', hT, hA]
  have hτ := adjacentRatio_pos (u := u) hP
  have hN : 0 ≤ τ * ((1 + p * A) * t ^ 2 - 2 * A * t) + (3 / 10) * ((1 + p * A) * t - A) :=
    add_nonneg (mul_nonneg hτ.le h₁) (mul_nonneg (by norm_num) h₂)
  have hM := mul_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ 1 + u) (-p)) hN
  unfold pureNativeBandDD pureNativeG2 pureNativeG1
  dsimp only [A, t, τ] at hM
  nlinarith only [hM]

end ACS12.GammaMeasure

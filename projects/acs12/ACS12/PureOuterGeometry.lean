import ACS12.PureZetaEnvelope

/-! The finite high-gap scaling bound for the one-source outer corner. -/

namespace ACS12.GammaMeasure

open MeasureTheory Set

theorem high_gap_inv_power_lt {p u : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hu : 7 / 8 ≤ u) :
    u ^ (-p) < 159 / 125 := by
  have hu₀ := (by norm_num : (0 : ℝ) < 7 / 8).trans_le hu
  have hU := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 7 / 8) hu
    (show -p ≤ 0 by linarith)
  have hP' := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 7 / 8)
    (by norm_num : (7 / 8 : ℝ) ≤ 1) (show -(9 / 5 : ℝ) ≤ -p by linarith)
  have hX : (7 / 8 : ℝ) ^ (-(9 / 5 : ℝ)) < 159 / 125 := by
    convert fifth_rpow_upper (k := 9) (b := 7 / 8) (x := 159 / 125)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  exact hU.trans_lt (hP'.trans_lt hX)

private theorem u_negFourFifths_add_le {u : ℝ} (hu : 7 / 8 ≤ u) (hu₁ : u ≤ 1) :
    u ^ (-(4 / 5 : ℝ)) + u ≤ 2 := by
  let f (x : ℝ) := x ^ (-(4 / 5 : ℝ)) + x
  let R (x : ℝ) := x ^ (-(4 / 5 : ℝ))
  have hD (x : ℝ) (hx : 0 < x) :
      HasDerivAt R (-(4 / 5) * x ^ (-(9 / 5 : ℝ))) x := by
    convert Real.hasDerivAt_rpow_const (p := -(4 / 5 : ℝ)) (Or.inl hx.ne') using 1
    norm_num
  have hD₂ (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun x : ℝ => -(4 / 5) * x ^ (-(9 / 5 : ℝ)))
        ((36 / 25) * x ^ (-(14 / 5 : ℝ))) x := by
    convert (Real.hasDerivAt_rpow_const (p := -(9 / 5 : ℝ)) (Or.inl hx.ne')).const_mul
      (-(4 / 5)) using 1
    norm_num
    ring
  have hPos (x : ℝ) (hx : x ∈ Icc (7 / 8 : ℝ) 1) : 0 < x :=
    (by norm_num : (0 : ℝ) < 7 / 8).trans_le hx.1
  have hConvR : ConvexOn ℝ (Icc (7 / 8 : ℝ) 1) R := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (fun x hx => (hD x (hPos x hx)).continuousAt.continuousWithinAt)
      (fun x hx => (hD x (hPos x (interior_subset hx))).hasDerivWithinAt)
      (fun x hx => (hD₂ x (hPos x (interior_subset hx))).hasDerivWithinAt)
    intro x hx
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (hPos x (interior_subset hx)).le _)
  have hConv : ConvexOn ℝ (Icc (7 / 8 : ℝ) 1) f := hConvR.add (convexOn_id (convex_Icc _ _))
  have hA : 0 ≤ (1 - u) / (1 / 8) := div_nonneg (sub_nonneg.mpr hu₁) (by norm_num)
  have hB : 0 ≤ (u - 7 / 8) / (1 / 8) := div_nonneg (sub_nonneg.mpr hu) (by norm_num)
  have h := hConv.2 (show (7 / 8 : ℝ) ∈ Icc (7 / 8) 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Icc (7 / 8) 1 by constructor <;> norm_num) hA hB (by ring)
  simp only [smul_eq_mul, mul_one] at h
  rw [show (1 - u) / (1 / 8) * (7 / 8) + (u - 7 / 8) / (1 / 8) = u by ring] at h
  have hX : (7 / 8 : ℝ) ^ (-(4 / 5 : ℝ)) < 9 / 8 := by
    convert fifth_rpow_upper (k := 4) (b := 7 / 8) (x := 9 / 8)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  have hL : f (7 / 8) ≤ 2 := by dsimp only [f]; linarith
  have hR : f 1 = 2 := by simp [f]; norm_num
  have hM := add_le_add (mul_le_mul_of_nonneg_left hL hA)
    (mul_le_mul_of_nonneg_left hR.le hB)
  change f u ≤ (1 - u) / (1 / 8) * f (7 / 8) + (u - 7 / 8) / (1 / 8) * f 1 at h
  exact h.trans (hM.trans_eq (by ring))

private theorem integral_rpow_trapezoid {p u : ℝ} (hp : 1 ≤ p) (hu : 0 < u) (hu₁ : u < 1) :
    (1 - u ^ (p + 1)) / (p + 1) ≤ (1 - u) * (u ^ p + 1) / 2 := by
  let B (t : ℝ) := ((1 - t) / (1 - u)) * u ^ p + (t - u) / (1 - u)
  have hf : ContinuousOn (fun t : ℝ => t ^ p) (Icc u 1) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (hu.trans_le ht.1).ne')
  have hB : Continuous B := by unfold B; fun_prop
  have hδ := sub_pos.mpr hu₁
  have hConv := (convexOn_rpow hp).2
  have hPt (t : ℝ) (ht : t ∈ Icc u 1) : t ^ p ≤ B t := by
    have hA : 0 ≤ (1 - t) / (1 - u) := div_nonneg (sub_nonneg.mpr ht.2) hδ.le
    have hD : 0 ≤ (t - u) / (1 - u) := div_nonneg (sub_nonneg.mpr ht.1) hδ.le
    have h := hConv (mem_Ici.mpr hu.le) (mem_Ici.mpr zero_le_one) hA hD (by field_simp; ring)
    simp only [smul_eq_mul, Real.one_rpow, mul_one] at h
    have hE : (1 - t) / (1 - u) * u + (t - u) / (1 - u) = t := by
      field_simp [hδ.ne']
      ring
    rwa [hE] at h
  have h := intervalIntegral.integral_mono_on hu₁.le (hf.intervalIntegrable_of_Icc (μ := volume) hu₁.le)
    (hB.intervalIntegrable (μ := volume) _ _) hPt
  have hI : (∫ t in u..1, t ^ p) = (1 - u ^ (p + 1)) / (p + 1) := by
    rw [integral_rpow (Or.inl (by linarith : -1 < p)), Real.one_rpow]
  have hT : (∫ t in u..1, B t) = (1 - u) * (u ^ p + 1) / 2 := by
    let D := (1 - u)⁻¹
    let F (t : ℝ) := (D * (u ^ p - u)) * t + (D * (1 - u ^ p)) * t ^ 2 / 2
    have hD (t : ℝ) : HasDerivAt F (B t) t := by
      have h := (((hasDerivAt_id t).const_mul (D * (u ^ p - u))).add
        ((((hasDerivAt_id t).pow 2).const_mul (D * (1 - u ^ p))).div_const 2))
      convert h using 1
      norm_num [B, id_eq, D, div_eq_mul_inv]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hD t) (hB.intervalIntegrable (μ := volume) _ _)]
    dsimp only [F, D]
    field_simp [hδ.ne']
    ring
  rwa [hI, hT] at h

theorem outer_finite_scaling {p u : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hu : 7 / 8 ≤ u) (hu₁ : u < 1) :
    u ^ 2 * ((u ^ (-(p + 1)) - 1) / (p + 1)) ≤ 1 - u := by
  have hu₀ := (by norm_num : (0 : ℝ) < 7 / 8).trans_le hu
  have hR : u ^ (1 - p) ≤ u ^ (-(4 / 5 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hu₀ hu₁.le (by linarith)
  have hAdd : u ^ (1 - p) + u ≤ 2 := (add_le_add_left hR u).trans (u_negFourFifths_add_le hu hu₁.le)
  have h := mul_le_mul_of_nonneg_left (integral_rpow_trapezoid hp hu₀ hu₁) (Real.rpow_nonneg hu₀.le (1 - p))
  have hA : u ^ (1 - p) * u ^ (p + 1) = u ^ 2 := by
    rw [← Real.rpow_add hu₀, show 1 - p + (p + 1) = 2 by ring, Real.rpow_two]
  have hB : u ^ 2 * u ^ (-(p + 1)) = u ^ (1 - p) := by
    rw [← Real.rpow_two, ← Real.rpow_add hu₀]
    congr 1
    ring
  have hC : u ^ (1 - p) * u ^ p = u := by
    rw [← Real.rpow_add hu₀, show 1 - p + p = 1 by ring, Real.rpow_one]
  rw [← mul_div_assoc, mul_sub, mul_one, hA] at h
  have hE : u ^ (1 - p) * ((1 - u) * (u ^ p + 1) / 2) =
      (1 - u) * (u ^ (1 - p) + u) / 2 := by
    linear_combination ((1 - u) / 2) * hC
  rw [hE] at h
  rw [← mul_div_assoc, mul_sub, mul_one, hB]
  exact h.trans (by
    have hD := mul_le_mul_of_nonneg_left hAdd (sub_nonneg.mpr hu₁.le)
    linarith only [hD])

end ACS12.GammaMeasure

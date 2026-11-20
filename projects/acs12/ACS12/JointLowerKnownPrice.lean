import ACS12.JointLowerRightDerivative

/-! The finite part of the original lower-diagonal third source. -/
namespace ACS12.GammaMeasure

open Set

noncomputable def lowerKnownFinite (p δ : ℝ) : ℝ :=
  (p + 1) * (1 - δ) ^ (-p) - (2 * p + 1) * (1 - δ) ^ (1 - p)

noncomputable def lowerKnownFiniteD1 (p δ : ℝ) : ℝ :=
  (p + 1) * p * (1 - δ) ^ (-p - 1) - (2 * p + 1) * (p - 1) * (1 - δ) ^ (-p)

noncomputable def lowerKnownFiniteD2 (p δ : ℝ) : ℝ :=
  (p + 1) ^ 2 * p * (1 - δ) ^ (-p - 2) - (2 * p + 1) * (p - 1) * p * (1 - δ) ^ (-p - 1)

private theorem oneSub_rpow_deriv (r δ : ℝ) (hδ : δ < 1) :
    HasDerivAt (fun d => (1 - d) ^ r) (-r * (1 - δ) ^ (r - 1)) δ := by
  convert ((hasDerivAt_id δ).const_sub 1).rpow_const (p := r)
    (Or.inl (sub_pos.mpr hδ).ne') using 1
  simp only [id_eq,mul_neg,mul_one]
  ring

theorem lowerKnownFinite_deriv1 (p δ : ℝ) (hδ : δ < 1) :
    HasDerivAt (lowerKnownFinite p) (lowerKnownFiniteD1 p δ) δ := by
  convert ((oneSub_rpow_deriv (-p) δ hδ).const_mul (p + 1)).sub
    ((oneSub_rpow_deriv (1 - p) δ hδ).const_mul (2 * p + 1)) using 1
  simp only [lowerKnownFiniteD1,show 1 - p - 1 = -p by ring]
  ring

theorem lowerKnownFinite_deriv2 (p δ : ℝ) (hδ : δ < 1) :
    HasDerivAt (lowerKnownFiniteD1 p) (lowerKnownFiniteD2 p δ) δ := by
  convert ((oneSub_rpow_deriv (-p - 1) δ hδ).const_mul ((p + 1) * p)).sub
    ((oneSub_rpow_deriv (-p) δ hδ).const_mul ((2 * p + 1) * (p - 1))) using 1
  simp only [lowerKnownFiniteD2,show -p - 1 - 1 = -p - 2 by ring]
  ring

noncomputable def lowerKnownFiniteD3 (p δ : ℝ) : ℝ :=
  (p + 1) ^ 2 * p * (p + 2) * (1 - δ) ^ (-p - 3) -
    (2 * p + 1) * (p - 1) * p * (p + 1) * (1 - δ) ^ (-p - 2)

theorem lowerKnownFinite_deriv3 (p δ : ℝ) (hδ : δ < 1) :
    HasDerivAt (lowerKnownFiniteD2 p) (lowerKnownFiniteD3 p δ) δ := by
  convert ((oneSub_rpow_deriv (-p - 2) δ hδ).const_mul ((p + 1) ^ 2 * p)).sub
    ((oneSub_rpow_deriv (-p - 1) δ hδ).const_mul ((2 * p + 1) * (p - 1) * p)) using 1
  simp only [lowerKnownFiniteD3,show -p - 2 - 1 = -p - 3 by ring,show -p - 1 - 1 = -p - 2 by ring]
  ring

private noncomputable def knownResponse (p u : ℝ) : ℝ :=
  (2 - u⁻¹) ^ (p + 2) * ((p + 1) * (p + 2) / u - (2 * p + 1) * (p - 1))

private theorem knownResponse_mono {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    MonotoneOn (knownResponse p) (Icc (7 / 8) 1) := by
  let A := (p + 1) * (p + 2)
  let B := (2 * p + 1) * (p - 1)
  let a (u : ℝ) := 2 - u⁻¹
  have ha (u : ℝ) (hu : u ∈ Icc (7 / 8) 1) : 0 < a u := by
    unfold a
    apply sub_pos.mpr
    rw [← one_div]
    apply (div_lt_iff₀ ((by norm_num : (0 : ℝ) < 7 / 8).trans_le hu.1)).mpr
    linarith only [hu.1]
  have hA : 0 < A := by have := zero_lt_one.trans_le hp; unfold A; positivity
  have hD (u : ℝ) (hu : u ∈ Icc (7 / 8) 1) :
      HasDerivAt (knownResponse p)
        (a u ^ (p + 1) / u ^ 2 * ((p + 3) * A / u - (p + 2) * B - 2 * A)) u := by
    have hu₀ := (by norm_num : (0 : ℝ) < 7 / 8).trans_le hu.1
    have h₁ := (hasDerivAt_id u).inv hu₀.ne'
    have h₂ := (h₁.const_sub 2).rpow_const (p := p + 2) (Or.inl (ha u hu).ne')
    have h₃ := (h₁.const_mul A).sub_const B
    have hPow : a u ^ (p + 2) = a u ^ (p + 1) * a u := by
      rw [← Real.rpow_add_one (ha u hu).ne']
      congr 1
      ring
    have h := h₂.mul h₃
    convert h using 1
    simp only [id_eq,Pi.inv_apply,show p + 2 - 1 = p + 1 by ring,mul_one,neg_neg]
    change _ = -(-1 / u ^ 2) * (p + 2) * a u ^ (p + 1) * (A * u⁻¹ - B) +
      a u ^ (p + 2) * (A * (-1 / u ^ 2))
    rw [hPow]
    unfold a
    field_simp [hu₀.ne'] <;> ring
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · exact fun u hu => (hD u hu).continuousAt.continuousWithinAt
  · exact fun u hu => (hD u (interior_subset hu)).differentiableAt.differentiableWithinAt
  · intro u hu
    have hu' : u ∈ Icc (7 / 8 : ℝ) 1 := interior_subset hu
    have hu₀ := (by norm_num : (0 : ℝ) < 7 / 8).trans_le hu'.1
    have hLower : (p + 3) * A ≤ (p + 3) * A / u := (le_div_iff₀ hu₀).mpr
      (mul_le_of_le_one_right (by have := zero_lt_one.trans_le hp; positivity) hu'.2)
    have hP' : 0 ≤ (p + 1) * A - (p + 2) * B := by
      have h := mul_nonneg (show 0 ≤ p + 2 by linarith only [hp])
        (show 0 ≤ -p ^ 2 + 3 * p + 2 by
          nlinarith only [mul_nonneg (show 0 ≤ p by linarith only [hp]) (show 0 ≤ 3 - p by linarith only [hP])])
      unfold A B
      nlinarith only [h]
    rw [(hD u hu').deriv]
    exact mul_nonneg (div_nonneg (Real.rpow_nonneg (ha u hu').le _) (sq_nonneg _))
      (by linarith only [hLower,hP'])

private theorem knownResponse_far_gt {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    423 / 100 < knownResponse p (7 / 8) := by
  let t := p - 1
  let b : ℝ := 6 / 7
  let A := (p + 1) * (p + 2) / (7 / 8) - (2 * p + 1) * (p - 1)
  have ht : 0 ≤ t := sub_nonneg.mpr hp
  have hT : t ≤ 4 / 5 := by unfold t; linarith only [hP]
  have hL : - (1 / 6 : ℝ) ≤ Real.log b := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 7 / 6)
    rw [show b = (7 / 6 : ℝ)⁻¹ by norm_num [b],Real.log_inv]
    linarith only [h]
  have hb : 0 < b := by norm_num [b]
  have hPow : b ^ 3 * (1 - t / 6) ≤ b ^ (p + 2) := by
    rw [show p + 2 = 3 + t by unfold t; ring,Real.rpow_add hb,show (3 : ℝ) = (3 : ℕ) by norm_num,Real.rpow_natCast]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hb.le _)
    rw [Real.rpow_def_of_pos hb]
    have h := Real.add_one_le_exp (Real.log b * t)
    have h' := mul_le_mul_of_nonneg_right hL ht
    linarith only [h,h']
  have hExp : A = 48 / 7 + (19 / 7) * t - (6 / 7) * t ^ 2 := by
    unfold A t
    ring
  have hA : 0 ≤ A := by
    rw [hExp]
    nlinarith only [ht,mul_le_mul_of_nonneg_right hT ht]
  have hProd : (48 / 7 : ℝ) ≤ (1 - t / 6) * A := by
    rw [hExp]
    nlinarith only [ht,mul_le_mul_of_nonneg_right hT ht,pow_nonneg ht 3]
  have hE : knownResponse p (7 / 8) = b ^ (p + 2) * A := by
    unfold knownResponse A b
    norm_num
  rw [hE]
  have h₁ := mul_le_mul_of_nonneg_right hPow hA
  have h₂ := mul_le_mul_of_nonneg_left hProd (pow_nonneg hb.le 3)
  unfold b at h₁ h₂
  norm_num at h₁ h₂
  nlinarith only [h₁,h₂]

theorem lowerKnownFinite_normalized_gt {p δ : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hδ : 0 ≤ δ) (hD : δ ≤ 1 / 8) :
    (423 / 100 : ℝ) * (p * (p + 1) * lowerDiagonalMass δ ^ (-p - 2)) < lowerKnownFiniteD3 p δ := by
  let u := 1 - δ
  let m := lowerDiagonalMass δ
  have hu : u ∈ Icc (7 / 8) 1 := ⟨by unfold u; linarith only [hD],by unfold u; linarith only [hδ]⟩
  have hu₀ := (by norm_num : (0 : ℝ) < 7 / 8).trans_le hu.1
  have hm : 0 < m := by unfold m lowerDiagonalMass; linarith only [hD]
  have hp₀ := zero_lt_one.trans_le hp
  have hB := (knownResponse_far_gt hp hP).trans_le ((knownResponse_mono hp hP)
    (show (7 / 8 : ℝ) ∈ Icc (7 / 8) 1 by constructor <;> norm_num) hu hu.1)
  have hM : 2 - u⁻¹ = m / u := by
    unfold m lowerDiagonalMass
    field_simp [hu₀.ne']
    unfold u
    ring
  have hEq : (p * (p + 1) * m ^ (-p - 2)) * knownResponse p u = lowerKnownFiniteD3 p δ := by
    unfold knownResponse lowerKnownFiniteD3
    rw [hM,Real.div_rpow hm.le hu₀.le,show -p - 2 = -(p + 2) by ring,Real.rpow_neg hm.le]
    change _ = (p + 1) ^ 2 * p * (p + 2) * u ^ (-p - 3) -
      (2 * p + 1) * (p - 1) * p * (p + 1) * u ^ (-(p + 2))
    rw [show -p - 3 = -(p + 2) - 1 by ring,Real.rpow_sub_one hu₀.ne',Real.rpow_neg hu₀.le]
    field_simp [hu₀.ne',(Real.rpow_pos_of_pos hm _).ne',(Real.rpow_pos_of_pos hu₀ _).ne'] <;> ring
  simpa only [mul_comm (423 / 100 : ℝ)] using
    (mul_lt_mul_of_pos_left hB (by positivity : 0 < p * (p + 1) * m ^ (-p - 2))).trans_eq hEq

end ACS12.GammaMeasure

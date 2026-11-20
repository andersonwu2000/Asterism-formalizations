import ACS12.HighNormalizedPressure

/-! The admitted affine lower envelope of the actual exponent-dependent unit pressure. -/
namespace ACS12.Pressure

open Set

noncomputable def highUnitAffine (p : ℝ) : ℝ := (1208 - 107 * p) / 768

theorem highUnitCoefficient_ge_affine {p : ℝ} (hp : 2 ≤ p) (hP : p ≤ 4) :
    highUnitAffine p ≤ highUnitCoefficient p := by
  let l := Real.log 2
  let β (x : ℝ) := (12 - x) / 16
  let E (x : ℝ) := Real.exp (-l * x)
  let f (x : ℝ) := 2 * β x + β x ^ 2 * E x
  let f₁ (x : ℝ) := -1 / 8 + E x * (-β x / 8 - l * β x ^ 2)
  let f₂ (x : ℝ) := E x * (1 / 128 + l * β x / 4 + l ^ 2 * β x ^ 2)
  have hl : 0 < l := by unfold l; linarith only [Real.log_two_gt_d9]
  have hβ (x : ℝ) : HasDerivAt β (-1 / 16) x := by
    simpa only [β,zero_sub] using (((hasDerivAt_id x).const_sub 12).div_const 16)
  have hE (x : ℝ) : HasDerivAt E (-l * E x) x := by
    convert ((hasDerivAt_id x).const_mul (-l)).exp using 1
    simp only [E,id_eq,mul_one]
    ring
  have hD (x : ℝ) : HasDerivAt f (f₁ x) x := by
    convert ((hβ x).const_mul 2).add (((hβ x).pow 2).mul (hE x)) using 1
    simp only [Pi.pow_apply,f₁]
    ring
  have hD₁ (x : ℝ) : HasDerivAt f₁ (f₂ x) x := by
    convert ((hE x).mul (((hβ x).div_const 8).neg.sub (((hβ x).pow 2).const_mul l))).const_add (-1 / 8) using 1
    · funext y
      simp only [f₁,Pi.mul_apply,Pi.neg_apply,Pi.sub_apply,Pi.pow_apply]
      ring
    · simp only [Pi.pow_apply,Pi.mul_apply,Pi.neg_apply,Pi.sub_apply,f₂]
      ring
  have hMono : MonotoneOn f₁ (Icc 2 4) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun x _ => (hD₁ x).continuousAt.continuousWithinAt
    · exact fun x _ => (hD₁ x).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx₄ : x ≤ 4 := (interior_subset hx).2
      have hβx : 0 ≤ β x := by unfold β; linarith only [hx₄]
      rw [(hD₁ x).deriv]
      unfold f₂ E
      positivity
  have hE₄ : E 4 = 1 / 16 := by
    unfold E l
    rw [show -Real.log 2 * (4 : ℝ) = -(4 * Real.log 2) by ring,Real.exp_neg,
      show (4 : ℝ) * Real.log 2 = (4 : ℕ) * Real.log 2 by norm_num,Real.exp_nat_mul,Real.exp_log (by norm_num)]
    norm_num
  have hF₄ : f 4 = 65 / 64 := by norm_num [f,β,hE₄]
  have hD₄ : f₁ 4 + 107 / 768 ≤ 0 := by
    change -1 / 8 + E 4 * (-β 4 / 8 - l * β 4 ^ 2) + 107 / 768 ≤ 0
    rw [hE₄]
    norm_num [β]
    unfold l
    linarith only [Real.log_two_gt_d9]
  let H (x : ℝ) := f x - highUnitAffine x
  have hDH (x : ℝ) : HasDerivAt H (f₁ x + 107 / 768) x := by
    convert (hD x).sub ((((hasDerivAt_id x).const_mul 107).const_sub 1208).div_const 768) using 1
    dsimp only [H,highUnitAffine]
    ring
  have hAnti : AntitoneOn H (Icc 2 4) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · exact fun x _ => (hDH x).continuousAt.continuousWithinAt
    · exact fun x _ => (hDH x).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Icc 2 4 := interior_subset hx
      have h := hMono hx' (show (4 : ℝ) ∈ Icc 2 4 by norm_num) hx'.2
      rw [(hDH x).deriv]
      linarith only [h,hD₄]
  have hH := hAnti (show p ∈ Icc 2 4 from ⟨hp,hP⟩) (show (4 : ℝ) ∈ Icc 2 4 by norm_num) hP
  have hAt : H 4 = 0 := by unfold H highUnitAffine; rw [hF₄]; norm_num
  rw [hAt] at hH
  have hPow : (2 : ℝ) ^ (-(p + 1)) = E p / 2 := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      show Real.log 2 * -(p + 1) = (-Real.log 2 * p) + (-Real.log 2) by ring,
      Real.exp_add,Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    unfold E l
    ring
  have hEq : highUnitCoefficient p = f p := by
    unfold highUnitCoefficient f β
    rw [hPow]
    ring
  rw [hEq]
  exact sub_nonneg.mp hH

end ACS12.Pressure

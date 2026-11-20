import ACS12.PurePeano

/-! The moving lower diagonal's complete right-source response starts with
a positive normalized derivative at every original atom. -/
namespace ACS12.GammaMeasure

open Set

noncomputable def sourceRightD1 (p j U : ℝ) : ℝ :=
  p * (p + 1) * U * (j + U) ^ (-p - 2)

noncomputable def sourceRightD2 (p j U : ℝ) : ℝ :=
  p * (p + 1) * ((j + U) ^ (-p - 2) - (p + 2) * U * (j + U) ^ (-p - 3))

noncomputable def sourceRightD3 (p j U : ℝ) : ℝ :=
  p * (p + 1) * (p + 2) * (-2 * (j + U) ^ (-p - 3) + (p + 3) * U * (j + U) ^ (-p - 4))

noncomputable def sourceRightD4 (p j U : ℝ) : ℝ :=
  p * (p + 1) * (p + 2) * (p + 3) *
    (3 * (j + U) ^ (-p - 4) - (p + 4) * U * (j + U) ^ (-p - 5))

private theorem shiftPower_deriv (j q U : ℝ) (h : 0 < j + U) :
    HasDerivAt (fun x => (j + x) ^ q) (q * (j + U) ^ (q - 1)) U := by
  simpa only [id_eq,one_mul,mul_one] using
    (((hasDerivAt_id U).const_add j).rpow_const (p := q) (Or.inl h.ne'))

theorem sourceRight_deriv1 (p j U : ℝ) (h : 0 < j + U) :
    HasDerivAt (fun x => purePeanoA p x j) (sourceRightD1 p j U) U := by
  have h₁ := shiftPower_deriv j (-p) U h
  have h₂ := shiftPower_deriv j (-(p + 1)) U h
  convert ((hasDerivAt_const U (j ^ (-p))).sub h₁).sub (((hasDerivAt_id U).mul_const p).mul h₂) using 1
  simp only [id_eq,one_mul,zero_sub,sourceRightD1,show -(p + 1) = -p - 1 by ring,
    show -p - 1 - 1 = -p - 2 by ring]
  ring

theorem sourceRight_deriv2 (p j U : ℝ) (h : 0 < j + U) :
    HasDerivAt (sourceRightD1 p j) (sourceRightD2 p j U) U := by
  have h' := ((hasDerivAt_id U).const_mul (p * (p + 1))).mul (shiftPower_deriv j (-p - 2) U h)
  convert h' using 1
  simp only [id_eq,mul_one,sourceRightD2,show -p - 2 - 1 = -p - 3 by ring]
  ring

theorem sourceRight_deriv3 (p j U : ℝ) (h : 0 < j + U) :
    HasDerivAt (sourceRightD2 p j) (sourceRightD3 p j U) U := by
  have h' := ((hasDerivAt_id U).const_mul (p + 2)).mul (shiftPower_deriv j (-p - 3) U h)
  convert ((shiftPower_deriv j (-p - 2) U h).sub h').const_mul (p * (p + 1)) using 1
  simp only [id_eq,mul_one,sourceRightD3,show -p - 2 - 1 = -p - 3 by ring,
    show -p - 3 - 1 = -p - 4 by ring]
  ring

theorem sourceRight_deriv4 (p j U : ℝ) (h : 0 < j + U) :
    HasDerivAt (sourceRightD3 p j) (sourceRightD4 p j U) U := by
  have h' := ((hasDerivAt_id U).const_mul (p + 3)).mul (shiftPower_deriv j (-p - 4) U h)
  convert (((shiftPower_deriv j (-p - 3) U h).const_mul (-2)).add h').const_mul (p * (p + 1) * (p + 2)) using 1
  simp only [id_eq,mul_one,sourceRightD4,show -p - 3 - 1 = -p - 4 by ring,
    show -p - 4 - 1 = -p - 5 by ring]
  ring

noncomputable def lowerRightResponse (p j U : ℝ) : ℝ :=
  8 * (p - 1) * purePeanoA p U j + 12 * (2 * U - 1) * sourceRightD1 p j U +
    6 * (2 * U - 1) ^ 2 * sourceRightD2 p j U / p +
    (2 * U - 1) ^ 3 * sourceRightD3 p j U / (p * (p + 1))

private noncomputable def lowerRightPolynomial (p t k : ℝ) : ℝ :=
  8 * p * (p + 1) + 12 * (p + 1) * k -
    12 * (p + 1) * (p + 2) * t - 12 * (p + 2) * k * t +
    6 * (p + 2) * (p + 3) * t ^ 2 + 3 * (p + 3) * k * t ^ 2 -
    (p + 3) * (p + 4) * t ^ 3

private theorem lowerRightPolynomial_pos {p t k : ℝ} (hp : 1 ≤ p)
    (htU : t ≤ 8 / 13) (hk : 1 ≤ k) :
    0 < lowerRightPolynomial p t k := by
  let x := p - 1
  let y := 8 / 13 - t
  have hx : 0 ≤ x := sub_nonneg.mpr hp
  have hy : 0 ≤ y := sub_nonneg.mpr htU
  have hN : lowerRightPolynomial p t 1 =
      x ^ 2 * (y ^ 3 + 54 / 13 * y ^ 2 + 972 / 169 * y + 5832 / 2197) +
      x * (9 * y ^ 3 + 369 / 13 * y ^ 2 + 4536 / 169 * y + 14580 / 2197) +
      (20 * y ^ 3 + 612 / 13 * y ^ 2 + 4620 / 169 * y) + 1512 / 2197 := by
    unfold lowerRightPolynomial x y
    ring
  have hN₀ : 0 < lowerRightPolynomial p t 1 := by rw [hN]; positivity
  have hC : 0 ≤ 12 * (p + 1) - 12 * (p + 2) * t + 3 * (p + 3) * t ^ 2 := by
    have h := mul_le_mul_of_nonneg_left htU (show 0 ≤ 12 * (p + 2) by positivity)
    have hS : 0 ≤ 3 * (p + 3) * t ^ 2 := by positivity
    nlinarith only [h,hS,hp]
  have hE : lowerRightPolynomial p t k = lowerRightPolynomial p t 1 +
      (k - 1) * (12 * (p + 1) - 12 * (p + 2) * t + 3 * (p + 3) * t ^ 2) := by
    unfold lowerRightPolynomial
    ring
  rw [hE]
  exact add_pos_of_pos_of_nonneg hN₀ (mul_nonneg (sub_nonneg.mpr hk) hC)

private theorem lowerRightResponse_deriv {p j U : ℝ} (hp : 0 < p) (hU : 0 < U) (h : 0 < j + U) :
    HasDerivAt (lowerRightResponse p j)
      ((p + 2) * U * (j + U) ^ (-p - 2) *
        lowerRightPolynomial p ((2 * U - 1) / (j + U)) ((2 * U - 1) / U)) U := by
  have hE := ((hasDerivAt_id U).const_mul 2).sub_const 1
  have h₁ := (sourceRight_deriv1 p j U h).const_mul (8 * (p - 1))
  have h₂ := (hE.const_mul 12).mul (sourceRight_deriv2 p j U h)
  have h₃ := (((hE.pow 2).const_mul 6).mul (sourceRight_deriv3 p j U h)).div_const p
  have h₄ := ((hE.pow 3).mul (sourceRight_deriv4 p j U h)).div_const (p * (p + 1))
  convert ((h₁.add h₂).add h₃).add h₄ using 1
  simp only [id_eq,mul_one,sourceRightD1,sourceRightD2,sourceRightD3,sourceRightD4,lowerRightPolynomial,
    Pi.pow_apply,Nat.cast_ofNat,show (2 : ℕ) - 1 = 1 by decide,show (3 : ℕ) - 1 = 2 by decide,pow_one]
  have hR (n : ℕ) : (j + U) ^ (-p - 2 - n) = (j + U) ^ (-p - 2) / (j + U) ^ n := by
    rw [sub_eq_add_neg,Real.rpow_add h,Real.rpow_neg h.le,Real.rpow_natCast,div_eq_mul_inv]
  have h₃' := hR 1
  have h₄' := hR 2
  have h₅' := hR 3
  norm_num at h₃' h₄' h₅'
  rw [show -p - 3 = -p - 2 - 1 by ring,h₃',
    show -p - 4 = -p - 2 - 2 by ring,h₄',
    show -p - 5 = -p - 2 - 3 by ring,h₅']
  field_simp [hp.ne',(by positivity : 0 < p + 1).ne',hU.ne',h.ne']
  ring

theorem lowerRightResponse_strictMono {p j : ℝ} (hp : 1 ≤ p) (hj : 1 ≤ j) :
    StrictMonoOn (lowerRightResponse p j) (Icc 1 (7 / 6)) := by
  have hp₀ := zero_lt_one.trans_le hp
  have hj₀ := zero_lt_one.trans_le hj
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · intro U hU
    have h₀ := zero_lt_one.trans_le hU.1
    exact (lowerRightResponse_deriv hp₀ h₀ (add_pos hj₀ h₀)).continuousAt.continuousWithinAt
  · intro U hU
    have hU' : U ∈ Icc 1 (7 / 6) := interior_subset hU
    have h₀ := zero_lt_one.trans_le hU'.1
    have h := add_pos hj₀ h₀
    have ht : (2 * U - 1) / (j + U) ≤ 8 / 13 := (div_le_iff₀ h).mpr (by linarith only [hj,hU'.2])
    have hk : 1 ≤ (2 * U - 1) / U := (le_div_iff₀ h₀).mpr (by linarith only [hU'.1])
    rw [(lowerRightResponse_deriv hp₀ h₀ h).deriv]
    exact mul_pos (by positivity) (lowerRightPolynomial_pos hp ht hk)

end ACS12.GammaMeasure

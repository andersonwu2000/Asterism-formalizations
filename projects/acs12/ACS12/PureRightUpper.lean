import ACS12.PureClipLower

/-! The complete fourth-order right-kernel upper used at the last clipped atom. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open BoseShape (positive_of_derivative)

private theorem exp_neg_fourth_upper {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) < 1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24 := by
  let f₁ (x : ℝ) := Real.exp (-x) - (1 - x)
  let f₂ (x : ℝ) := 1 - x + x ^ 2 / 2 - Real.exp (-x)
  let f₃ (x : ℝ) := Real.exp (-x) - (1 - x + x ^ 2 / 2 - x ^ 3 / 6)
  let f₄ (x : ℝ) := 1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24 - Real.exp (-x)
  have h₁ (x : ℝ) : HasDerivAt f₁ (1 - Real.exp (-x)) x := by
    convert (hasDerivAt_neg x).exp.sub ((hasDerivAt_id x).const_sub 1) using 1
    simp [sub_eq_add_neg, add_comm]
  have h₂ (x : ℝ) : HasDerivAt f₂ (f₁ x) x := by
    have h := (hasDerivAt_id x).const_sub 1
    convert (h.add (((hasDerivAt_id x).pow 2).div_const 2)).sub (hasDerivAt_neg x).exp using 1
    norm_num [f₁] <;> ring
  have h₃ (x : ℝ) : HasDerivAt f₃ (f₂ x) x := by
    have h := ((hasDerivAt_id x).const_sub 1).add (((hasDerivAt_id x).pow 2).div_const 2)
    convert (hasDerivAt_neg x).exp.sub (h.sub (((hasDerivAt_id x).pow 3).div_const 6)) using 1
    norm_num [f₂] <;> ring
  have h₄ (x : ℝ) : HasDerivAt f₄ (f₃ x) x := by
    have h := (((hasDerivAt_id x).const_sub 1).add (((hasDerivAt_id x).pow 2).div_const 2)).sub
      (((hasDerivAt_id x).pow 3).div_const 6)
    convert (h.add (((hasDerivAt_id x).pow 4).div_const 24)).sub (hasDerivAt_neg x).exp using 1
    norm_num [f₃] <;> ring
  have hPos₁ (x : ℝ) (hx : 0 < x) : 0 < f₁ x :=
    positive_of_derivative (by norm_num [f₁]) h₁
      (fun y hy => sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hy))) hx
  have hPos₂ (x : ℝ) (hx : 0 < x) : 0 < f₂ x :=
    positive_of_derivative (by norm_num [f₂]) h₂ hPos₁ hx
  have hPos₃ (x : ℝ) (hx : 0 < x) : 0 < f₃ x :=
    positive_of_derivative (by norm_num [f₃]) h₃ hPos₂ hx
  exact sub_pos.mp (positive_of_derivative (by norm_num [f₄]) h₄ hPos₃ hx)

theorem pureMoment_succ {p L t : ℝ} (hp : 0 < p) (ht : 0 < t) (j : ℕ) :
    lawMoment p L 0 (j + 1) t = lawMoment p L 0 j t * ((p + j) / t) := by
  rw [pureMoment_eq hp ht, pureMoment_eq hp ht, Nat.cast_add, Nat.cast_one,
    ← add_assoc, Real.Gamma_add_one (show p + j ≠ 0 by positivity),
    show -(p + (j : ℝ) + 1) = -(p + j) - 1 by ring, Real.rpow_sub_one ht.ne']
  ring

noncomputable def rightTaylorA (p u : ℝ) : ℝ := (1 / 2 - middleA u) * (p + 1)
noncomputable def rightTaylorB (p u : ℝ) : ℝ := (1 / 6 - middleA u / 2) * (p + 1) * (p + 2)
noncomputable def rightTaylorC (p u : ℝ) : ℝ :=
  (1 / 24 - middleA u / 6) * (p + 1) * (p + 2) * (p + 3)
noncomputable def rightTaylorD (p u : ℝ) : ℝ :=
  (middleA u / 24) * (p + 1) * (p + 2) * (p + 3) * (p + 4)

theorem pureRight_quartic_upper {p u t : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hu : 0 < u) (hu₁ : u ≤ 1) (ht : 0 < t) :
    pureRight p u t <
      (p * t ^ (-(p + 1))) * (-(1 - u) + rightTaylorA p u / t - rightTaylorB p u / t ^ 2 +
        rightTaylorC p u / t ^ 3 + rightTaylorD p u / t ^ 4) := by
  let a := middleA u
  let b := 1 / 2 - a
  let c := 1 / 6 - a / 2
  let d := 1 / 24 - a / 6
  let e := a / 24
  let m (j : ℕ) (s : ℝ) := lawDensity p 1 0 s * s ^ j * Real.exp (-s * t)
  let f₁ (s : ℝ) := -(1 - u) * m 1 s + b * m 2 s
  let f₂ (s : ℝ) := f₁ s - c * m 3 s
  let f₃ (s : ℝ) := f₂ s + d * m 4 s
  let f (s : ℝ) := f₃ s + e * m 5 s
  let g (s : ℝ) := lawRightDensity p 1 0 u s * Real.exp (-s * t)
  let μ := volume.restrict (Ioi (0 : ℝ))
  have hp₀ := zero_lt_one.trans_le hp
  have hθ : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have ha : 0 ≤ a := by
    dsimp only [a, middleA]
    exact mul_nonneg (mul_nonneg (by norm_num) hu.le) (by linarith)
  have hM (j : ℕ) : Integrable (m j) μ := lawMoment_integrable hp hp₂ zero_lt_one hθ ht j
  have hI₁ : Integrable f₁ μ := ((hM 1).const_mul _).add ((hM 2).const_mul _)
  have hI₂ : Integrable f₂ μ := hI₁.sub ((hM 3).const_mul _)
  have hI₃ : Integrable f₃ μ := hI₂.add ((hM 4).const_mul _)
  have hf : Integrable f μ := hI₃.add ((hM 5).const_mul _)
  have hg : Integrable g μ := lawRightDensity_integrable hp hp₂ zero_lt_one hθ ht
  letI : NeZero μ := ⟨positiveHalfLine_ne_zero⟩
  have hLt := integral_strict_of_ae_lt μ hg hf (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0 < s := hs
    have hE := mul_lt_mul_of_pos_left (exp_neg_fourth_upper hs₀) (show 0 < 1 + a * s by positivity)
    have h := mul_lt_mul_of_pos_left hE
      (mul_pos (lawDensity_pos hp₀ zero_lt_one hθ hs₀) (Real.exp_pos (-s * t)))
    dsimp only [g, f, f₃, f₂, f₁, m, b, c, d, e, lawRightDensity, middleRightDensity, middleA0, middleZ]
    nlinarith only [h])
  have hF₁ : (∫ s : ℝ, f₁ s ∂μ) = -(1 - u) * lawMoment p 1 0 1 t + b * lawMoment p 1 0 2 t := by
    dsimp only [f₁]
    rw [integral_add ((hM 1).const_mul (-(1 - u))) ((hM 2).const_mul b),
      integral_const_mul, integral_const_mul]
    rfl
  have hF₂ : (∫ s : ℝ, f₂ s ∂μ) = (∫ s : ℝ, f₁ s ∂μ) - c * lawMoment p 1 0 3 t := by
    dsimp only [f₂]
    rw [integral_sub hI₁ ((hM 3).const_mul c), integral_const_mul]
    rfl
  have hF₃ : (∫ s : ℝ, f₃ s ∂μ) = (∫ s : ℝ, f₂ s ∂μ) + d * lawMoment p 1 0 4 t := by
    dsimp only [f₃]
    rw [integral_add hI₂ ((hM 4).const_mul d), integral_const_mul]
    rfl
  have hF : (∫ s : ℝ, f s ∂μ) = (∫ s : ℝ, f₃ s ∂μ) + e * lawMoment p 1 0 5 t := by
    dsimp only [f]
    rw [integral_add hI₃ ((hM 5).const_mul e), integral_const_mul]
    rfl
  have hG : (∫ s : ℝ, g s ∂μ) = pureRight p u t := lawRightTest_zero hp hp₂ zero_lt_one ht
  rw [hG, hF, hF₃, hF₂, hF₁] at hLt
  rw [pureMoment_succ hp₀ ht 4, pureMoment_succ hp₀ ht 3, pureMoment_succ hp₀ ht 2,
    pureMoment_succ hp₀ ht 1, lawMoment_zero_slope hp₀ ht] at hLt
  norm_num only [Nat.cast_ofNat, Nat.cast_one] at hLt
  convert hLt using 1
  dsimp only [a, b, c, d, e, rightTaylorA, rightTaylorB, rightTaylorC, rightTaylorD]
  ring

end ACS12.GammaMeasure

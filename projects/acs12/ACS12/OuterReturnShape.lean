import ACS12.OuterGap
import ACS12.MiddleScalar

/-! Full positive-ray bounds for the selected outer once-self return. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN Set

noncomputable def middleA0 (u s : ℝ) : ℝ :=
  1 - (1 + middleA u * s) * Real.exp (-s)

noncomputable def middleRightDensity (u s : ℝ) : ℝ :=
  middleZ u * s - middleA0 u s

noncomputable def outerNativeResponse (u m s : ℝ) : ℝ :=
  (1 - u) * middleA0 u s - middleRightDensity u s *
    (Real.exp (-s * u) * (u - m) - (scaledExpTail s u - scaledExpTail s 1))

theorem boseC_lt_half {x : ℝ} (hx : 0 < x) : BoseShape.C x < 1 / 2 := by
  unfold BoseShape.C
  apply (div_lt_iff₀ (sq_pos_of_pos (expTail_den_pos hx))).mpr
  have h := Real.self_lt_sinh_iff.mpr hx
  rw [Real.sinh_eq] at h
  have hP := mul_lt_mul_of_pos_right h (Real.exp_pos x)
  have he : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  nlinarith only [hP, he]

private theorem outerFirstPoly_pos {x : ℝ} (hx : 0 < x) :
    0 < (1 / 2) * Real.exp (2 * x) + (1 / 2) * Real.exp x -
      1 - x * Real.exp x - (12 / 25) * x := by
  let F (s : ℝ) := (1 / 2) * Real.exp (2 * s) + (1 / 2) * Real.exp s -
      1 - s * Real.exp s - (12 / 25) * s
  let D (s : ℝ) := Real.exp (2 * s) - (s + 1 / 2) * Real.exp s - 12 / 25
  have hD (s : ℝ) : HasDerivAt F (D s) s := by
    have hE₂ := (((hasDerivAt_id s).const_mul (2 : ℝ)).exp).const_mul (1 / 2)
    have hE₁ := (Real.hasDerivAt_exp s).const_mul (1 / 2)
    have h := (((hE₂.add hE₁).sub_const 1).sub ((hasDerivAt_id s).mul (Real.hasDerivAt_exp s))).sub
      ((hasDerivAt_id s).const_mul (12 / 25))
    convert h using 1
    simp only [D, id_eq, one_mul, mul_one]
    ring
  have hP (s : ℝ) (hs : 0 < s) : 0 < D s := by
    have he : Real.exp (2 * s) = Real.exp s * Real.exp s := by rw [two_mul, Real.exp_add]
    have h := Real.add_one_le_exp s
    have hA : 1 / 2 ≤ Real.exp s - (s + 1 / 2) := by linarith
    have hB := mul_le_mul_of_nonneg_left hA (Real.exp_pos s).le
    have hC := Real.one_le_exp_iff.mpr hs.le
    change 0 < Real.exp (2 * s) - (s + 1 / 2) * Real.exp s - 12 / 25
    rw [he]
    nlinarith only [hB, hC]
  exact BoseShape.positive_of_derivative (by norm_num [F]) hD hP hx

theorem outerNative_lower_half {u s : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) (hs : 0 < s) :
    (1 / 2) * (1 - Real.exp (-s * u)) <
      middleA0 u s - Real.exp (-s * u) * middleRightDensity u s := by
  let x := u * s
  let Y := Real.exp (-x)
  let X := Real.exp (-s)
  let a := middleA u
  let z := middleZ u
  have hx : 0 < x := mul_pos hu hs
  have hXY : X ≤ Y := Real.exp_le_exp.mpr (by dsimp only [x]; nlinarith only [mul_le_mul_of_nonneg_right hu₁ hs.le])
  have ha : 0 ≤ a := (middleA_pos hu hu₁).le
  have hA : a * s ≤ (12 / 25) * x := by
    dsimp only [a, x, middleA]
    have h := mul_nonneg (mul_nonneg hu.le hs.le) hu.le
    nlinarith only [h]
  have haz : a + z = u := by dsimp only [z, a, middleZ]; ring
  have hAz : a * s * Y + z * s * Y = x * Y := by
    dsimp only [x]
    linear_combination s * Y * haz
  have hY₀ : 0 < Y := Real.exp_pos _
  have hAY := mul_le_mul_of_nonneg_right
    (sub_le_sub_left (mul_le_mul_of_nonneg_left hXY (by positivity : 0 ≤ 1 + a * s)) 1)
    (by positivity : 0 ≤ 1 + Y)
  have hCost := mul_le_mul_of_nonneg_right hA (sq_nonneg Y)
  have hExp1 : Real.exp x * Y = 1 := by
    dsimp only [Y]
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hExp2 : Real.exp (2 * x) * Y ^ 2 = 1 := by
    rw [two_mul, Real.exp_add, ← sq, ← mul_pow, hExp1, one_pow]
  have hF := mul_pos (outerFirstPoly_pos hx) (sq_pos_of_pos hY₀)
  have hFE : ((1 / 2) * Real.exp (2 * x) + (1 / 2) * Real.exp x -
      1 - x * Real.exp x - (12 / 25) * x) * Y ^ 2 =
        1 - Y ^ 2 - x * Y - (12 / 25) * x * Y ^ 2 - (1 / 2) * (1 - Y) := by
    linear_combination (1 / 2) * hExp2 + (1 / 2 - x) * Y * hExp1
  rw [hFE] at hF
  have hYe : Real.exp (-s * u) = Y := by
    dsimp only [Y, x]
    rw [show -s * u = -(u * s) by ring]
  rw [hYe]
  change (1 / 2) * (1 - Y) < (1 - (1 + a * s) * X) - Y * (z * s - (1 - (1 + a * s) * X))
  nlinarith only [hF, hAY, hCost, hAz]

private theorem cubic_le_exp {x : ℝ} (hx : 0 ≤ x) :
    1 + x + x ^ 2 / 2 + x ^ 3 / 6 ≤ Real.exp x := by
  let f (t : ℝ) := Real.exp t - (1 + t + t ^ 2 / 2 + t ^ 3 / 6)
  have hd (t : ℝ) : HasDerivAt f (Real.exp t - (1 + t + t ^ 2 / 2)) t := by
    have hP := (((hasDerivAt_id t).const_add 1).add (((hasDerivAt_id t).pow 2).div_const 2)).add
      (((hasDerivAt_id t).pow 3).div_const 6)
    convert (Real.hasDerivAt_exp t).sub hP using 1
    norm_num [id_eq, show (2 - 1 : ℕ) = 1 by decide, show (3 - 1 : ℕ) = 2 by decide] <;> ring
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun t _ => (hd t).continuousAt.continuousWithinAt
    · exact fun t _ => (hd t).differentiableAt.differentiableWithinAt
    · intro t ht
      have h : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
      rw [(hd t).deriv]
      exact sub_nonneg.mpr (Real.quadratic_le_exp_of_nonneg h.le)
  have h := hm (mem_Ici.mpr (le_refl (0 : ℝ))) (mem_Ici.mpr hx) hx
  have h0 : f 0 = 0 := by norm_num [f]
  rw [h0] at h
  exact sub_nonneg.mp h

private noncomputable def kReturnPoly (x : ℝ) : ℝ :=
  BoseShape.expQuad 3 0 0 1 x + BoseShape.expQuad 2 (-2) 6 (-5) x +
    BoseShape.expQuad 1 0 (-8) 7 x + 2 * x - 3

private theorem kReturnPoly_pos {x : ℝ} (hx : 0 < x) : 0 < kReturnPoly x := by
  let f₁ (t : ℝ) := BoseShape.expQuad 3 0 0 3 t + BoseShape.expQuad 2 (-4) 8 (-4) t +
    BoseShape.expQuad 1 0 (-8) (-1) t + 2
  let f₂ (t : ℝ) := BoseShape.expQuad 3 0 0 9 t + BoseShape.expQuad 2 (-8) 8 0 t +
    BoseShape.expQuad 1 0 (-8) (-9) t
  let f₃ (t : ℝ) := BoseShape.expQuad 3 0 0 27 t + BoseShape.expQuad 2 (-16) 0 8 t +
    BoseShape.expQuad 1 0 (-8) (-17) t
  have h₁ (t : ℝ) : HasDerivAt kReturnPoly (f₁ t) t := by
    convert (((((BoseShape.expQuad_deriv 3 0 0 1 t).add
      (BoseShape.expQuad_deriv 2 (-2) 6 (-5) t)).add
      (BoseShape.expQuad_deriv 1 0 (-8) 7 t)).add ((hasDerivAt_id t).const_mul 2)).sub_const 3) using 1
    norm_num [f₁]
  have h₂ (t : ℝ) : HasDerivAt f₁ (f₂ t) t := by
    convert ((((BoseShape.expQuad_deriv 3 0 0 3 t).add
      (BoseShape.expQuad_deriv 2 (-4) 8 (-4) t)).add
      (BoseShape.expQuad_deriv 1 0 (-8) (-1) t)).add_const 2) using 1
    norm_num [f₂]
  have h₃ (t : ℝ) : HasDerivAt f₂ (f₃ t) t := by
    convert (((BoseShape.expQuad_deriv 3 0 0 9 t).add
      (BoseShape.expQuad_deriv 2 (-8) 8 0 t)).add
      (BoseShape.expQuad_deriv 1 0 (-8) (-9) t)) using 1
    norm_num [f₃]
  have hP₃ (t : ℝ) (ht : 0 < t) : 0 < f₃ t := by
    have hExp := cubic_le_exp ht.le
    have he : 0 < 27 * Real.exp t - 16 * t ^ 2 + 8 - (17 + 8 * t) := by
      by_cases h1 : t ≤ 1
      · have h2 := pow_le_pow_left₀ ht.le h1 2
        nlinarith only [hExp, h2, ht, pow_nonneg ht.le 3]
      · have h2 := mul_le_mul_of_nonneg_right (le_of_not_ge h1) (sq_nonneg t)
        nlinarith only [hExp, h2, ht, sq_nonneg t]
    have he' := mul_pos he (sq_pos_of_pos (Real.exp_pos t))
    have hComp := mul_nonneg (show 0 ≤ (17 + 8 * t) * Real.exp t by positivity)
      (sub_nonneg.mpr (Real.one_le_exp_iff.mpr ht.le))
    have hE₂ : Real.exp (2 * t) = Real.exp t ^ 2 := by rw [two_mul, Real.exp_add, sq]
    have hE₃ : Real.exp (3 * t) = Real.exp t ^ 3 := by
      rw [show 3 * t = 2 * t + t by ring, Real.exp_add, hE₂]
      ring
    simp only [f₃, BoseShape.expQuad, hE₂, hE₃, one_mul]
    nlinarith only [he', hComp]
  have hP₂ (t : ℝ) (ht : 0 < t) : 0 < f₂ t :=
    BoseShape.positive_of_derivative (by norm_num [f₂, BoseShape.expQuad]) h₃ hP₃ ht
  have hP₁ (t : ℝ) (ht : 0 < t) : 0 < f₁ t :=
    BoseShape.positive_of_derivative (by norm_num [f₁, BoseShape.expQuad]) h₂ hP₂ ht
  exact BoseShape.positive_of_derivative (by norm_num [kReturnPoly, BoseShape.expQuad]) h₁ hP₁ hx

theorem outerPeanoC_upper {x : ℝ} (hx : 0 < x) :
    polyA x + polyB x * BoseShape.C x < (3 / 2) * (1 - Real.exp (-x)) := by
  have hEq : 2 * Real.exp x * (Real.exp x - 1) ^ 2 *
      ((3 / 2) * (1 - Real.exp (-x)) - (polyA x + polyB x * BoseShape.C x)) =
        kReturnPoly x := by
    have hE₂ : Real.exp (2 * x) = Real.exp x ^ 2 := by rw [two_mul, Real.exp_add, sq]
    have hE₃ : Real.exp (3 * x) = Real.exp x ^ 3 := by
      rw [show 3 * x = 2 * x + x by ring, Real.exp_add, hE₂]
      ring
    simp only [kReturnPoly, BoseShape.expQuad, polyA, polyB, BoseShape.C, Real.exp_neg,
      hE₂, hE₃, one_mul]
    field_simp [(expTail_den_pos hx).ne', Real.exp_ne_zero x]
    ring
  apply sub_pos.mp
  exact pos_of_mul_pos_right (hEq.symm ▸ kReturnPoly_pos hx)
    (mul_nonneg (by positivity) (sq_nonneg _))

end ACS12.GammaMeasure


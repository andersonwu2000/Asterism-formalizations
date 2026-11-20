import ACS12.PureRightOrder

/-! A complete quadratic spatial lower and a one-peak clipping majorant. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaDeficit (lineDensity gamma_exp_integral)
open BoseShape (positive_of_derivative expQuad expQuad_deriv)

private theorem rightMultiplier_quadratic_lt {u s : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) (hs : 0 < s) :
    -(1 - u) + (1 / 2 - middleA u) * s - (1 / 6 - middleA u / 2) * s ^ 2 <
      rightMultiplier (middleA u) (middleZ u) s := by
  let a := middleA u
  let c := 1 / 2 - a
  let d := 1 / 6 - a / 2
  let f (x : ℝ) := (1 - a) * x - 1 + expQuad (-1) 0 a 1 x - c * x ^ 2 + d * x ^ 3
  let f₁ (x : ℝ) := (1 - a) + expQuad (-1) 0 (-a) (a - 1) x - 2 * c * x + 3 * d * x ^ 2
  let f₂ (x : ℝ) := expQuad (-1) 0 a (1 - 2 * a) x - 2 * c + 6 * d * x
  let f₃ (x : ℝ) := expQuad (-1) 0 (-a) (3 * a - 1) x + 6 * d
  let f₄ (x : ℝ) := expQuad (-1) 0 a (1 - 4 * a) x
  have h₁ (x : ℝ) : HasDerivAt f (f₁ x) x := by
    have hx := hasDerivAt_id x
    convert ((((hx.const_mul (1 - a)).sub_const 1).add (expQuad_deriv (-1) 0 a 1 x)).sub
      ((hx.pow 2).const_mul c)).add ((hx.pow 3).const_mul d) using 1
    norm_num [f₁, expQuad] <;> ring
  have h₂ (x : ℝ) : HasDerivAt f₁ (f₂ x) x := by
    have hx := hasDerivAt_id x
    convert ((((expQuad_deriv (-1) 0 (-a) (a - 1) x).const_add (1 - a)).sub
      ((hx.const_mul (2 * c)))).add ((hx.pow 2).const_mul (3 * d))) using 1
    norm_num [f₂, expQuad] <;> ring
  have h₃ (x : ℝ) : HasDerivAt f₂ (f₃ x) x := by
    convert (((expQuad_deriv (-1) 0 a (1 - 2 * a) x).sub_const (2 * c)).add
      ((hasDerivAt_id x).const_mul (6 * d))) using 1
    norm_num [f₃, expQuad] <;> ring
  have h₄ (x : ℝ) : HasDerivAt f₃ (f₄ x) x := by
    convert (expQuad_deriv (-1) 0 (-a) (3 * a - 1) x).add_const (6 * d) using 1
    norm_num [f₄, expQuad] <;> ring
  have hA : a ≤ 6 / 25 := middleA_le u
  have hP (x : ℝ) (hx : 0 < x) : 0 < f₄ x := by
    unfold f₄ expQuad
    rw [zero_mul, zero_add]
    have ha : 0 ≤ a := by
      dsimp only [a, middleA]
      exact mul_nonneg (mul_nonneg (by norm_num) hu.le) (by linarith)
    exact mul_pos (by nlinarith [mul_nonneg ha hx.le]) (Real.exp_pos _)
  have hP₃ (x : ℝ) (hx : 0 < x) : 0 < f₃ x :=
    positive_of_derivative (by norm_num [f₃, expQuad, d] <;> ring) h₄ hP hx
  have hP₂ (x : ℝ) (hx : 0 < x) : 0 < f₂ x :=
    positive_of_derivative (by norm_num [f₂, expQuad, c] <;> ring) h₃ hP₃ hx
  have hP₁ (x : ℝ) (hx : 0 < x) : 0 < f₁ x :=
    positive_of_derivative (by norm_num [f₁, expQuad]) h₂ hP₂ hx
  have hF := positive_of_derivative (by norm_num [f, expQuad]) h₁ hP₁ hs
  apply lt_of_mul_lt_mul_left _ hs.le
  have hE : s * (rightMultiplier (middleA u) (middleZ u) s -
      (-(1 - u) + (1 / 2 - a) * s - (1 / 6 - a / 2) * s ^ 2)) = f s := by
    dsimp only [f, c, d, expQuad, a, rightMultiplier, middleZ]
    field_simp [hs.ne']
    ring
  rw [mul_sub] at hE
  linarith only [hE, hF]

theorem pureMoment_eq {p L t : ℝ} (hp : 0 < p) (ht : 0 < t) (j : ℕ) :
    lawMoment p L 0 j t = (Real.Gamma (p + j) / Real.Gamma p) * t ^ (-(p + j)) := by
  simp only [lawMoment, lawDensity, sub_zero, one_mul, zero_mul, add_zero]
  have hE (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      lineDensity p s * s ^ j * Real.exp (-s * t) =
        (Real.Gamma p)⁻¹ * (s ^ (p + j - 1) * Real.exp (-s * t)) := by
    unfold lineDensity
    rw [← Real.rpow_natCast, show p + (j : ℝ) - 1 = p - 1 + j by ring, Real.rpow_add hs]
    ring
  have h := gamma_exp_integral (show 0 < p + j by positivity) ht
  simp only [neg_mul, mul_comm t] at h
  rw [setIntegral_congr_fun measurableSet_Ioi hE, integral_const_mul]
  simp_rw [show ∀ s : ℝ, -s * t = -(s * t) by intro s; ring]
  rw [h]
  ring

theorem pureRight_quadratic_lower {p u t : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hu : 0 < u) (hu₁ : u ≤ 1) (ht : 0 < t) :
    p * t ^ (-(p + 1)) * (-(1 - u) + ((1 / 2 - middleA u) * (p + 1)) / t -
      ((1 / 6 - middleA u / 2) * (p + 1) * (p + 2)) / t ^ 2) < pureRight p u t := by
  let c := 1 / 2 - middleA u
  let d := 1 / 6 - middleA u / 2
  let m (j : ℕ) (s : ℝ) := lawDensity p 1 0 s * s ^ j * Real.exp (-s * t)
  let f (s : ℝ) := -(1 - u) * m 1 s + c * m 2 s - d * m 3 s
  let g (s : ℝ) := lawRightDensity p 1 0 u s * Real.exp (-s * t)
  have hp₀ := zero_lt_one.trans_le hp
  have hθ : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have hM (j : ℕ) : IntegrableOn (m j) (Ioi 0) := lawMoment_integrable hp hp₂ zero_lt_one hθ ht j
  have hf : IntegrableOn f (Ioi 0) :=
    (((hM 1).const_mul _).add ((hM 2).const_mul _)).sub ((hM 3).const_mul _)
  have hg : IntegrableOn g (Ioi 0) := lawRightDensity_integrable hp hp₂ zero_lt_one hθ ht
  letI : NeZero (volume.restrict (Ioi (0 : ℝ))) := ⟨positiveHalfLine_ne_zero⟩
  have hI := integral_strict_of_ae_lt (volume.restrict (Ioi (0 : ℝ))) hf hg (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have h := mul_lt_mul_of_pos_left (rightMultiplier_quadratic_lt hu hu₁ hs)
      (mul_pos (mul_pos (lawDensity_pos hp₀ zero_lt_one hθ hs) hs) (Real.exp_pos (-s * t)))
    dsimp only [f, m, g, c, d, lawRightDensity]
    rw [middleRightDensity_eq hs]
    nlinarith only [h])
  have hF : (∫ s : ℝ in Ioi 0, f s) =
      -(1 - u) * lawMoment p 1 0 1 t + c * lawMoment p 1 0 2 t - d * lawMoment p 1 0 3 t := by
    have h12 : IntegrableOn (fun s => -(1 - u) * m 1 s + c * m 2 s) (Ioi 0) :=
      ((hM 1).const_mul _).add ((hM 2).const_mul _)
    dsimp only [f]
    rw [integral_sub h12 ((hM 3).const_mul d),
      integral_add ((hM 1).const_mul (-(1 - u))) ((hM 2).const_mul c),
      integral_const_mul, integral_const_mul, integral_const_mul]
    rfl
  have hG : (∫ s : ℝ in Ioi 0, g s) = pureRight p u t := lawRightTest_zero hp hp₂ zero_lt_one ht
  rw [hF, hG, pureMoment_eq hp₀ ht, pureMoment_eq hp₀ ht, pureMoment_eq hp₀ ht] at hI
  simp only [Nat.cast_one, Nat.cast_ofNat] at hI
  rw [show p + 3 = (p + 2) + 1 by ring,
    Real.Gamma_add_one (show p + 2 ≠ 0 by positivity),
    show p + 2 = (p + 1) + 1 by ring,
    Real.Gamma_add_one (show p + 1 ≠ 0 by positivity),
    Real.Gamma_add_one hp₀.ne',
    show -(p + 1 + 1) = -(p + 1) - 1 by ring,
    show -(p + 1 + 1 + 1) = -(p + 1) - 2 by ring,
    Real.rpow_sub_one ht.ne', Real.rpow_sub ht (-(p + 1)) 2, Real.rpow_two] at hI
  have hΓ := (Real.Gamma_pos_of_pos hp₀).ne'
  convert hI using 1
  dsimp only [c, d]
  field_simp [hΓ, ht.ne']
  ring

end ACS12.GammaMeasure

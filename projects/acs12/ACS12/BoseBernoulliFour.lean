import ACS12.PureZetaBound

/-! The full fourth-Bernoulli lower bound for the Bose kernel. -/
namespace ACS12.GammaMeasure

open CenteredCircle.AllN

private noncomputable def expQuartic (a b c d e x : ℝ) : ℝ :=
  (a * x ^ 4 + b * x ^ 3 + c * x ^ 2 + d * x + e) * Real.exp x

private theorem expQuartic_deriv (a b c d e x : ℝ) :
    HasDerivAt (expQuartic a b c d e) (expQuartic a (b + 4 * a) (c + 3 * b) (d + 2 * c) (e + d) x) x := by
  have hx := hasDerivAt_id x
  have h := (((((hx.pow 4).const_mul a).add ((hx.pow 3).const_mul b)).add
    ((hx.pow 2).const_mul c)).add (hx.const_mul d)).add_const e
  convert h.mul (Real.hasDerivAt_exp x) using 1
  norm_num [expQuartic,id_eq]
  ring

private theorem bose_b4_polynomial_pos {x : ℝ} (hx : 0 < x) :
    0 < (x ^ 4 - 60 * x ^ 2 + 360 * x - 720) * Real.exp x + 720 + 360 * x + 60 * x ^ 2 - x ^ 4 := by
  let f (t : ℝ) := expQuartic 1 0 (-60) 360 (-720) t + 720 + 360 * t + 60 * t ^ 2 - t ^ 4
  let f₁ (t : ℝ) := expQuartic 1 4 (-60) 240 (-360) t + 360 + 120 * t - 4 * t ^ 3
  let f₂ (t : ℝ) := expQuartic 1 8 (-48) 120 (-120) t + 120 - 12 * t ^ 2
  let f₃ (t : ℝ) := expQuartic 1 12 (-24) 24 0 t - 24 * t
  let f₄ (t : ℝ) := expQuartic 1 16 12 (-24) 24 t - 24
  let f₅ (t : ℝ) := expQuartic 1 20 60 0 0 t
  have h₁ (t : ℝ) : HasDerivAt f (f₁ t) t := by
    have h := hasDerivAt_id t
    convert ((((expQuartic_deriv 1 0 (-60) 360 (-720) t).add_const 720).add (h.const_mul 360)).add
      ((h.pow 2).const_mul 60)).sub (h.pow 4) using 1
    norm_num [f₁,expQuartic,id_eq] <;> ring
  have h₂ (t : ℝ) : HasDerivAt f₁ (f₂ t) t := by
    have h := hasDerivAt_id t
    convert (((expQuartic_deriv 1 4 (-60) 240 (-360) t).add_const 360).add (h.const_mul 120)).sub
      ((h.pow 3).const_mul 4) using 1
    norm_num [f₂,expQuartic,id_eq] <;> ring
  have h₃ (t : ℝ) : HasDerivAt f₂ (f₃ t) t := by
    have h := hasDerivAt_id t
    convert ((expQuartic_deriv 1 8 (-48) 120 (-120) t).add_const 120).sub
      ((h.pow 2).const_mul 12) using 1
    norm_num [f₃,expQuartic,id_eq] <;> ring
  have h₄ (t : ℝ) : HasDerivAt f₃ (f₄ t) t := by
    convert (expQuartic_deriv 1 12 (-24) 24 0 t).sub ((hasDerivAt_id t).const_mul 24) using 1
    norm_num [f₄,expQuartic,id_eq]
  have h₅ (t : ℝ) : HasDerivAt f₄ (f₅ t) t := by
    convert (expQuartic_deriv 1 16 12 (-24) 24 t).sub_const 24 using 1
    norm_num [f₅,expQuartic]
  have hP₅ (t : ℝ) (ht : 0 < t) : 0 < f₅ t := by unfold f₅ expQuartic; positivity
  have hP₄ (t : ℝ) (ht : 0 < t) : 0 < f₄ t :=
    BoseShape.positive_of_derivative (by norm_num [f₄,expQuartic]) h₅ hP₅ ht
  have hP₃ (t : ℝ) (ht : 0 < t) : 0 < f₃ t :=
    BoseShape.positive_of_derivative (by norm_num [f₃,expQuartic]) h₄ hP₄ ht
  have hP₂ (t : ℝ) (ht : 0 < t) : 0 < f₂ t :=
    BoseShape.positive_of_derivative (by norm_num [f₂,expQuartic]) h₃ hP₃ ht
  have hP₁ (t : ℝ) (ht : 0 < t) : 0 < f₁ t :=
    BoseShape.positive_of_derivative (by norm_num [f₁,expQuartic]) h₂ hP₂ ht
  have h := BoseShape.positive_of_derivative (by norm_num [f,expQuartic]) h₁ hP₁ hx
  convert h using 1
  unfold f expQuartic
  ring

theorem bose_inverse_B4 {s : ℝ} (hs : 0 < s) :
    s⁻¹ + 1 / 2 + s / 12 - s ^ 3 / 720 < (1 - Real.exp (-s))⁻¹ := by
  have hD := expTail_den_pos hs
  have hA : (1 - Real.exp (-s))⁻¹ = Real.exp s / (Real.exp s - 1) := by
    rw [Real.exp_neg]
    field_simp [Real.exp_ne_zero s,hD.ne']
  rw [hA]
  apply (lt_div_iff₀ hD).mpr
  have h := bose_b4_polynomial_pos hs
  apply lt_of_mul_lt_mul_left _ (show 0 ≤ 720 * s by positivity)
  have hE : 720 * s * ((s⁻¹ + 1 / 2 + s / 12 - s ^ 3 / 720) * (Real.exp s - 1)) =
      (720 + 360 * s + 60 * s ^ 2 - s ^ 4) * (Real.exp s - 1) := by
    field_simp [hs.ne']
    ring
  rw [hE]
  nlinarith only [h]

end ACS12.GammaMeasure


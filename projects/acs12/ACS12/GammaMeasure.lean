import CenteredCircle.EulerIntegral
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! The beta integral for the actual positive-power Gamma density. -/

namespace ACS12.GammaMeasure

open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

noncomputable def betaProfile (p x : ℝ) : ℝ :=
  Real.exp (p * x / 2) / (1 + Real.exp x) ^ p

private noncomputable def logistic (x : ℝ) : ℝ := Real.exp x / (1 + Real.exp x)

private theorem logistic_range (x : ℝ) : logistic x ∈ Ioo (0 : ℝ) 1 := by
  unfold logistic
  exact ⟨by positivity, (div_lt_iff₀ (by positivity)).mpr (by linarith)⟩

private theorem logistic_deriv (x : ℝ) :
    HasDerivAt logistic (logistic x * (1 - logistic x)) x := by
  have hx : 1 + Real.exp x ≠ 0 := by positivity
  have he := Real.hasDerivAt_exp x
  have h := he.div (he.const_add 1) hx
  convert h using 1
  dsimp only [logistic]
  field_simp [hx]

private theorem logistic_injective : Function.Injective logistic := by
  apply StrictMono.injective
  intro x y hxy
  have h := Real.exp_lt_exp.mpr hxy
  unfold logistic
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

private theorem logistic_image : logistic '' (univ : Set ℝ) = Ioo 0 1 := by
  ext x
  constructor
  · rintro ⟨y, _, rfl⟩
    exact logistic_range y
  · intro hx
    refine ⟨Real.log (x / (1 - x)), mem_univ _, ?_⟩
    have h1 := sub_pos.mpr hx.2
    rw [logistic, Real.exp_log (div_pos hx.1 h1)]
    have hdiv := div_pos hx.1 h1
    have hd : 1 + x / (1 - x) ≠ 0 := (by linarith : 0 < 1 + x / (1 - x)).ne'
    field_simp [h1.ne', hd]
    ring

private theorem logistic_beta_integrand (p t x : ℝ) :
    (↑(logistic x * (1 - logistic x)) : ℂ) *
      ((logistic x : ℂ) ^ ((p / 2 : ℝ) + (t : ℂ) * Complex.I - 1) *
        (1 - (logistic x : ℂ)) ^ ((p / 2 : ℝ) - (t : ℂ) * Complex.I - 1)) =
      (betaProfile p x : ℂ) * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) := by
  let y := logistic x
  let d := 1 + Real.exp x
  have hy : 0 < y := (logistic_range x).1
  have hy1 : 0 < 1 - y := sub_pos.mpr (logistic_range x).2
  have hd : 0 < d := by dsimp only [d]; positivity
  have hcomplement : 1 - y = 1 / d := by
    dsimp only [y, logistic, d]
    field_simp [show 1 + Real.exp x ≠ 0 by positivity]
    ring
  have hlogy : Real.log y = x - Real.log d := by
    change Real.log (Real.exp x / d) = _
    rw [Real.log_div (Real.exp_pos x).ne' hd.ne', Real.log_exp]
  have hlog1 : Real.log (1 - y) = -Real.log d := by
    rw [hcomplement, Real.log_div one_ne_zero hd.ne', Real.log_one, zero_sub]
  change (↑(y * (1 - y)) : ℂ) *
      ((y : ℂ) ^ ((p / 2 : ℝ) + (t : ℂ) * Complex.I - 1) *
        (1 - (y : ℂ)) ^ ((p / 2 : ℝ) - (t : ℂ) * Complex.I - 1)) =
      (betaProfile p x : ℂ) * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)
  have hbase : (↑(y * (1 - y)) : ℂ) =
      Complex.exp ((Real.log y + Real.log (1 - y) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_add, Real.exp_log hy, Real.exp_log hy1]
  have hp : (betaProfile p x : ℂ) =
      Complex.exp ((p * x / 2 - p * Real.log d : ℝ) : ℂ) := by
    change ((Real.exp (p * x / 2) / d ^ p : ℝ) : ℂ) = _
    rw [← Complex.ofReal_exp, Real.exp_sub, Real.rpow_def_of_pos hd, mul_comm (Real.log d)]
  have hz : (1 - (y : ℂ)) = ((1 - y : ℝ) : ℂ) := by push_cast; rfl
  rw [hbase, hz, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy1.ne'),
    ← Complex.ofReal_log hy.le, ← Complex.ofReal_log hy1.le, hp,
    ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [hlogy, hlog1]
  push_cast
  ring

/-- The positive-power Gamma product is the exact Fourier integral of the
real logistic profile. The strip continuation is a separate step. -/
theorem gamma_product_fourier {p : ℝ} (hp : 0 < p) (t : ℝ) :
    (∫ x : ℝ, (betaProfile p x : ℂ) * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) =
      (↑(‖Complex.Gamma ((p / 2 : ℝ) + (t : ℂ) * Complex.I)‖ ^ 2) : ℂ) /
        Complex.Gamma (p : ℂ) := by
  let u : ℂ := (p / 2 : ℝ) + (t : ℂ) * Complex.I
  let v : ℂ := (p / 2 : ℝ) - (t : ℂ) * Complex.I
  let g (s : ℝ) : ℂ := (s : ℂ) ^ (u - 1) * (1 - (s : ℂ)) ^ (v - 1)
  have h := integral_image_eq_integral_abs_deriv_smul (s := (univ : Set ℝ))
    MeasurableSet.univ (fun x _ => (logistic_deriv x).hasDerivWithinAt)
    logistic_injective.injOn g
  rw [logistic_image, Measure.restrict_univ] at h
  have h1 : (∫ s in Ioo (0 : ℝ) 1, g s) = Complex.betaIntegral u v := by
    rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num),
      integral_Ioc_eq_integral_Ioo]
  have h2 : (∫ x : ℝ, (betaProfile p x : ℂ) * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) =
      Complex.betaIntegral u v := by
    rw [← h1, h]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      have hη := logistic_range x
      change _ = |logistic x * (1 - logistic x)| • g (logistic x)
      rw [abs_of_pos (mul_pos hη.1 (sub_pos.mpr hη.2)), Complex.real_smul]
      exact (logistic_beta_integrand p t x).symm
  rw [h2, Complex.betaIntegral_eq_Gamma_mul_div u v
      (by simpa [u, Complex.mul_re] using (show 0 < p / 2 by positivity))
      (by simpa [v, Complex.mul_re] using (show 0 < p / 2 by positivity)),
    show u + v = (p : ℂ) by dsimp only [u, v]; push_cast; ring,
    show v = star u by dsimp only [u, v]; simp [Complex.conj_I]; ring,
    Complex.star_def, Complex.Gamma_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem betaProfile_integrable {p : ℝ} (hp : 0 < p) :
    Integrable (betaProfile p) := by
  have hc : Integrable (fun x => (betaProfile p x : ℂ)) := by
    apply Integrable.of_integral_ne_zero
    have hh := gamma_product_fourier hp 0
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one, add_zero] at hh
    rw [hh]
    have hu : 0 < ((p / 2 : ℝ) : ℂ).re := by simp only [Complex.ofReal_re]; positivity
    have hv : 0 < (p : ℂ).re := hp
    exact div_ne_zero
      (Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr
        (Complex.Gamma_ne_zero_of_re_pos hu)))) (Complex.Gamma_ne_zero_of_re_pos hv)
  simpa only [Complex.ofReal_re] using hc.re

noncomputable def gammaDensity (p t : ℝ) : ℝ :=
  (2 : ℝ) ^ (p - 1) * ‖Complex.Gamma ((p / 2 : ℝ) + (t : ℂ) * Complex.I)‖ ^ 2 /
    (Real.pi * Real.Gamma p)

theorem gammaDensity_pos {p : ℝ} (hp : 0 < p) (t : ℝ) : 0 < gammaDensity p t := by
  have h : 0 < (((p / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I).re := by
    simp [Complex.mul_re]
    positivity
  unfold gammaDensity
  exact div_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (sq_pos_of_pos (norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos h))))
    (mul_pos Real.pi_pos (Real.Gamma_pos_of_pos hp))

noncomputable def imageDensity (p L s : ℝ) : ℝ :=
  (2 : ℝ) ^ (p - 1) * Real.pi ^ (p - 2) * L ^ (1 - p) / Real.Gamma p *
    Real.sinh (L * s / 2) * ‖Complex.Gamma ((p / 2 : ℝ) + ((L * s / (2 * Real.pi) : ℝ) : ℂ) *
      Complex.I)‖ ^ 2

theorem imageDensity_pos {p L s : ℝ} (hp : 0 < p) (hL : 0 < L) (hs : 0 < s) :
    0 < imageDensity p L s := by
  have h : 0 < (((p / 2 : ℝ) : ℂ) + ((L * s / (2 * Real.pi) : ℝ) : ℂ) * Complex.I).re := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero] using (show 0 < p / 2 by positivity)
  unfold imageDensity
  apply mul_pos _ (sq_pos_of_pos (norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos h)))
  apply mul_pos
  · exact div_pos (mul_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (Real.rpow_pos_of_pos Real.pi_pos _)) (Real.rpow_pos_of_pos hL _)) (Real.Gamma_pos_of_pos hp)
  · exact Real.sinh_pos_iff.mpr (by positivity)

theorem betaProfile_eq_cosh (p x : ℝ) :
    betaProfile p x = (2 * Real.cosh (x / 2)) ^ (-p) := by
  have hc : 2 * Real.cosh (x / 2) = Real.exp (-(x / 2)) * (1 + Real.exp x) := by
    rw [Real.cosh_eq, mul_add, mul_one, ← Real.exp_add,
      show -(x / 2) + x = x / 2 by ring]
    ring
  rw [betaProfile, hc, Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (by positivity),
    ← Real.exp_sub, Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp]
  congr 1
  ring

theorem gammaDensity_even (p : ℝ) : Function.Even (gammaDensity p) := by
  intro t
  have h : ((p / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I =
      star (((p / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
    simp [Complex.conj_I]
  rw [gammaDensity, gammaDensity, h, Complex.star_def, Complex.Gamma_conj, ← Complex.star_def, norm_star]

private theorem gamma_half_norm (t : ℝ) :
    ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * t) := by
  let z : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  have hconj : 1 - z = star z := by
    dsimp only [z]
    simp [Complex.conj_I]
    ring
  have hs : Complex.sin ((Real.pi : ℂ) * z) = (Real.cosh (Real.pi * t) : ℂ) := by
    rw [show (Real.pi : ℂ) * z = ((Real.pi * t : ℝ) : ℂ) * Complex.I + (Real.pi : ℂ) / 2 by
      dsimp only [z]; push_cast; ring,
      Complex.sin_add_pi_div_two, Complex.cos_mul_I, ← Complex.ofReal_cosh]
  have h := Complex.Gamma_mul_Gamma_one_sub z
  rw [hconj, Complex.star_def, Complex.Gamma_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, hs,
    ← Complex.ofReal_div] at h
  exact Complex.ofReal_injective h

/-- The literal-one Gamma image density is the tanh law used by the
vendored Newtonian development. -/
theorem imageDensity_one (L s : ℝ) :
    imageDensity 1 L s = Real.tanh (L * s / 2) := by
  unfold imageDensity
  simp only [sub_self, Real.rpow_zero, one_mul, Real.Gamma_one, div_one,
    show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one]
  rw [gamma_half_norm, Real.tanh_eq_sinh_div_cosh,
    show Real.pi * (L * s / (2 * Real.pi)) = L * s / 2 by field_simp [Real.pi_pos.ne']]
  field_simp [Real.pi_pos.ne', (Real.cosh_pos _).ne']

end ACS12.GammaMeasure

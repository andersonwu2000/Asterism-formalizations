import ACS12.DeficitProfile
import ACS12.GammaMeasure

/-! The subunit Gamma density as a sine transform of the hyperbolic
profile. -/

namespace ACS12.GammaDeficit

open MeasureTheory Set Filter

noncomputable def normalizedImage (p u : ℝ) : ℝ :=
  Real.sinh (Real.pi * u) *
    ‖Complex.Gamma ((p / 2 : ℝ) + (u : ℂ) * Complex.I)‖ ^ 2 / Real.pi

private theorem sinhProfile_eq_exp {p t : ℝ} (ht : 0 < t) :
    sinhProfile p t = Real.exp (-(p / 2) * t) * (1 - Real.exp (-t)) ^ (-p) := by
  have hbase : 2 * Real.sinh (t / 2) = Real.exp (t / 2) * (1 - Real.exp (-t)) := by
    rw [Real.sinh_eq, mul_sub, mul_one, ← Real.exp_add,
      show t / 2 + -t = -(t / 2) by ring]
    ring
  have he : 0 < 1 - Real.exp (-t) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht))
  rw [sinhProfile, hbase, Real.mul_rpow (Real.exp_pos _).le he.le, ← Real.exp_mul]
  congr 2
  ring

private theorem exp_neg_image_Ioi :
    (fun t : ℝ => Real.exp (-t)) '' Ioi 0 = Ioo 0 1 := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)⟩
  · intro hx
    refine ⟨-Real.log x, neg_pos.mpr (Real.log_neg hx.1 hx.2), ?_⟩
    simp only [neg_neg]
    exact Real.exp_log hx.1

private theorem sinh_beta_integrand {p u t : ℝ} (ht : 0 < t) :
    (Real.exp (-t) : ℂ) * ((Real.exp (-t) : ℂ) ^ ((p / 2 : ℝ) + (u : ℂ) * Complex.I - 1) *
      (1 - (Real.exp (-t) : ℂ)) ^ (((1 - p : ℝ) - 1 : ℝ) : ℂ)) =
      (sinhProfile p t : ℂ) * Complex.exp ((-(u * t) : ℝ) * Complex.I) := by
  have hbase : 0 < 1 - Real.exp (-t) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht))
  rw [show (1 - (Real.exp (-t) : ℂ)) = ((1 - Real.exp (-t) : ℝ) : ℂ) by push_cast; rfl]
  rw [← Complex.ofReal_cpow hbase.le, show (1 - p : ℝ) - 1 = -p by ring,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
    ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp, Complex.ofReal_exp]
  rw [mul_left_comm, ← mul_assoc, ← Complex.exp_add]
  rw [sinhProfile_eq_exp ht, Complex.ofReal_mul, Complex.ofReal_exp]
  rw [mul_assoc, mul_comm _ (Complex.exp ((↑(-(u * t)) : ℂ) * Complex.I)), ← mul_assoc,
    ← Complex.exp_add]
  congr 2
  push_cast
  ring

private theorem sinhProfile_beta {p : ℝ} (hp : 0 < p) (hp₁ : p < 1) (u : ℝ) :
    (∫ t : ℝ in Ioi 0, (sinhProfile p t : ℂ) * Complex.exp ((-(u * t) : ℝ) * Complex.I)) =
      Complex.Gamma ((p / 2 : ℝ) + (u : ℂ) * Complex.I) * Complex.Gamma (1 - (p : ℂ)) /
        Complex.Gamma (1 - star ((p / 2 : ℝ) + (u : ℂ) * Complex.I)) := by
  let z : ℂ := (p / 2 : ℝ) + (u : ℂ) * Complex.I
  let w : ℂ := (1 - p : ℝ)
  let g (x : ℝ) : ℂ := (x : ℂ) ^ (z - 1) * (1 - (x : ℂ)) ^ (w - 1)
  have hder (t : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-t)) t := by
    simpa only [mul_neg, mul_one] using ((hasDerivAt_id t).neg.exp)
  have h := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ)) measurableSet_Ioi
    (fun t _ => (hder t).hasDerivWithinAt)
    ((Real.exp_injective.comp neg_injective).injOn) g
  rw [exp_neg_image_Ioi] at h
  have hβ : (∫ x : ℝ in Ioo 0 1, g x) = Complex.betaIntegral z w := by
    rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num),
      integral_Ioc_eq_integral_Ioo]
  have hg : (∫ t : ℝ in Ioi 0,
      (sinhProfile p t : ℂ) * Complex.exp ((-(u * t) : ℝ) * Complex.I)) =
      Complex.betaIntegral z w := by
    rw [← hβ, h]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change _ = |(-Real.exp (-t))| • g (Real.exp (-t))
    rw [abs_neg, abs_of_pos (Real.exp_pos _), Complex.real_smul]
    simpa only [g, z, w, Complex.ofReal_sub, Complex.ofReal_one] using
      (sinh_beta_integrand (p := p) (u := u) ht).symm
  have hz : 0 < z.re := by simp [z, Complex.mul_re]; positivity
  have hw : 0 < w.re := sub_pos.mpr hp₁
  have hz' : z + w = 1 - star z := by
    dsimp only [z, w]
    simp only [Complex.star_def, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I,
      Complex.ofReal_sub, Complex.ofReal_one]
    push_cast
    ring
  rw [hg, Complex.betaIntegral_eq_Gamma_mul_div z w hz hw, hz']
  simp only [z, w, Complex.ofReal_sub, Complex.ofReal_one]

theorem sinhProfile_integrable {p : ℝ} (hp : 0 < p) (hp₁ : p < 1) :
    IntegrableOn (sinhProfile p) (Ioi 0) := by
  have hi : IntegrableOn (fun t : ℝ => (sinhProfile p t : ℂ)) (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    have h := sinhProfile_beta hp hp₁ 0
    simp only [zero_mul, neg_zero, Complex.ofReal_zero, Complex.exp_zero, mul_one, add_zero] at h
    rw [h]
    refine div_ne_zero (mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos (by simpa using (show
      0 < p / 2 by positivity))) (Complex.Gamma_ne_zero_of_re_pos (by simpa using sub_pos.mpr hp₁)))
      (Complex.Gamma_ne_zero_of_re_pos ?_)
    simp
    linarith
  simpa only [Complex.ofReal_re] using hi.re

private theorem im_sin_conj {p u : ℝ} :
    (Complex.sin ((Real.pi : ℂ) * star ((p / 2 : ℝ) + (u : ℂ) * Complex.I))).im =
      -Real.cos (Real.pi * p / 2) * Real.sinh (Real.pi * u) := by
  have h : (Real.pi : ℂ) * star ((p / 2 : ℝ) + (u : ℂ) * Complex.I) =
      ((Real.pi * p / 2 : ℝ) : ℂ) + ((-(Real.pi * u) : ℝ) : ℂ) * Complex.I := by
    simp [Complex.conj_I]
    ring
  rw [h, Complex.sin_add, Complex.cos_mul_I, Complex.sin_mul_I,
    ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sinh, ← Complex.ofReal_cosh]
  simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_im, mul_one, mul_zero, zero_mul, zero_add, add_zero, Real.sinh_neg, mul_neg, neg_mul]

/-- The exact sine transform of the hyperbolic profile in the subunit
range, with the original Gamma normalization. -/
theorem sinhProfile_sine {p : ℝ} (hp : 0 < p) (hp₁ : p < 1) (u : ℝ) :
    (∫ t : ℝ in Ioi 0, sinhProfile p t * Real.sin (u * t)) =
      Real.Gamma (1 - p) * Real.cos (Real.pi * p / 2) * normalizedImage p u := by
  let z : ℂ := (p / 2 : ℝ) + (u : ℂ) * Complex.I
  let f (t : ℝ) := (sinhProfile p t : ℂ) * Complex.exp ((-(u * t) : ℝ) * Complex.I)
  have hbeta : (∫ t : ℝ in Ioi 0, f t) =
      Complex.Gamma z * Complex.Gamma (1 - (p : ℂ)) / Complex.Gamma (1 - star z) :=
    sinhProfile_beta hp hp₁ u
  have hz : 0 < z.re := by simp [z, Complex.mul_re]; positivity
  have hzs : 0 < (star z).re := by simpa
  have hw : 0 < (1 - (p : ℂ)).re := by simpa using sub_pos.mpr hp₁
  have hd : 0 < (1 - star z).re := by simp [z, Complex.mul_re]; linarith
  have hΓd := Complex.Gamma_ne_zero_of_re_pos hd
  have hΓs := Complex.Gamma_ne_zero_of_re_pos hzs
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hf : IntegrableOn f (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [hbeta]
    exact div_ne_zero (mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos hz)
      (Complex.Gamma_ne_zero_of_re_pos hw)) hΓd
  have hreflection := Complex.Gamma_mul_Gamma_one_sub (star z)
  have hs : Complex.sin ((Real.pi : ℂ) * star z) ≠ 0 := by
    intro h
    rw [h, div_zero] at hreflection
    exact (mul_ne_zero hΓs hΓd) hreflection
  have hinv : (Complex.Gamma (1 - star z))⁻¹ =
      Complex.Gamma (star z) * Complex.sin ((Real.pi : ℂ) * star z) / (Real.pi : ℂ) := by
    apply (eq_div_iff hpi).mpr
    rw [inv_mul_eq_div]
    apply (div_eq_iff hΓd).mpr
    calc
      _ = Complex.Gamma (star z) * Complex.Gamma (1 - star z) *
          Complex.sin ((Real.pi : ℂ) * star z) := ((eq_div_iff hs).mp hreflection).symm
      _ = _ := by ring
  have hComplex : (∫ t : ℝ in Ioi 0, f t) =
      ((‖Complex.Gamma z‖ ^ 2 * Real.Gamma (1 - p) / Real.pi : ℝ) : ℂ) *
        Complex.sin ((Real.pi : ℂ) * star z) := by
    rw [hbeta, div_eq_mul_inv, hinv]
    calc
      _ = (Complex.Gamma z * Complex.Gamma (star z)) * Complex.Gamma (1 - (p : ℂ)) *
        Complex.sin ((Real.pi : ℂ) * star z) / (Real.pi : ℂ) := by ring
      _ = _ := by
        rw [Complex.star_def, Complex.Gamma_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq,
          show 1 - (p : ℂ) = ((1 - p : ℝ) : ℂ) by push_cast; rfl,
          Complex.Gamma_ofReal, Complex.ofReal_div, Complex.ofReal_mul]
        ring
  have hIm := congrArg Complex.im hComplex
  have hInt : (∫ t : ℝ in Ioi 0, (f t).im) = (∫ t : ℝ in Ioi 0, f t).im := integral_im hf
  rw [← hInt, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    at hIm
  change (∫ t : ℝ in Ioi 0, (f t).im) =
    ‖Complex.Gamma z‖ ^ 2 * Real.Gamma (1 - p) / Real.pi *
      (Complex.sin ((Real.pi : ℂ) * star ((p / 2 : ℝ) + (u : ℂ) * Complex.I))).im at hIm
  have hF (t : ℝ) : (f t).im = -(sinhProfile p t * Real.sin (u * t)) := by
    unfold f
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_im, Complex.I_re, Real.sin_neg, mul_zero, zero_mul, mul_one, add_zero,
      zero_add, mul_neg]
  simp_rw [hF, integral_neg, im_sin_conj] at hIm
  calc
    _ = -(-(∫ t : ℝ in Ioi 0, sinhProfile p t * Real.sin (u * t))) := (neg_neg _).symm
    _ = _ := by rw [hIm]; unfold normalizedImage; dsimp only [z]; ring

end ACS12.GammaDeficit

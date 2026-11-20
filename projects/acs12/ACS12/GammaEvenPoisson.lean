import ACS12.GammaStrip
import ACS12.PoissonKernel

/-! The even Poisson boundary for the Gamma density ordering. -/

namespace ACS12.GammaMeasure

open MeasureTheory Set Filter
open scoped FourierTransform

noncomputable def evenGammaProfile (t : ℝ) : ℝ :=
  (Real.pi / 2) * gammaDensity 2 (t / (2 * Real.pi))

noncomputable def evenGammaBoundary (x : ℝ) : ℝ :=
  (2 * Real.pi) ^ 2 * betaProfile 2 (2 * Real.pi * x)

theorem evenGammaProfile_integrable : Integrable evenGammaProfile := by
  have h := gammaDensity_exp_integrable (p := 2) (y := 0) (by norm_num) (by simpa using Real.pi_pos)
  simp only [mul_zero, Real.exp_zero, mul_one] at h
  have hc : 2 * Real.pi ≠ 0 := by positivity
  exact (((integrable_comp_mul_left_iff (gammaDensity 2) (inv_ne_zero hc)).mpr h).const_mul
    (Real.pi / 2)).congr (Eventually.of_forall fun t => by
      simp only [evenGammaProfile, div_eq_mul_inv, mul_comm t])

theorem integral_evenGammaProfile_exp (x : ℝ) :
    (∫ t : ℝ, (evenGammaProfile t : ℂ) * Complex.exp ((x : ℂ) * (t : ℂ) * Complex.I)) =
      (evenGammaBoundary x : ℂ) := by
  let f (x : ℝ) := (betaProfile 2 x : ℂ)
  let c := 2 * Real.pi
  have hc : 0 < c := by dsimp [c]; positivity
  have hf : Integrable f := (betaProfile_integrable (p := 2) (by norm_num)).ofReal
  have hFc : 𝓕 f = fun w : ℝ => (evenGammaProfile (c ^ 2 * w) : ℂ) := by
    funext w
    rw [Real.fourier_real_eq_integral_exp_smul]
    have hEq :
        (∫ x : ℝ, Complex.exp (↑(-2 * Real.pi * x * w) * Complex.I) • f x) =
        ∫ x : ℝ, (betaProfile 2 x : ℂ) * Complex.exp ((↑(-c * w) : ℂ) * (x : ℂ) * Complex.I) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp only [f, smul_eq_mul, mul_comm _ (↑(betaProfile 2 x) : ℂ)]
        congr 2
        dsimp only [c]
        push_cast
        ring
    rw [hEq, gamma_product_fourier (by norm_num : 0 < (2 : ℝ))]
    have hΓ : Complex.Gamma 2 = 1 := by norm_num [← Complex.Gamma_nat_eq_factorial 1]
    simp only [show (2 : ℝ) / 2 = 1 by norm_num, show (↑(2 : ℝ) : ℂ) = 2 by norm_num,
      hΓ, div_one, evenGammaProfile]
    have hh : c ^ 2 * w / (2 * Real.pi) = c * w := by change c ^ 2 * w / c = _; field_simp
    rw [hh, ← gammaDensity_even (2 : ℝ) (c * w), ← neg_mul]
    unfold gammaDensity
    simp only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.Gamma_two, mul_one,
      show (2 : ℝ) / 2 = 1 by norm_num]
    congr 1
    field_simp [Real.pi_ne_zero]
    rw [mul_comm Complex.I, mul_comm w c]
  have hFi : Integrable (𝓕 f) := by
    rw [hFc]
    exact ((integrable_comp_mul_left_iff evenGammaProfile (pow_ne_zero 2 hc.ne')).mpr
      evenGammaProfile_integrable).ofReal
  have hCont : Continuous f := by
    unfold f
    have hForm : betaProfile 2 = fun x : ℝ => ((2 * Real.cosh (x / 2)) ^ (2 : ℕ))⁻¹ := by
      funext x
      rw [betaProfile_eq_cosh, Real.rpow_neg (by positivity), Real.rpow_two]
    rw [hForm]
    apply Complex.continuous_ofReal.comp
    exact Continuous.inv₀ (by fun_prop) (fun x => by positivity)
  have h := hf.fourierInv_fourier_eq hFi (hCont.continuousAt (x := c * x))
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul, hFc] at h
  let g (t : ℝ) := (evenGammaProfile t : ℂ) * Complex.exp ((x : ℂ) * (t : ℂ) * Complex.I)
  have he :
      (∫ t : ℝ, Complex.exp (↑(-2 * Real.pi * t * -(c * x)) * Complex.I) •
        (↑(evenGammaProfile (c ^ 2 * t)) : ℂ)) =
      ∫ t : ℝ, g (c ^ 2 * t) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by
      simp only [g, smul_eq_mul, mul_comm _ (↑(evenGammaProfile (c ^ 2 * t)) : ℂ)]
      congr 2
      dsimp only [c]
      push_cast
      ring
  rw [he, Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr (pow_pos hc 2))] at h
  change (↑((c ^ 2)⁻¹) : ℂ) * (∫ t : ℝ, g t) = f (c * x) at h
  have hRes : (∫ t : ℝ, g t) = (↑(c ^ 2) : ℂ) * f (c * x) := by
    calc
      _ = (↑(c ^ 2) : ℂ) * ((↑((c ^ 2)⁻¹) : ℂ) * ∫ t : ℝ, g t) := by
        rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (pow_ne_zero 2 hc.ne'),
          Complex.ofReal_one, one_mul]
      _ = _ := by rw [h]
  rw [hRes, evenGammaBoundary, ← Complex.ofReal_mul]

theorem evenGammaBoundary_eq (x : ℝ) :
    evenGammaBoundary x = Real.pi ^ 2 / Real.cosh (Real.pi * x) ^ 2 := by
  rw [evenGammaBoundary, betaProfile_eq_cosh, show 2 * Real.pi * x / 2 = Real.pi * x by ring,
    show (-(2 : ℝ)) = -(2 : ℝ) by rfl, Real.rpow_neg (by positivity), Real.rpow_two]
  field_simp [show (2 * Real.cosh (Real.pi * x)) ≠ 0 by positivity]

noncomputable def smoothedEvenGamma (a x : ℝ) : ℝ :=
  ∫ y : ℝ, Poisson.kernel a y * evenGammaBoundary (x - y)

/-- Shift of the real Gamma boundary under the exact Poisson law. -/
theorem smoothedEvenGamma_eq {a : ℝ} (ha : 0 < a) (x : ℝ) :
    (smoothedEvenGamma a x : ℂ) =
      ∫ t : ℝ, ((evenGammaProfile t * Poisson.damping a t : ℝ) : ℂ) *
        Complex.exp ((x : ℂ) * (t : ℂ) * Complex.I) := by
  let f (y t : ℝ) := (Poisson.kernel a y : ℂ) *
    ((evenGammaProfile t : ℂ) * Complex.exp (((x - y : ℝ) : ℂ) * (t : ℂ) * Complex.I))
  have hI : Integrable (Function.uncurry f) ((volume : Measure ℝ).prod volume) := by
    refine ((Poisson.integrable_kernel ha).norm.mul_prod evenGammaProfile_integrable.norm).mono' ?_ ?_
    · have hE : Measurable evenGammaProfile :=
        (continuous_const.mul ((continuous_gammaDensity (by norm_num : 0 < (2 : ℝ))).comp
          (by fun_prop))).measurable
      have hK : Measurable (Poisson.kernel a) := by unfold Poisson.kernel; fun_prop
      have hK' : Measurable (fun z : ℝ × ℝ => Poisson.kernel a z.1) := hK.comp measurable_fst
      have hE' : Measurable (fun z : ℝ × ℝ => evenGammaProfile z.2) := hE.comp measurable_snd
      unfold Function.uncurry f
      exact (by fun_prop (disch := assumption) : Measurable _).aestronglyMeasurable
    · exact Eventually.of_forall fun z => by
        dsimp only [Function.uncurry, f]
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_exp]
        simp [Complex.mul_re, Complex.mul_im]
  calc
    _ = ∫ y : ℝ, ((Poisson.kernel a y * evenGammaBoundary (x - y) : ℝ) : ℂ) :=
      (integral_ofReal (μ := volume) (f := fun y : ℝ =>
        Poisson.kernel a y * evenGammaBoundary (x - y))).symm
    _ = ∫ y : ℝ, ∫ t : ℝ, f y t := by
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        dsimp only [f]
        rw [Complex.ofReal_mul, ← integral_evenGammaProfile_exp]
        exact (integral_const_mul (μ := volume) (Poisson.kernel a y : ℂ)
          (fun t : ℝ => (evenGammaProfile t : ℂ) *
            Complex.exp (((x - y : ℝ) : ℂ) * (t : ℂ) * Complex.I))).symm
    _ = ∫ t : ℝ, ∫ y : ℝ, f y t := integral_integral_swap hI
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun t => by
        let c : ℂ := (evenGammaProfile t : ℂ) *
          Complex.exp ((x : ℂ) * (t : ℂ) * Complex.I)
        have he (y : ℝ) : f y t =
            c * ((Poisson.kernel a y : ℂ) * Complex.exp ((y : ℂ) * (-t : ℝ) * Complex.I)) := by
          dsimp only [f, c]
          rw [Complex.ofReal_sub, sub_mul, sub_mul, Complex.exp_sub, div_eq_mul_inv, ← Complex.exp_neg]
          push_cast
          ring
        simp_rw [he]
        calc
          _ = c * (∫ y : ℝ, (Poisson.kernel a y : ℂ) *
              Complex.exp ((y : ℂ) * (-t : ℝ) * Complex.I)) :=
            integral_const_mul (μ := volume) c _
          _ = _ := by
            rw [Poisson.integral_kernel_exp ha (-t), Poisson.damping, abs_neg,
              ← Poisson.damping, Complex.ofReal_mul]
            dsimp only [c]
            ring

end ACS12.GammaMeasure

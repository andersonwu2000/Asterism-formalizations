import ACS12.GammaPoissonOrder
import ACS12.GammaOrder

/-! The actual positive-frequency Gamma moment and its ordered Poisson form. -/

namespace ACS12.GammaMeasure

open MeasureTheory Set Filter

theorem evenGammaProfile_pos (t : ℝ) : 0 < evenGammaProfile t :=
  mul_pos (by positivity) (gammaDensity_pos (by norm_num) _)

theorem evenGammaProfile_eq {t : ℝ} (ht : 0 < t) :
    evenGammaProfile t = t * Real.exp (-(1 / 2 : ℝ) * t) / (1 - Real.exp (-t)) := by
  have h := imageDensity_two (L := 1) zero_lt_one ht
  rw [imageDensity_eq_spectral 2 zero_lt_one] at h
  simp only [div_one, one_mul, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] at h
  have hS : Real.sinh (t / 2) * 2 * Real.exp (-t / 2) = 1 - Real.exp (-t) := by
    rw [Real.sinh_eq]
    have h₁ : Real.exp (t / 2) * Real.exp (-t / 2) = 1 := by
      rw [← Real.exp_add, show t / 2 + -t / 2 = 0 by ring, Real.exp_zero]
    have h₂ : Real.exp (-(t / 2)) * Real.exp (-t / 2) = Real.exp (-t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    linear_combination h₁ - h₂
  have hP : 0 < Real.sinh (t / 2) := Real.sinh_pos_iff.mpr (by positivity)
  calc
    evenGammaProfile t = t / (2 * Real.sinh (t / 2)) := by
      unfold evenGammaProfile
      apply (eq_div_iff (mul_ne_zero two_ne_zero hP.ne')).mpr
      linarith only [h]
    _ = _ := by
      rw [show -(1 / 2 : ℝ) * t = -t / 2 by ring, ← hS]
      field_simp [hP.ne', (Real.exp_pos (-t / 2)).ne']

private theorem evenGammaProfile_even : Function.Even evenGammaProfile := by
  intro t
  unfold evenGammaProfile
  rw [neg_div, gammaDensity_even]

theorem gammaCosine_moment {q : ℝ} (hq : 1 / 2 < q) (x : ℝ) :
    (∫ t : ℝ in Ioi 0, evenGammaProfile t * Real.exp (-(q - 1 / 2) * t) * Real.cos (x * t)) =
      smoothedEvenGamma (q - 1 / 2) x / 2 := by
  let a := q - 1 / 2
  have ha : 0 < a := sub_pos.mpr hq
  let f (t : ℝ) := ((evenGammaProfile t * Poisson.damping a t : ℝ) : ℂ) *
    Complex.exp ((x : ℂ) * (t : ℂ) * Complex.I)
  have hF : Integrable f := by
    have hE : Measurable evenGammaProfile :=
      (continuous_const.mul ((continuous_gammaDensity (by norm_num : 0 < (2 : ℝ))).comp
        (by fun_prop))).measurable
    refine evenGammaProfile_integrable.mono' ?_ ?_
    · unfold f Poisson.damping
      exact (by fun_prop (disch := assumption) : Measurable _).aestronglyMeasurable
    · exact Eventually.of_forall fun t => by
        dsimp only [f, Poisson.damping]
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg
          (mul_nonneg (evenGammaProfile_pos t).le (Real.exp_pos _).le), Complex.norm_exp]
        simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero,
          zero_mul, add_zero, sub_zero, Complex.I_im, mul_one, Real.exp_zero]
        exact mul_le_of_le_one_right (evenGammaProfile_pos t).le
          (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha.le) (abs_nonneg _)))
  have hRe (t : ℝ) : (f t).re = evenGammaProfile t * Poisson.damping a t * Real.cos (x * t) := by
    have he : (Complex.exp ((x : ℂ) * (t : ℂ) * Complex.I)).re = Real.cos (x * t) := by
      rw [← Complex.ofReal_mul, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
    unfold f
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, he]
  have hEven : Function.Even (fun t => (f t).re) := by
    intro t
    change (f (-t)).re = (f t).re
    rw [hRe, hRe, evenGammaProfile_even, Poisson.damping, Poisson.damping, abs_neg, mul_neg,
      Real.cos_neg]
  have h := congrArg Complex.re (smoothedEvenGamma_eq ha x)
  change smoothedEvenGamma a x = (∫ t : ℝ, f t).re at h
  have hIR : (∫ t : ℝ, (f t).re) = (∫ t : ℝ, f t).re := integral_re hF
  rw [← hIR] at h
  have hSplit := setIntegral_union (Iic_disjoint_Ioi le_rfl)
    (measurableSet_Ioi (a := (0 : ℝ))) hF.re.integrableOn hF.re.integrableOn
  rw [Iic_union_Ioi, Measure.restrict_univ] at hSplit
  change (∫ t : ℝ, (f t).re) =
    (∫ t : ℝ in Iic 0, (f t).re) + ∫ t : ℝ in Ioi 0, (f t).re at hSplit
  have hReflect : (∫ t : ℝ in Ioi 0, (f t).re) = ∫ t : ℝ in Iic 0, (f t).re := by
    calc
      _ = ∫ t : ℝ in Ioi 0, (f (-t)).re := by
        apply setIntegral_congr_fun measurableSet_Ioi
        exact fun t _ => (hEven t).symm
      _ = _ := by simpa only [neg_zero] using integral_comp_neg_Ioi (0 : ℝ) (fun t => (f t).re)
  rw [hSplit, ← hReflect, ← two_mul] at h
  have he : (∫ t : ℝ in Ioi 0, (f t).re) =
      ∫ t : ℝ in Ioi 0, evenGammaProfile t * Real.exp (-(q - 1 / 2) * t) * Real.cos (x * t) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [hRe, Poisson.damping, abs_of_pos ht]
  rw [← he]
  linarith

end ACS12.GammaMeasure

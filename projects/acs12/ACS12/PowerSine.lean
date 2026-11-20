import CenteredCircle.EulerIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Abel regularization of the positive-frequency power sine transform. -/

namespace ACS12.GammaDeficit

open MeasureTheory Set Filter
open scoped Topology

noncomputable def dampedPowerSine (p ε u : ℝ) : ℝ :=
  ∫ t : ℝ in Ioi 0, t ^ (-p) * Real.exp (-ε * t) * Real.sin (u * t)

noncomputable def sineScale (p : ℝ) : ℝ :=
  Real.Gamma (1 - p) * Real.cos (Real.pi * p / 2)

theorem sineScale_pos {p : ℝ} (hp : 0 < p) (hp₁ : p < 1) : 0 < sineScale p := by
  unfold sineScale
  apply mul_pos (Real.Gamma_pos_of_pos (sub_pos.mpr hp₁))
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> nlinarith [Real.pi_pos, mul_pos Real.pi_pos hp,
    mul_pos Real.pi_pos (sub_pos.mpr hp₁)]

theorem exp_sine_integral {c : ℝ} (hc : 0 < c) (u : ℝ) :
    (∫ t : ℝ in Ioi 0, Real.exp (-c * t) * Real.sin (u * t)) = u / (c ^ 2 + u ^ 2) := by
  let z : ℂ := -(c : ℂ) + (u : ℂ) * Complex.I
  have hz : z.re < 0 := by simpa [z, Complex.mul_re] using neg_neg_of_pos hc
  have hi := integrableOn_exp_mul_complex_Ioi hz 0
  have h := integral_exp_mul_complex_Ioi hz 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero] at h
  have him := congrArg Complex.im h
  have hm : (∫ t : ℝ in Ioi 0, (Complex.exp (z * (t : ℂ))).im) =
      (∫ t : ℝ in Ioi 0, Complex.exp (z * (t : ℂ))).im := integral_im hi
  rw [← hm] at him
  have hpoint (t : ℝ) :
      (Complex.exp (z * (t : ℂ))).im = Real.exp (-c * t) * Real.sin (u * t) := by
    rw [show z * (t : ℂ) = ((-c * t : ℝ) : ℂ) + ((u * t : ℝ) : ℂ) * Complex.I by
      dsimp [z]; push_cast; ring,
      Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, zero_add,
      add_zero]
  simp_rw [hpoint] at him
  rw [him, Complex.div_im, Complex.normSq_apply]
  simp [z, Complex.mul_re, Complex.mul_im, pow_two, neg_div]

theorem gamma_exp_integral {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    (∫ x : ℝ in Ioi 0, x ^ (a - 1) * Real.exp (-c * x)) =
      Real.Gamma a * c ^ (-a) := by
  rw [show (fun x : ℝ => x ^ (a - 1) * Real.exp (-c * x)) =
    fun x => x ^ (a - 1) * Real.exp (-(c * x)) by funext x; rw [neg_mul],
    Real.integral_rpow_mul_exp_neg_mul_Ioi ha hc, Real.div_rpow zero_le_one hc.le,
    Real.one_rpow, Real.rpow_neg hc.le, div_eq_mul_inv]
  ring

theorem integrable_gamma_exp {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => x ^ (a - 1) * Real.exp (-c * x)) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [gamma_exp_integral ha hc]
  exact (mul_pos (Real.Gamma_pos_of_pos ha) (Real.rpow_pos_of_pos hc _)).ne'

private theorem dampedPowerSine_eq {p ε : ℝ} (hp : 0 < p) (hp₁ : p < 1)
    (hε : 0 < ε) (u : ℝ) :
    dampedPowerSine p ε u =
      (Real.Gamma p)⁻¹ * ∫ x : ℝ in Ioi 0, x ^ (p - 1) * (u / ((x + ε) ^ 2 + u ^ 2)) := by
  let ν := volume.restrict (Ioi (0 : ℝ))
  let G (z : ℝ × ℝ) := z.2 ^ (p - 1) * Real.exp (-z.2 * z.1) * Real.exp (-ε * z.1)
  let F (z : ℝ × ℝ) := G z * Real.sin (u * z.1)
  have hGm : Measurable G := by unfold G; fun_prop
  have hFm : Measurable F := hGm.mul (by fun_prop)
  have hGi : Integrable G (ν.prod ν) := by
    apply (integrable_prod_iff hGm.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      refine ((integrable_gamma_exp hp ht).mul_const (Real.exp (-ε * t))).congr ?_
      exact Eventually.of_forall fun x => by dsimp [G]; rw [show -t * x = -x * t by ring]
    · have houter : Integrable (fun t : ℝ => Real.Gamma p * (t ^ (-p) * Real.exp (-ε * t))) ν := by
        have h := (integrable_gamma_exp (sub_pos.mpr hp₁) hε).const_mul (Real.Gamma p)
        simpa only [sub_sub_cancel_left] using h
      refine houter.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht₀ : 0 < t := ht
      calc
        _ = (∫ x : ℝ in Ioi 0, x ^ (p - 1) * Real.exp (-t * x)) * Real.exp (-ε * t) := by
          rw [gamma_exp_integral hp ht₀]
          ring
        _ = ∫ x : ℝ in Ioi 0, G (t, x) := by
          rw [← integral_mul_const]
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x _
          dsimp [G]
          rw [show -t * x = -x * t by ring]
        _ = _ := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          change 0 < x at hx
          exact (Real.norm_of_nonneg (by dsimp [G]; positivity)).symm
  have hFi : Integrable F (ν.prod ν) := by
    refine hGi.mono' hFm.aestronglyMeasurable ?_
    have hpos : ∀ᵐ z : ℝ × ℝ ∂ν.prod ν, 0 < z.2 := by
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const measurable_snd)).mpr
      exact Eventually.of_forall fun _ => ae_restrict_mem measurableSet_Ioi
    filter_upwards [hpos] with z hz
    have hn : 0 ≤ G z := by dsimp [G]; positivity
    dsimp only [F]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hn]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (u * z.1)) hn
  have hrow_t : ∀ᵐ t ∂ν, (∫ x : ℝ, F (t, x) ∂ν) =
      Real.Gamma p * (t ^ (-p) * Real.exp (-ε * t) * Real.sin (u * t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht₀ : 0 < t := ht
    calc
      _ = (∫ x : ℝ in Ioi 0, x ^ (p - 1) * Real.exp (-t * x)) *
          (Real.exp (-ε * t) * Real.sin (u * t)) := by
        rw [← integral_mul_const]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x _
        dsimp [F, G]
        rw [show -x * t = -t * x by ring]
        ring
      _ = _ := by rw [gamma_exp_integral hp ht₀]; ring
  have hrow_x : ∀ᵐ x ∂ν, (∫ t : ℝ, F (t, x) ∂ν) =
      x ^ (p - 1) * (u / ((x + ε) ^ 2 + u ^ 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx₀ : 0 < x := hx
    calc
      _ = x ^ (p - 1) * ∫ t : ℝ in Ioi 0, Real.exp (-(x + ε) * t) * Real.sin (u * t) := by
        rw [← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t _
        dsimp [F, G]
        rw [show Real.exp (-(x + ε) * t) = Real.exp (-x * t) * Real.exp (-ε * t) by
          rw [← Real.exp_add]; congr 1; ring]
        ring
      _ = _ := by rw [exp_sine_integral (add_pos hx₀ hε)]
  have he : Real.Gamma p * dampedPowerSine p ε u =
      ∫ x : ℝ in Ioi 0, x ^ (p - 1) * (u / ((x + ε) ^ 2 + u ^ 2)) := by
    calc
      _ = ∫ t : ℝ, (∫ x : ℝ, F (t, x) ∂ν) ∂ν := by
        unfold dampedPowerSine
        rw [← integral_const_mul]
        exact integral_congr_ae (hrow_t.mono fun _ h => h.symm)
      _ = ∫ z, F z ∂ν.prod ν := (integral_prod F hFi).symm
      _ = ∫ x : ℝ, (∫ t : ℝ, F (t, x) ∂ν) ∂ν := integral_prod_symm F hFi
      _ = _ := integral_congr_ae hrow_x
  rw [← he, ← mul_assoc, inv_mul_cancel₀ (Real.Gamma_pos_of_pos hp).ne', one_mul]

private theorem unit_lorentz_integral {p : ℝ} (hp : 0 < p) (hp₁ : p < 1) :
    (∫ y : ℝ in Ioi 0, y ^ (p - 1) / (1 + y ^ 2)) =
      Real.pi / (2 * Real.sin (Real.pi * p / 2)) := by
  let f (x : ℝ) := x ^ (p / 2 - 1) / (1 + x)
  have hsub := integral_comp_rpow_Ioi_of_pos (g := f) (p := 2) (by norm_num)
  have he : (∫ y : ℝ in Ioi 0, 2 * (y ^ (p - 1) / (1 + y ^ 2))) =
      ∫ x : ℝ in Ioi 0, f x := by
    refine (setIntegral_congr_fun measurableSet_Ioi ?_).trans hsub
    intro y hy
    change 0 < y at hy
    simp only [f, smul_eq_mul, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    rw [← Real.rpow_mul hy.le, show (2 : ℝ) * (p / 2 - 1) = p - 2 by ring,
      Real.rpow_two, show y ^ (p - 1) = y ^ (p - 2) * y by
        rw [← Real.rpow_add_one hy.ne', show p - 2 + 1 = p - 1 by ring]]
    ring
  have hEuler := CenteredCircle.AllN.euler_integral (b := p / 2) (by positivity) (by linarith)
  change (∫ x : ℝ in Ioi 0, f x) = _ at hEuler
  rw [integral_const_mul, hEuler, show Real.pi * (p / 2) = Real.pi * p / 2 by ring] at he
  calc
    _ = (Real.pi / Real.sin (Real.pi * p / 2)) / 2 := by linarith
    _ = _ := by rw [div_div, mul_comm]

private theorem lorentz_integral {p u : ℝ} (hp : 0 < p) (hp₁ : p < 1) (hu : 0 < u) :
    (∫ x : ℝ in Ioi 0, x ^ (p - 1) * (u / (x ^ 2 + u ^ 2))) =
      u ^ (p - 1) * (Real.pi / (2 * Real.sin (Real.pi * p / 2))) := by
  let f (x : ℝ) := x ^ (p - 1) * (u / (x ^ 2 + u ^ 2))
  have hscale := integral_comp_mul_left_Ioi f 0 hu
  simp only [mul_zero, smul_eq_mul] at hscale
  change (∫ x : ℝ in Ioi 0, f x) = _
  calc
    _ = u * ∫ y : ℝ in Ioi 0, f (u * y) := by
      rw [hscale, ← mul_assoc, mul_inv_cancel₀ hu.ne', one_mul]
    _ = ∫ y : ℝ in Ioi 0, u * f (u * y) := (integral_const_mul u _).symm
    _ = ∫ y : ℝ in Ioi 0, u ^ (p - 1) * (y ^ (p - 1) / (1 + y ^ 2)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      change 0 < y at hy
      dsimp only [f]
      rw [Real.mul_rpow hu.le hy.le, mul_pow]
      field_simp [hu.ne', (show 0 < 1 + y ^ 2 by positivity).ne',
        (show 0 < u ^ 2 * y ^ 2 + u ^ 2 by positivity).ne']
      ring
    _ = _ := by rw [integral_const_mul, unit_lorentz_integral hp hp₁]

private theorem sineScale_eq {p : ℝ} (hp : 0 < p) (hp₁ : p < 1) :
    (Real.Gamma p)⁻¹ * (Real.pi / (2 * Real.sin (Real.pi * p / 2))) = sineScale p := by
  let x := Real.pi * p / 2
  have hx : 0 < x := by dsimp [x]; positivity
  have hxp : x < Real.pi / 2 := by
    dsimp [x]
    nlinarith [Real.pi_pos, mul_pos Real.pi_pos (sub_pos.mpr hp₁)]
  have hsin : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hxp⟩
  have hs : Real.sin (Real.pi * p) = 2 * Real.sin x * Real.cos x := by
    rw [show Real.pi * p = 2 * x by dsimp [x]; ring, Real.sin_two_mul]
  have hΓ := (Real.Gamma_pos_of_pos hp).ne'
  change _ = Real.Gamma (1 - p) * Real.cos x
  calc
    _ = (Real.Gamma p)⁻¹ *
        ((Real.pi / (2 * Real.sin x * Real.cos x)) * Real.cos x) := by
      change (Real.Gamma p)⁻¹ * (Real.pi / (2 * Real.sin x)) = _
      field_simp [hsin.ne', hcos.ne']
    _ = _ := by
      rw [← hs, ← Real.Gamma_mul_Gamma_one_sub p, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hΓ,
        one_mul]

private noncomputable def lorentzProfile (p ε u x : ℝ) : ℝ :=
  x ^ (p - 1) * (u / ((x + ε) ^ 2 + u ^ 2))

private theorem lorentzProfile_nonneg {p ε u x : ℝ} (hu : 0 < u) (hx : 0 < x) :
    0 ≤ lorentzProfile p ε u x := by
  unfold lorentzProfile
  positivity

private theorem lorentzProfile_le {p ε u x : ℝ} (hε : 0 ≤ ε) (hu : 0 < u) (hx : 0 < x) :
    lorentzProfile p ε u x ≤ lorentzProfile p 0 u x := by
  unfold lorentzProfile
  rw [add_zero]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hx.le _)
  exact div_le_div_of_nonneg_left hu.le (by positivity)
    (by nlinarith [mul_nonneg hx.le hε, sq_nonneg ε])

private theorem lorentz_zero_integrable {p u : ℝ} (hp : 0 < p) (hp₁ : p < 1) (hu : 0 < u) :
    IntegrableOn (lorentzProfile p 0 u) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  have h : 0 < Real.sin (Real.pi * p / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    nlinarith [Real.pi_pos, mul_pos Real.pi_pos (sub_pos.mpr hp₁)]
  simpa only [lorentzProfile, add_zero, lorentz_integral hp hp₁ hu] using
    (mul_pos (Real.rpow_pos_of_pos hu (p - 1)) (div_pos Real.pi_pos (mul_pos (by norm_num) h))).ne'

theorem dampedPowerSine_bounds {p ε u : ℝ} (hp : 0 < p) (hp₁ : p < 1)
    (hε : 0 < ε) (hu : 0 < u) :
    0 ≤ dampedPowerSine p ε u ∧ dampedPowerSine p ε u ≤ sineScale p * u ^ (p - 1) := by
  rw [dampedPowerSine_eq hp hp₁ hε]
  have hn : ∀ᵐ x : ℝ ∂volume.restrict (Ioi 0), 0 ≤ lorentzProfile p ε u x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact lorentzProfile_nonneg hu hx
  have hle : lorentzProfile p ε u ≤ᵐ[volume.restrict (Ioi 0)] lorentzProfile p 0 u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact lorentzProfile_le hε.le hu hx
  have hΓ : 0 ≤ (Real.Gamma p)⁻¹ := inv_nonneg.mpr (Real.Gamma_pos_of_pos hp).le
  constructor
  · exact mul_nonneg hΓ (integral_nonneg_of_ae hn)
  · have h := integral_mono_of_nonneg hn (lorentz_zero_integrable hp hp₁ hu) hle
    change (Real.Gamma p)⁻¹ * (∫ x : ℝ in Ioi 0, lorentzProfile p ε u x) ≤ _
    refine (mul_le_mul_of_nonneg_left h hΓ).trans_eq ?_
    simp only [lorentzProfile, add_zero, lorentz_integral hp hp₁ hu]
    rw [mul_left_comm, sineScale_eq hp hp₁, mul_comm]

theorem tendsto_dampedPowerSine {p u : ℝ} (hp : 0 < p) (hp₁ : p < 1) (hu : 0 < u) :
    Tendsto (fun ε => dampedPowerSine p ε u) (𝓝[>] 0) (𝓝 (sineScale p * u ^ (p - 1))) := by
  let ν := volume.restrict (Ioi (0 : ℝ))
  have hlim : Tendsto (fun ε => ∫ x : ℝ, lorentzProfile p ε u x ∂ν) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x : ℝ, lorentzProfile p 0 u x ∂ν)) := by
    apply tendsto_integral_filter_of_dominated_convergence (lorentzProfile p 0 u)
    · exact Eventually.of_forall fun ε =>
        (by unfold lorentzProfile; fun_prop : Measurable (lorentzProfile p ε u)).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [Real.norm_of_nonneg (lorentzProfile_nonneg hu hx)]
      exact lorentzProfile_le (le_of_lt hε) hu hx
    · exact lorentz_zero_integrable hp hp₁ hu
    · exact Eventually.of_forall fun x => by
        have hcont : ContinuousAt (fun ε : ℝ => lorentzProfile p ε u x) 0 := by
          unfold lorentzProfile
          fun_prop (disch := positivity)
        exact hcont.continuousWithinAt
  have h := hlim.const_mul (Real.Gamma p)⁻¹
  have hlimit : (Real.Gamma p)⁻¹ * (∫ x : ℝ, lorentzProfile p 0 u x ∂ν) =
      sineScale p * u ^ (p - 1) := by
    simp only [ν, lorentzProfile, add_zero, lorentz_integral hp hp₁ hu]
    rw [mul_left_comm, sineScale_eq hp hp₁, mul_comm]
  rw [hlimit] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (dampedPowerSine_eq hp hp₁ hε u).symm

end ACS12.GammaDeficit

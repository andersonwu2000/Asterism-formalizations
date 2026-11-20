import ACS12.CumulativeWeight
import ACS12.GammaBoundary
import ACS12.GammaTorque

/-! The corrected radial comparison at the actual finite period. -/

namespace ACS12.GammaDeficit

open MeasureTheory Set Filter
open scoped Topology
open ACS12.GammaMeasure (imageDensity imagePotential imageSlope imageSelf
  imagePotential_integrable imageSlope_integrable tendsto_line_sub_imagePotential)

theorem lineDensity_exp_integrable {p t : ℝ} (hp : 0 < p) (ht : 0 < t) :
    IntegrableOn (fun s : ℝ => lineDensity p s * Real.exp (-s * t)) (Ioi 0) := by
  refine ((integrable_gamma_exp hp ht).div_const (Real.Gamma p)).congr ?_
  exact Eventually.of_forall fun s => by
    dsimp [lineDensity]
    rw [show -t * s = -s * t by ring]
    ring

theorem lineDensity_exp_integral {p t : ℝ} (hp : 0 < p) (ht : 0 < t) :
    (∫ s : ℝ in Ioi 0, lineDensity p s * Real.exp (-s * t)) = t ^ (-p) := by
  calc
    _ = (∫ s : ℝ in Ioi 0, s ^ (p - 1) * Real.exp (-t * s)) / Real.Gamma p := by
      rw [← integral_div]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s _
      dsimp [lineDensity]
      rw [show -s * t = -t * s by ring]
      ring
    _ = _ := by rw [gamma_exp_integral hp ht, mul_div_cancel_left₀ _ (Real.Gamma_pos_of_pos hp).ne']

theorem signedDensity_exp_integrable {p L t : ℝ} (hp : 0 < p) (hL : 0 < L) (ht : 0 < t) :
    IntegrableOn (fun s : ℝ => signedDensity p L s * Real.exp (-s * t)) (Ioi 0) := by
  refine ((lineDensity_exp_integrable hp ht).sub (imagePotential_integrable hp hL ht)).congr ?_
  exact Eventually.of_forall fun s => by dsimp [signedDensity]; ring

theorem signedDensity_exp_integral {p L t : ℝ} (hp : 0 < p) (hL : 0 < L) (ht : 0 < t) :
    (∫ s : ℝ in Ioi 0, signedDensity p L s * Real.exp (-s * t)) =
      t ^ (-p) - imagePotential p L t := by
  rw [← lineDensity_exp_integral hp ht, imagePotential,
    ← integral_sub (lineDensity_exp_integrable hp ht) (imagePotential_integrable hp hL ht)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s _
  dsimp [signedDensity]
  ring

private theorem signedFirstDensity_exp_integrable {p L t : ℝ} (hp : 0 < p)
    (hL : 0 < L) (ht : 0 < t) :
    IntegrableOn (fun s : ℝ => signedFirstDensity p L s * Real.exp (-s * t)) (Ioi 0) := by
  have h := integrable_gamma_exp (a := p + 1) (by positivity) ht
  simp only [add_sub_cancel_right] at h
  refine ((h.div_const (Real.Gamma p)).sub (imageSlope_integrable hp hL ht)).congr ?_
  exact Eventually.of_forall fun s => by dsimp [signedFirstDensity]; rw [show -t * s = -s * t by ring]; ring

private theorem signedFirstDensity_exp_integral_one {p L : ℝ} (hp : 0 < p) (hL : 0 < L) :
    (∫ s : ℝ in Ioi 0, signedFirstDensity p L s * Real.exp (-s)) = p - imageSlope p L 1 := by
  have h := integrable_gamma_exp (a := p + 1) (by positivity : 0 < p + 1) (by norm_num : 0 < (1 : ℝ))
  simp only [add_sub_cancel_right, neg_one_mul] at h
  have hline : (∫ s : ℝ in Ioi 0, (s ^ p * Real.exp (-s)) / Real.Gamma p) = p := by
    have hg := gamma_exp_integral (a := p + 1) (by positivity : 0 < p + 1)
      (by norm_num : 0 < (1 : ℝ))
    simp only [add_sub_cancel_right, neg_one_mul, Real.one_rpow, mul_one] at hg
    rw [integral_div, hg, Real.Gamma_add_one hp.ne', mul_div_cancel_right₀ _ (Real.Gamma_pos_of_pos hp).ne']
  have hi := imageSlope_integrable hp hL (show 0 < (1 : ℝ) by norm_num)
  calc
    _ = (∫ s : ℝ in Ioi 0, (s ^ p * Real.exp (-s)) / Real.Gamma p) -
        imageSlope p L 1 := by
      rw [imageSlope, ← integral_sub (h.div_const _) hi]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s _
      dsimp [signedFirstDensity]
      simp only [mul_one]
      ring
    _ = _ := by rw [hline]

private noncomputable def radialWeight (p τ s : ℝ) : ℝ :=
  p * ((Real.exp (-τ * s) - Real.exp (-s)) / s) + Real.exp (-s)

private theorem radialWeight_eq_integral (p τ : ℝ) {s : ℝ} (hs : 0 < s) :
    radialWeight p τ s = p * (∫ x : ℝ in τ..1, Real.exp (-s * x)) + Real.exp (-s) := by
  have hDer (x : ℝ) : HasDerivAt (fun x => Real.exp (-s * x) / (-s)) (Real.exp (-s * x)) x := by
    convert (((hasDerivAt_id x).const_mul (-s)).exp).div_const (-s) using 1
    dsimp
    field_simp [hs.ne']
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hDer x)
    (by apply Continuous.intervalIntegrable; fun_prop :
      IntervalIntegrable (fun x : ℝ => Real.exp (-s * x)) volume τ 1)
  rw [radialWeight, h, mul_one, show -s * τ = -τ * s by ring]
  ring

private theorem radialWeight_nonneg {p τ s : ℝ} (hp : 0 < p) (hτ : τ ≤ 1) (hs : 0 < s) :
    0 ≤ radialWeight p τ s := by
  rw [radialWeight_eq_integral p τ hs]
  exact add_nonneg (mul_nonneg hp.le (intervalIntegral.integral_nonneg hτ (fun _ _ =>
    (Real.exp_pos _).le))) (Real.exp_pos _).le

private theorem radialWeight_antitone {p τ : ℝ} (hp : 0 < p) (hτ₀ : 0 ≤ τ) (hτ : τ ≤ 1) :
    AntitoneOn (radialWeight p τ) (Ioi 0) := by
  intro s hs t ht hst
  rw [radialWeight_eq_integral p τ ht, radialWeight_eq_integral p τ hs]
  apply add_le_add _ (Real.exp_le_exp.mpr (by linarith))
  apply mul_le_mul_of_nonneg_left _ hp.le
  apply intervalIntegral.integral_mono_on hτ
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)
  intro x hx
  exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hst) (hτ₀.trans hx.1)])

private theorem radialWeight_bound {p τ s : ℝ} (hp : 0 < p) (hτ₀ : 0 ≤ τ) (hτ : τ ≤ 1)
    (hs : 0 < s) : |radialWeight p τ s| ≤ p + 1 := by
  rw [abs_of_nonneg (radialWeight_nonneg hp hτ hs), radialWeight_eq_integral p τ hs]
  have he := intervalIntegral.integral_mono_on hτ
    (by apply Continuous.intervalIntegrable; fun_prop :
      IntervalIntegrable (fun x : ℝ => Real.exp (-s * x)) volume τ 1)
    (intervalIntegrable_const (c := (1 : ℝ))) (fun x hx =>
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le)
        (hτ₀.trans hx.1)))
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at he
  have h := mul_le_mul_of_nonneg_left he hp.le
  linarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.le),
    mul_nonneg hp.le hτ₀]

private theorem radialWeight_pair_nonneg {p L τ : ℝ} (hp : 0 < p) (hp₁ : p ≤ 1)
    (hL : 0 < L) (hτ : 0 < τ) (hτ₁ : τ ≤ 1) :
    0 ≤ p * ((τ ^ (-p) - imagePotential p L τ) - (1 - imagePotential p L 1)) +
      (p - imageSlope p L 1) := by
  let e (t : ℝ) (s : ℝ) := signedDensity p L s * Real.exp (-s * t)
  let σ (s : ℝ) := signedFirstDensity p L s * Real.exp (-s)
  have heτ : IntegrableOn (e τ) (Ioi 0) := signedDensity_exp_integrable hp hL hτ
  have he₁ : IntegrableOn (e 1) (Ioi 0) := signedDensity_exp_integrable hp hL zero_lt_one
  have hσ : IntegrableOn σ (Ioi 0) := by
    simpa only [σ, mul_one] using signedFirstDensity_exp_integrable hp hL zero_lt_one
  have hInt : IntegrableOn (fun s : ℝ => p * (e τ s - e 1 s) + σ s) (Ioi 0) :=
    ((heτ.sub he₁).const_mul p).add hσ
  have he (s : ℝ) (hs : 0 < s) :
      signedFirstDensity p L s * radialWeight p τ s = p * (e τ s - e 1 s) + σ s := by
    rw [radialWeight]
    dsimp only [e, σ]
    rw [signedFirstDensity_eq hs]
    rw [show -s * τ = -τ * s by ring, mul_one]
    field_simp [hs.ne']
  have hInt' : IntegrableOn (fun s : ℝ => signedFirstDensity p L s * radialWeight p τ s) (Ioi 0) := by
    refine hInt.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (he s hs).symm
  have hSmooth : ContDiffOn ℝ 1 (radialWeight p τ) (Ioi 0) := by
    intro s hs
    have hs' : s ≠ 0 := (mem_Ioi.mp hs).ne'
    apply ContDiffAt.contDiffWithinAt
    unfold radialWeight
    fun_prop (disch := assumption)
  have h := signedFirstDensity_test_nonneg hp hp₁ hL hSmooth
    (fun _ hs => radialWeight_nonneg hp hτ₁ hs)
    (radialWeight_antitone hp hτ.le hτ₁)
    (fun _ hs => radialWeight_bound hp hτ.le hτ₁ hs.1) hInt'
  have hE : (∫ s : ℝ in Ioi 0, signedFirstDensity p L s * radialWeight p τ s) =
      ∫ s : ℝ in Ioi 0, p * (e τ s - e 1 s) + σ s := by
    apply setIntegral_congr_fun measurableSet_Ioi
    exact he
  have hsum : (∫ s : ℝ in Ioi 0, p * (e τ s - e 1 s) + σ s) =
      p * ((∫ s : ℝ in Ioi 0, e τ s) - (∫ s : ℝ in Ioi 0, e 1 s)) +
        ∫ s : ℝ in Ioi 0, σ s := by
    calc
      _ = (∫ s : ℝ in Ioi 0, p * (e τ s - e 1 s)) + ∫ s : ℝ in Ioi 0, σ s :=
        integral_add ((heτ.sub he₁).const_mul p) hσ
      _ = _ := by
        rw [integral_const_mul]
        exact congrArg (fun v : ℝ => p * v + ∫ s : ℝ in Ioi 0, σ s) (integral_sub heτ he₁)
  rw [hE, hsum] at h
  change 0 ≤ p * ((∫ s : ℝ in Ioi 0, signedDensity p L s * Real.exp (-s * τ)) -
    (∫ s : ℝ in Ioi 0, signedDensity p L s * Real.exp (-s * 1))) +
      ∫ s : ℝ in Ioi 0, signedFirstDensity p L s * Real.exp (-s) at h
  rw [signedDensity_exp_integral hp hL hτ, signedDensity_exp_integral hp hL zero_lt_one,
    Real.one_rpow, signedFirstDensity_exp_integral_one hp hL] at h
  exact h

/-- The original self-corrected radial level pays the slope at the
subunit exponents, including the literal Newtonian boundary. -/
theorem imageSlope_le_corrected {p L : ℝ} (hp : 0 < p) (hp₁ : p ≤ 1) (hL : 0 < L) :
    imageSlope p L 1 ≤ p * (imagePotential p L 1 + imageSelf p L) := by
  have h := (((tendsto_line_sub_imagePotential hp hp₁ hL).sub_const
    (1 - imagePotential p L 1)).const_mul p).add_const (p - imageSlope p L 1)
  have hlim : 0 ≤ p * (imageSelf p L - (1 - imagePotential p L 1)) +
      (p - imageSlope p L 1) := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds h
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ τ : ℝ in 𝓝 (0 : ℝ), τ < 1 from Iio_mem_nhds zero_lt_one).filter_mono
        nhdsWithin_le_nhds] with τ hτ hτ₁
    exact radialWeight_pair_nonneg hp hp₁ hL hτ hτ₁.le
  linarith

end ACS12.GammaDeficit

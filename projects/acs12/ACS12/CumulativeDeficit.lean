import ACS12.DeficitMixture
import ACS12.DeficitSine
import ACS12.PowerSine
import ACS12.GammaPeriodization

/-! The exact cumulative signed Gamma comparison below exponent one. -/

namespace ACS12.GammaDeficit

open MeasureTheory Set Filter
open scoped Topology

private noncomputable def dampedSinhSine (p ε u : ℝ) : ℝ :=
  ∫ t : ℝ in Ioi 0, sinhProfile p t * Real.exp (-ε * t) * Real.sin (u * t)

private noncomputable def dampedDeficitSine (p ε u : ℝ) : ℝ :=
  ∫ t : ℝ in Ioi 0, deficitProfile p t * Real.exp (-ε * t) * Real.sin (u * t)

private theorem sinhProfile_nonneg {p t : ℝ} (ht : 0 < t) : 0 ≤ sinhProfile p t := by
  unfold sinhProfile
  exact Real.rpow_nonneg (mul_nonneg (by norm_num)
    (Real.sinh_pos_iff.mpr (by positivity : 0 < t / 2)).le) _

private theorem abs_damped_sine_le {ε t u : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t) :
    |Real.exp (-ε * t) * Real.sin (u * t)| ≤ 1 := by
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (-ε * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hε) ht)
  exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (Real.exp_pos _).le).trans
    (by simpa only [mul_one] using he)

private theorem damped_sine_integrable {g : ℝ → ℝ} (hg : Measurable g)
    (hi : IntegrableOn g (Ioi 0)) (hpos : ∀ t > 0, 0 ≤ g t)
    {ε : ℝ} (hε : 0 ≤ ε) (u : ℝ) :
    IntegrableOn (fun t : ℝ => g t * Real.exp (-ε * t) * Real.sin (u * t)) (Ioi 0) := by
  refine hi.mono' ((hg.mul (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht₀ : 0 < t := ht
  rw [Real.norm_eq_abs, mul_assoc, abs_mul, abs_of_nonneg (hpos t ht₀)]
  exact (mul_le_mul_of_nonneg_left (abs_damped_sine_le hε ht₀.le) (hpos t ht₀)).trans_eq
    (mul_one _)

private theorem dampedSinhSine_bound {p ε : ℝ} (hp : 0 < p) (hp₁ : p < 1)
    (hε : 0 ≤ ε) (u : ℝ) :
    |dampedSinhSine p ε u| ≤ ∫ t : ℝ in Ioi 0, sinhProfile p t := by
  unfold dampedSinhSine
  rw [← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le (sinhProfile_integrable hp hp₁)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht₀ : 0 < t := ht
  rw [Real.norm_eq_abs, mul_assoc, abs_mul, abs_of_nonneg (sinhProfile_nonneg ht₀)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (abs_damped_sine_le hε ht₀.le)
    (sinhProfile_nonneg (p := p) ht₀)

private theorem tendsto_dampedSinhSine {p : ℝ} (hp : 0 < p) (hp₁ : p < 1) (u : ℝ) :
    Tendsto (fun ε => dampedSinhSine p ε u) (𝓝[>] 0) (𝓝 (sineScale p * normalizedImage p u)) := by
  rw [sineScale, ← sinhProfile_sine hp hp₁ u]
  unfold dampedSinhSine
  apply tendsto_integral_filter_of_dominated_convergence (sinhProfile p)
  · exact Eventually.of_forall fun ε =>
      (by unfold sinhProfile; fun_prop : Measurable (fun t : ℝ => sinhProfile p t *
        Real.exp (-ε * t) * Real.sin (u * t))).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht₀ : 0 < t := ht
    rw [Real.norm_eq_abs, mul_assoc, abs_mul, abs_of_nonneg (sinhProfile_nonneg ht₀)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (abs_damped_sine_le hε.le ht₀.le)
      (sinhProfile_nonneg (p := p) ht₀)
  · exact sinhProfile_integrable hp hp₁
  · exact Eventually.of_forall fun t => by
      have hc : ContinuousAt (fun ε : ℝ => sinhProfile p t * Real.exp (-ε * t) *
          Real.sin (u * t)) 0 := by fun_prop
      have h := hc.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
      simpa only [neg_zero, zero_mul, Real.exp_zero, mul_one] using h

private theorem dampedDeficitSine_eq {p ε : ℝ} (hp : 0 < p) (hp₁ : p < 1)
    (hε : 0 < ε) (u : ℝ) :
    dampedDeficitSine p ε u = dampedPowerSine p ε u - dampedSinhSine p ε u := by
  have hPow : IntegrableOn (fun t : ℝ => t ^ (-p) * Real.exp (-ε * t) * Real.sin (u * t))
      (Ioi 0) := by
    have hExp : IntegrableOn (fun t : ℝ => t ^ (-p) * Real.exp (-ε * t)) (Ioi 0) := by
      simpa only [sub_sub_cancel_left] using integrable_gamma_exp (sub_pos.mpr hp₁) hε
    refine hExp.mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht₀ : 0 < t := ht
    have hn : 0 ≤ t ^ (-p) * Real.exp (-ε * t) := by positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hn]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (u * t)) hn
  have hSinh := damped_sine_integrable (g := sinhProfile p) (by unfold sinhProfile; fun_prop)
    (sinhProfile_integrable hp hp₁) (fun _ ht => sinhProfile_nonneg ht) hε.le u
  unfold dampedDeficitSine dampedPowerSine dampedSinhSine
  rw [← integral_sub hPow hSinh]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only [deficitProfile]
  ring

noncomputable def normalizedCumulative (p U : ℝ) : ℝ :=
  ∫ u : ℝ in Ioo 0 U, u * (u ^ (p - 1) - normalizedImage p u)

private theorem tendsto_damped_deficit_integral {p U : ℝ} (hp : 0 < p) (hp₁ : p < 1)
    (hU : 0 < U) :
    Tendsto (fun ε => ∫ u : ℝ in Ioo 0 U, u * dampedDeficitSine p ε u)
      (𝓝[>] 0) (𝓝 (sineScale p * normalizedCumulative p U)) := by
  let B := ∫ t : ℝ in Ioi 0, sinhProfile p t
  have hBound : IntegrableOn (fun u : ℝ => sineScale p * u ^ p + B * u) (Ioo 0 U) := by
    have hr := (intervalIntegral.integrableOn_Ioo_rpow_iff hU).mpr
      (show -1 < p by linarith)
    have hi : IntegrableOn (fun u : ℝ => u) (Ioo 0 U) :=
      (continuous_id.integrableOn_Icc (μ := volume)).mono_set Ioo_subset_Icc_self
    exact (hr.const_mul _).add (hi.const_mul _)
  unfold normalizedCumulative
  rw [← integral_const_mul]
  apply tendsto_integral_filter_of_dominated_convergence
    (fun u : ℝ => sineScale p * u ^ p + B * u)
  · refine Eventually.of_forall fun ε => ?_
    have hm : Measurable (fun z : ℝ × ℝ => deficitProfile p z.2 *
        Real.exp (-ε * z.2) * Real.sin (z.1 * z.2)) := by
      unfold deficitProfile sinhProfile
      fun_prop
    exact (measurable_id.mul (hm.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioi 0))).measurable).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε₀ : 0 < ε := hε
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have hu₀ : 0 < u := hu.1
    obtain ⟨hP₀, hP⟩ := dampedPowerSine_bounds hp hp₁ hε₀ hu₀
    have hS := dampedSinhSine_bound hp hp₁ hε₀.le u
    rw [dampedDeficitSine_eq hp hp₁ hε₀, Real.norm_eq_abs, abs_mul, abs_of_pos hu₀]
    calc
      _ ≤ u * (|dampedPowerSine p ε u| + |dampedSinhSine p ε u|) := by
        apply mul_le_mul_of_nonneg_left _ hu₀.le
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (dampedPowerSine p ε u) (-dampedSinhSine p ε u)
      _ ≤ u * (sineScale p * u ^ (p - 1) + B) := by
        rw [abs_of_nonneg hP₀]
        exact mul_le_mul_of_nonneg_left (add_le_add hP hS) hu₀.le
      _ = _ := by
        rw [show u ^ p = u ^ (p - 1) * u by
          rw [← Real.rpow_add_one hu₀.ne', sub_add_cancel]]
        ring
  · exact hBound
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have hu₀ : 0 < u := hu.1
    have hlim := ((tendsto_dampedPowerSine hp hp₁ hu₀).sub
      (tendsto_dampedSinhSine hp hp₁ u)).const_mul u
    have he : u * (sineScale p * u ^ (p - 1) - sineScale p * normalizedImage p u) =
        sineScale p * (u * (u ^ (p - 1) - normalizedImage p u)) := by ring
    rw [he] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [dampedDeficitSine_eq hp hp₁ hε]

private theorem integral_u_sine {U t : ℝ} (hU : 0 < U) (ht : 0 < t) :
    (∫ u : ℝ in Ioo 0 U, u * Real.sin (u * t)) = sineBracket U t / t ^ 2 := by
  have hd (u : ℝ) : HasDerivAt (fun u => sineBracket u t / t ^ 2)
      (u * Real.sin (u * t)) u := by
    have hx := (hasDerivAt_id u).mul_const t
    have h := (hx.sin.sub (hx.mul hx.cos)).div_const (t ^ 2)
    convert h using 1
    dsimp
    field_simp [ht.ne']
    ring
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hU.le]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    (by apply Continuous.intervalIntegrable; fun_prop :
      IntervalIntegrable (fun u : ℝ => u * Real.sin (u * t)) volume 0 U)
  simpa only [sineBracket, zero_mul, Real.sin_zero, sub_zero, zero_div] using h

private theorem damped_bracket_eq {p U ε : ℝ} (hp : 0 < p) (hp₁ : p < 1)
    (hU : 0 < U) (hε : 0 < ε) :
    (∫ u : ℝ in Ioo 0 U, u * dampedDeficitSine p ε u) =
      ∫ t : ℝ in Ioi 0, (deficitProfile p t / t ^ 2 * sineBracket U t) * Real.exp (-ε * t) := by
  let μ := volume.restrict (Ioo (0 : ℝ) U)
  let ν := volume.restrict (Ioi (0 : ℝ))
  let F (z : ℝ × ℝ) := z.1 * (deficitProfile p z.2 * Real.exp (-ε * z.2) *
    Real.sin (z.1 * z.2))
  let G (z : ℝ × ℝ) := z.1 * (z.2 ^ (-p) * Real.exp (-ε * z.2))
  have hU' : Integrable (fun u : ℝ => u) μ :=
    (continuous_id.integrableOn_Icc (μ := volume)).mono_set Ioo_subset_Icc_self
  have hT : Integrable (fun t : ℝ => t ^ (-p) * Real.exp (-ε * t)) ν := by
    simpa only [sub_sub_cancel_left] using integrable_gamma_exp (sub_pos.mpr hp₁) hε
  have hGi : Integrable G (μ.prod ν) := hU'.mul_prod hT
  have hFm : Measurable F := by
    unfold F deficitProfile sinhProfile
    fun_prop
  have hFi : Integrable F (μ.prod ν) := by
    refine hGi.mono' hFm.aestronglyMeasurable ?_
    have hPos : ∀ᵐ z : ℝ × ℝ ∂μ.prod ν, 0 < z.1 ∧ 0 < z.2 := by
      apply (Measure.ae_prod_iff_ae_ae ((measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_lt measurable_const measurable_snd))).mpr
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact ⟨hu.1, ht⟩
    filter_upwards [hPos] with z hz
    have hd := deficitProfile_nonneg hp hz.2
    dsimp only [F, G]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hz.1, abs_mul, abs_of_nonneg (mul_nonneg hd
      (Real.exp_pos _).le)]
    apply mul_le_mul_of_nonneg_left _ hz.1.le
    calc
      _ ≤ (deficitProfile p z.2 * Real.exp (-ε * z.2)) * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (mul_nonneg hd (Real.exp_pos _).le)
      _ ≤ _ := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_right (deficitProfile_le_power p _ hz.2) (Real.exp_pos _).le
  have hrow_u (u : ℝ) : (∫ t : ℝ, F (u, t) ∂ν) = u * dampedDeficitSine p ε u := by
    exact integral_const_mul _ _
  have hrow_t : ∀ᵐ t ∂ν, (∫ u : ℝ, F (u, t) ∂μ) =
      (deficitProfile p t / t ^ 2 * sineBracket U t) * Real.exp (-ε * t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht₀ : 0 < t := ht
    calc
      _ = (deficitProfile p t * Real.exp (-ε * t)) *
          ∫ u : ℝ in Ioo 0 U, u * Real.sin (u * t) := by
        rw [← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioo
        intro u _
        dsimp [F]
        ring
      _ = _ := by rw [integral_u_sine hU ht₀]; ring
  calc
    _ = ∫ u : ℝ, (∫ t : ℝ, F (u, t) ∂ν) ∂μ :=
      integral_congr_ae (Eventually.of_forall fun u => (hrow_u u).symm)
    _ = ∫ z, F z ∂μ.prod ν := (integral_prod F hFi).symm
    _ = ∫ t : ℝ, (∫ u : ℝ, F (u, t) ∂μ) ∂ν := integral_prod_symm F hFi
    _ = _ := integral_congr_ae hrow_t

private theorem tendsto_damped_bracket {p U : ℝ} (hp : 0 < p) (hp₁ : p < 1) (hU : 0 < U) :
    Tendsto (fun ε => ∫ t : ℝ in Ioi 0,
      (deficitProfile p t / t ^ 2 * sineBracket U t) * Real.exp (-ε * t))
      (𝓝[>] 0) (𝓝 (∫ t : ℝ in Ioi 0, deficitProfile p t / t ^ 2 * sineBracket U t)) := by
  let g (t : ℝ) := deficitProfile p t / t ^ 2 * sineBracket U t
  have hg : Measurable g := by unfold g deficitProfile sinhProfile sineBracket; fun_prop
  apply tendsto_integral_filter_of_dominated_convergence (fun t => ‖g t‖)
  · exact Eventually.of_forall fun ε => (hg.mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε₀ : 0 < ε := hε
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht₀ : 0 < t := ht
    change ‖g t * Real.exp (-ε * t)‖ ≤ ‖g t‖
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr (by nlinarith))
  · exact (integrable_deficit_bracket hp (by linarith) hU).norm
  · exact Eventually.of_forall fun t => by
      have hc : ContinuousAt (fun ε : ℝ => g t * Real.exp (-ε * t)) 0 := by fun_prop
      have h := hc.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
      simpa only [neg_zero, zero_mul, Real.exp_zero, mul_one] using h

theorem normalizedCumulative_pos {p U : ℝ} (hp : 0 < p) (hp₁ : p < 1) (hU : 0 < U) :
    0 < normalizedCumulative p U := by
  have hlim := tendsto_damped_deficit_integral hp hp₁ hU
  have hlim' := tendsto_damped_bracket hp hp₁ hU
  have heq : (fun ε => ∫ u : ℝ in Ioo 0 U, u * dampedDeficitSine p ε u) =ᶠ[𝓝[>] 0]
      (fun ε => ∫ t : ℝ in Ioi 0,
        (deficitProfile p t / t ^ 2 * sineBracket U t) * Real.exp (-ε * t)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact damped_bracket_eq hp hp₁ hU hε
  have he := tendsto_nhds_unique (hlim.congr' heq) hlim'
  have hpos : 0 < sineScale p * normalizedCumulative p U := he.symm ▸
    integral_deficit_bracket_pos hp (by linarith) hU
  exact pos_of_mul_pos_right hpos (sineScale_pos hp hp₁).le

noncomputable def lineDensity (p s : ℝ) : ℝ := s ^ (p - 1) / Real.Gamma p

noncomputable def cumulativeDeficit (p L T : ℝ) : ℝ :=
  ∫ s : ℝ in Ioo 0 T, s * (lineDensity p s - GammaMeasure.imageDensity p L s)

private theorem imageDensity_eq_normalized (p : ℝ) {L : ℝ} (hL : 0 < L) (s : ℝ) :
    GammaMeasure.imageDensity p L s =
      (2 * Real.pi / L) ^ (p - 1) / Real.Gamma p *
        normalizedImage p (L * s / (2 * Real.pi)) := by
  rw [GammaMeasure.imageDensity_eq_spectral p hL, GammaMeasure.gammaDensity, normalizedImage,
    show 2 * Real.pi / L = 2 * (Real.pi / L) by ring,
    Real.mul_rpow (by norm_num : 0 ≤ (2 : ℝ)) (by positivity),
    show Real.pi * (L * s / (2 * Real.pi)) = L * s / 2 by field_simp [Real.pi_ne_zero]]
  ring

private theorem cumulativeDeficit_eq_normalized {p L T : ℝ} (hL : 0 < L) (hT : 0 < T) :
    cumulativeDeficit p L T =
      (2 * Real.pi / L) ^ (p + 1) / Real.Gamma p *
        normalizedCumulative p (T / (2 * Real.pi / L)) := by
  let η := 2 * Real.pi / L
  let f (s : ℝ) := s * (lineDensity p s - GammaMeasure.imageDensity p L s)
  have hη : 0 < η := by dsimp [η]; positivity
  have hTη : 0 < T / η := div_pos hT hη
  have hscale := intervalIntegral.integral_comp_mul_left (a := 0) (b := T / η) f hη.ne'
  rw [mul_zero, show η * (T / η) = T by field_simp [hη.ne'], smul_eq_mul] at hscale
  have hpoint (u : ℝ) (hu : 0 < u) : f (η * u) =
      η ^ p / Real.Gamma p * (u * (u ^ (p - 1) - normalizedImage p u)) := by
    unfold f lineDensity
    rw [Real.mul_rpow hη.le hu.le, imageDensity_eq_normalized p hL,
      show L * (η * u) / (2 * Real.pi) = u by
        dsimp [η]; field_simp [hL.ne', Real.pi_ne_zero],
      show η ^ p = η ^ (p - 1) * η by
        rw [← Real.rpow_add_one hη.ne', sub_add_cancel]]
    change η * u * (η ^ (p - 1) * u ^ (p - 1) / Real.Gamma p -
      η ^ (p - 1) / Real.Gamma p * normalizedImage p u) = _
    ring
  calc
    _ = ∫ s : ℝ in (0 : ℝ)..T, f s := by
      rw [intervalIntegral.integral_of_le hT.le, integral_Ioc_eq_integral_Ioo]
      rfl
    _ = η * ∫ u : ℝ in (0 : ℝ)..(T / η), f (η * u) := by
      rw [hscale, ← mul_assoc, mul_inv_cancel₀ hη.ne', one_mul]
    _ = η * ∫ u : ℝ in Ioo 0 (T / η), f (η * u) := by
      rw [intervalIntegral.integral_of_le hTη.le, integral_Ioc_eq_integral_Ioo]
    _ = η * ∫ u : ℝ in Ioo 0 (T / η),
        (η ^ p / Real.Gamma p) * (u * (u ^ (p - 1) - normalizedImage p u)) := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioo
      exact fun u hu => hpoint u hu.1
    _ = _ := by
      rw [integral_const_mul, ← mul_assoc, ← mul_div_assoc, mul_comm η (η ^ p),
        ← Real.rpow_add_one hη.ne']
      rfl

/-- The actual Gamma density has strictly positive cumulative signed
deficit at each finite truncation in the subunit range. -/
theorem cumulativeDeficit_pos {p L T : ℝ} (hp : 0 < p) (hp₁ : p < 1)
    (hL : 0 < L) (hT : 0 < T) : 0 < cumulativeDeficit p L T := by
  rw [cumulativeDeficit_eq_normalized hL hT]
  have hη : 0 < 2 * Real.pi / L := by positivity
  exact mul_pos (div_pos (Real.rpow_pos_of_pos hη _) (Real.Gamma_pos_of_pos hp))
    (normalizedCumulative_pos hp hp₁ (div_pos hT hη))

theorem cumulativeDeficit_nonneg {p L T : ℝ} (hp : 0 < p) (hp₁ : p ≤ 1)
    (hL : 0 < L) (hT : 0 < T) : 0 ≤ cumulativeDeficit p L T := by
  rcases lt_or_eq_of_le hp₁ with h | rfl
  · exact (cumulativeDeficit_pos hp h hL hT).le
  · unfold cumulativeDeficit
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    rw [lineDensity, sub_self, Real.rpow_zero, Real.Gamma_one, div_one, GammaMeasure.imageDensity_one]
    exact mul_nonneg hs.1.le (sub_nonneg.mpr (Real.tanh_lt_one _).le)

end ACS12.GammaDeficit

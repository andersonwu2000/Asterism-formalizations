import CenteredCircle.PeriodizationIntegral

/-! The nonzero self images, including the mass-dependent radial correction. -/

namespace CenteredCircle.AllN

open MeasureTheory Filter Set
open scoped BigOperators Topology

noncomputable def selfImageTerm (L : ℝ) : ℝ :=
  2 * ∑' j : ℕ, radialKernel L (L + j * L)

noncomputable def imageDensity (L u : ℝ) : ℝ :=
  Real.exp (-u * L) / (1 + Real.exp (-u * L))

theorem imageDensity_pos (L u : ℝ) : 0 < imageDensity L u := by
  dsimp [imageDensity]
  positivity

theorem imageDensity_integrable {L : ℝ} (hL : 0 < L) :
    IntegrableOn (imageDensity L) (Ioi 0) :=
  integrable_radial_sample_integrand hL L hL

theorem imageDensity_integral {L : ℝ} (hL : 0 < L) :
    (∫ u : ℝ in Ioi 0, imageDensity L u) = Real.log 2 / L := by
  let primitive : ℝ → ℝ := fun u => -(Real.log (1 + Real.exp (-u * L))) / L
  have hd (u : ℝ) : HasDerivAt primitive (imageDensity L u) u := by
    have he := (((hasDerivAt_id u).neg.mul_const L).exp).const_add 1
    have h := ((he.log (by positivity : (1 + Real.exp (-u * L) : ℝ) ≠ 0)).neg).div_const L
    convert h using 1
    dsimp [imageDensity]
    field_simp
  have hexp : Tendsto (fun u : ℝ => Real.exp (-u * L)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hL)
    convert h using 1
    funext u
    dsimp
    congr 1
    ring
  have harg : Tendsto (fun u : ℝ => 1 + Real.exp (-u * L)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hexp
  have hp : Tendsto primitive atTop (𝓝 0) := by
    have hlog := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp harg
    simpa only [Real.log_one, neg_zero, zero_div] using hlog.neg.div_const L
  have hf := integral_Ioi_of_hasDerivAt_of_tendsto' (a := (0 : ℝ))
    (fun u _ => hd u) (imageDensity_integrable hL) hp
  norm_num [primitive, neg_div] at hf
  exact hf

theorem selfImageTerm_eq {L : ℝ} (hL : 0 < L) :
    selfImageTerm L = 2 * Real.log 2 / L := by
  rw [selfImageTerm, radial_sample_tsum_integral hL L hL]
  change 2 * (∫ u : ℝ in Ioi 0, imageDensity L u) = _
  rw [imageDensity_integral hL]
  ring

theorem selfImageTerm_integral {L : ℝ} (hL : 0 < L) :
    selfImageTerm L = 2 * ∫ u : ℝ in Ioi 0, imageDensity L u := by
  rw [selfImageTerm, radial_sample_tsum_integral hL L hL]
  rfl

theorem circleWeight_eq_one_sub_images (L u : ℝ) :
    circleWeight L u = 1 - 2 * imageDensity L u := by
  rw [circleWeight_exp_ratio, imageDensity]
  field_simp
  ring

theorem continuous_imageDensity (L : ℝ) : Continuous (imageDensity L) := by
  have he : Continuous (fun u : ℝ => Real.exp (-u * L)) := by fun_prop
  exact he.div (continuous_const.add he) (fun u => by positivity)

theorem imageDensity_times_exp_integrable {L : ℝ} (hL : 0 < L) :
    IntegrableOn (fun u : ℝ => imageDensity L u * Real.exp (-u)) (Ioi 0) := by
  apply (imageDensity_integrable hL).mono'
    ((continuous_imageDensity L).mul (Real.continuous_exp.comp continuous_neg)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  dsimp only [Pi.mul_apply, Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos (imageDensity_pos L u) (Real.exp_pos _))]
  exact mul_le_of_le_one_right (imageDensity_pos L u).le
    (Real.exp_le_one_iff.mpr (by linarith [show 0 < u from hu]))

theorem imageCorrection_integrable {L : ℝ} (hL : 0 < L) :
    IntegrableOn (fun u : ℝ => imageDensity L u * (1 - Real.exp (-u))) (Ioi 0) := by
  convert (imageDensity_integrable hL).sub (imageDensity_times_exp_integrable hL) using 1
  funext u
  dsimp
  ring

noncomputable def radialCorrection (L : ℝ) : ℝ := radialKernel L 1 + selfImageTerm L

theorem radialCorrection_eq_integral {L : ℝ} (hL : 0 < L) :
    radialCorrection L = 1 + 2 *
      ∫ u : ℝ in Ioi 0, imageDensity L u * (1 - Real.exp (-u)) := by
  have hiExp : IntegrableOn (fun u : ℝ => Real.exp (-u)) (Ioi 0) := by
    simpa using integrable_power_exponential 0 1 (by norm_num)
  have hiRad : IntegrableOn (fun u : ℝ => circleWeight L u * Real.exp (-u)) (Ioi 0) := by
    simpa using radialKernel_integrable hL 1 (by norm_num)
  have hi := imageDensity_integrable hL
  have hj := imageCorrection_integrable hL
  have he : (∫ u : ℝ in Ioi 0, Real.exp (-u)) = 1 := by
    simpa using integral_power_exponential 0 1 (by norm_num)
  have hid : (∫ u : ℝ in Ioi 0,
      circleWeight L u * Real.exp (-u) + 2 * imageDensity L u) =
      ∫ u : ℝ in Ioi 0,
        Real.exp (-u) + 2 * (imageDensity L u * (1 - Real.exp (-u))) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    dsimp only
    rw [circleWeight_eq_one_sub_images]
    ring
  rw [integral_add hiRad (hi.const_mul 2), integral_add hiExp (hj.const_mul 2),
    integral_const_mul, integral_const_mul, he] at hid
  unfold radialCorrection radialKernel
  simp only [mul_one]
  rw [selfImageTerm_integral hL]
  exact hid

theorem radialCorrection_gt_one {L : ℝ} (hL : 0 < L) : 1 < radialCorrection L := by
  letI : NeZero (volume.restrict (Ioi (0 : ℝ))) := ⟨positiveHalfLine_ne_zero⟩
  have hp : (0 : ℝ) < ∫ u : ℝ in Ioi 0, imageDensity L u * (1 - Real.exp (-u)) := by
    have h := integral_strict_of_ae_lt (volume.restrict (Ioi (0 : ℝ)))
      (integrable_zero ℝ ℝ _) (imageCorrection_integrable hL) ?_
    · simpa only [integral_zero] using h
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have he : Real.exp (-u) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hu)
      exact mul_pos (imageDensity_pos L u) (by linarith)
  rw [radialCorrection_eq_integral hL]
  linarith

end CenteredCircle.AllN

import ACS12.CumulativeDeficit
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Nonnegative testing of the cumulative signed density against decreasing
weights. The integration by parts uses only finite positive endpoints. -/

namespace ACS12.GammaDeficit

open MeasureTheory Set Filter
open scoped Topology

noncomputable def signedDensity (p L s : ℝ) : ℝ :=
  lineDensity p s - GammaMeasure.imageDensity p L s

noncomputable def signedFirstDensity (p L s : ℝ) : ℝ :=
  s ^ p / Real.Gamma p - s * GammaMeasure.imageDensity p L s

theorem signedFirstDensity_eq {p L s : ℝ} (hs : 0 < s) :
    signedFirstDensity p L s = s * signedDensity p L s := by
  rw [signedFirstDensity, signedDensity, lineDensity,
    show s ^ p = s ^ (p - 1) * s by rw [← Real.rpow_add_one hs.ne', sub_add_cancel]]
  ring

private theorem continuous_signedFirstDensity {p L : ℝ} (hp : 0 < p) (hL : 0 < L) :
    Continuous (signedFirstDensity p L) := by
  unfold signedFirstDensity
  exact ((Real.continuous_rpow_const hp.le).div_const _).sub
    (continuous_id.mul (GammaMeasure.continuous_imageDensity hp hL))

private noncomputable def signedPrimitive (p L t : ℝ) : ℝ :=
  ∫ s : ℝ in (0 : ℝ)..t, signedFirstDensity p L s

private theorem signedPrimitive_nonneg {p L t : ℝ} (hp : 0 < p) (hp₁ : p ≤ 1)
    (hL : 0 < L) (ht : 0 < t) : 0 ≤ signedPrimitive p L t := by
  unfold signedPrimitive
  rw [intervalIntegral.integral_of_le ht.le, integral_Ioc_eq_integral_Ioo]
  have h : (∫ s : ℝ in Ioo 0 t, signedFirstDensity p L s) = cumulativeDeficit p L t := by
    apply setIntegral_congr_fun measurableSet_Ioo
    exact fun s hs => signedFirstDensity_eq hs.1
  rw [h]
  exact cumulativeDeficit_nonneg hp hp₁ hL ht

/-- A bounded-at-zero nonnegative smooth decreasing weight integrates
nonnegatively against the signed first density. -/
theorem signedFirstDensity_test_nonneg {p L : ℝ} (hp : 0 < p) (hp₁ : p ≤ 1)
    (hL : 0 < L) {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Ioi 0))
    (hf₀ : ∀ s > 0, 0 ≤ f s) (hAnti : AntitoneOn f (Ioi 0))
    {B : ℝ} (hB : ∀ s ∈ Ioc (0 : ℝ) 1, |f s| ≤ B)
    (hInt : IntegrableOn (fun s : ℝ => signedFirstDensity p L s * f s) (Ioi 0)) :
    0 ≤ ∫ s : ℝ in Ioi 0, signedFirstDensity p L s * f s := by
  let σ := signedFirstDensity p L
  let H := signedPrimitive p L
  let g (s : ℝ) := σ s * f s
  have hσ : Continuous σ := continuous_signedFirstDensity hp hL
  have hHd (s : ℝ) : HasDerivAt H (σ s) s := (hσ.integral_hasStrictDerivAt 0 s).hasDerivAt
  have hH : Continuous H := continuous_iff_continuousAt.mpr fun s => (hHd s).continuousAt
  have hfd (s : ℝ) (hs : 0 < s) : HasDerivAt f (deriv f s) s :=
    (hf.differentiableOn_one.differentiableAt (Ioi_mem_nhds hs)).hasDerivAt
  have hcont_deriv : ContinuousOn (deriv f) (Ioi 0) :=
    hf.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
  have hderiv (s : ℝ) (hs : 0 < s) : deriv f s ≤ 0 := by
    rw [← derivWithin_of_mem_nhds (Ioi_mem_nhds hs)]
    exact hAnti.derivWithin_nonpos
  have hHpos (s : ℝ) (hs : 0 < s) : 0 ≤ H s := signedPrimitive_nonneg hp hp₁ hL hs
  have hnear : Tendsto (fun a : ℝ => H a * f a) (𝓝[>] 0) (𝓝 0) := by
    have hH0 := hH.continuousAt (x := 0)
    have hlim := hH0.tendsto.norm.const_mul B
    simp only [H, signedPrimitive, intervalIntegral.integral_same, norm_zero, mul_zero] at hlim
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (hlim.mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ a : ℝ in 𝓝 (0 : ℝ), a < 1 from Iio_mem_nhds zero_lt_one).filter_mono
        nhdsWithin_le_nhds] with a ha ha₁
    have hbound := hB a ⟨ha, ha₁.le⟩
    rw [norm_mul, mul_comm B, Real.norm_eq_abs (f a)]
    exact mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
  have hfinite (T : ℝ) (hT : 0 < T) : 0 ≤ ∫ s : ℝ in (0 : ℝ)..T, g s := by
    have hintT : IntervalIntegrable g volume 0 T :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr
        (hInt.mono_set Ioc_subset_Ioi_self)
    have hq := intervalIntegral.continuousOn_primitive_interval' hintT (a := 0) left_mem_uIcc
    have hnhds : 𝓝[>] (0 : ℝ) ≤ 𝓝[uIcc (0 : ℝ) T] 0 := by
      rw [nhdsWithin]
      refine le_inf nhdsWithin_le_nhds (le_principal_iff.mpr ?_)
      filter_upwards [self_mem_nhdsWithin, (show ∀ᶠ a : ℝ in 𝓝 (0 : ℝ), a < T from Iio_mem_nhds hT).filter_mono
        nhdsWithin_le_nhds]
        with a ha haT
      exact mem_uIcc_of_le ha.le haT.le
    have hq0 := ((hq 0 left_mem_uIcc).tendsto).mono_left hnhds
    simp only [intervalIntegral.integral_same] at hq0
    have hUpper := (tendsto_const_nhds (x := ∫ s : ℝ in (0 : ℝ)..T, g s)).sub hq0
    have hLower := hnear.neg
    simp only [sub_zero] at hUpper
    simp only [neg_zero] at hLower
    apply le_of_tendsto_of_tendsto hLower hUpper
    filter_upwards [self_mem_nhdsWithin, (show ∀ᶠ a : ℝ in 𝓝 (0 : ℝ), a < T from Iio_mem_nhds hT).filter_mono
        nhdsWithin_le_nhds]
      with a ha haT
    have ha₀ : 0 < a := ha
    have haT' : a < T := haT
    have hsub : uIcc a T ⊆ Ioi 0 := by
      rw [uIcc_of_le haT'.le]
      exact fun x hx => ha₀.trans_le hx.1
    have hInt' : IntervalIntegrable (fun s : ℝ => H s * deriv f s) volume a T :=
      (hH.continuousOn.mul (hcont_deriv.mono hsub)).intervalIntegrable
    have hIntg : IntervalIntegrable g volume a T :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le haT'.le).mpr
        (hInt.mono_set fun x hx => ha₀.trans hx.1)
    have hIBP := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := T)
      (fun s hs => (hHd s).mul (hfd s (hsub hs))) (hIntg.add hInt')
    rw [intervalIntegral.integral_add hIntg hInt'] at hIBP
    have hnonpos : (∫ s : ℝ in a..T, H s * deriv f s) ≤ 0 :=
      by
        rw [intervalIntegral.integral_of_le haT'.le]
        apply integral_nonpos_of_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact mul_nonpos_of_nonneg_of_nonpos (hHpos s (ha₀.trans hs.1)) (hderiv s (ha₀.trans hs.1))
    have haInt : IntervalIntegrable g volume 0 a :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ha₀.le).mpr
        (hInt.mono_set Ioc_subset_Ioi_self)
    have hsplit := intervalIntegral.integral_add_adjacent_intervals haInt hIntg
    change (∫ s : ℝ in a..T, g s) + (∫ s : ℝ in a..T, H s * deriv f s) =
      H T * f T - H a * f a at hIBP
    linarith [mul_nonneg (hHpos T hT) (hf₀ T hT)]
  have hlim := intervalIntegral_tendsto_integral_Ioi 0 hInt tendsto_id
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  exact hfinite T hT

end ACS12.GammaDeficit

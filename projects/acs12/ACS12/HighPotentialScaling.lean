import ACS12.HighSlopeScaling

/-! The full high source potential has its original quadratic decay bound. -/
namespace ACS12.Pressure

open Set MeasureTheory Filter CenteredCircle.AllN
open GammaMeasure

theorem high_imagePotential_scaled_upper {p L t u : ℝ} (hp : 2 ≤ p)
    (hL : 0 < L) (ht : 0 < t) (htu : t ≤ u) :
    imagePotential p L u ≤ (t / u) ^ 2 * imagePotential p L t := by
  let c := u / t
  have hp₀ := (by linarith only [hp] : 0 < p)
  have hu := ht.trans_le htu
  have hc : 0 < c := div_pos hu ht
  have hc₁ : 1 ≤ c := (le_div_iff₀ ht).mpr (by simpa only [one_mul] using htu)
  let f (s : ℝ) := imageDensity p L s * Real.exp (-s * t)
  let g (s : ℝ) := imageDensity p L (s / c) * Real.exp (-s * t)
  have hEq (s : ℝ) : g (s * c) = imageDensity p L s * Real.exp (-s * u) := by
    dsimp only [g]
    rw [mul_div_cancel_right₀ _ hc.ne']
    congr 2
    dsimp only [c]
    field_simp [ht.ne']
  have hf : IntegrableOn f (Ioi 0) := imagePotential_integrable hp₀ hL ht
  have hg : IntegrableOn g (Ioi 0) := by
    have h : IntegrableOn (fun s => g (s * c)) (Ioi 0) :=
      (imagePotential_integrable hp₀ hL hu).congr (Eventually.of_forall fun s => (hEq s).symm)
    simpa only [zero_mul] using (integrableOn_Ioi_comp_mul_right_iff g 0 hc).mp h
  have hPoint (s : ℝ) (hs : 0 < s) : g s ≤ c⁻¹ * f s := by
    have hS := div_pos hs hc
    have h := imageDensity_div_monotone hp hL
      (mem_Ioi.mpr hS) (mem_Ioi.mpr hs) (div_le_self hs.le hc₁)
    have h' := (div_le_iff₀ hS).mp h
    have hW : imageDensity p L (s / c) ≤ c⁻¹ * imageDensity p L s := by
      have hE : imageDensity p L s / s * (s / c) = c⁻¹ * imageDensity p L s := by field_simp [hs.ne',hc.ne']
      rwa [hE] at h'
    simpa only [g,f,mul_assoc] using mul_le_mul_of_nonneg_right hW (Real.exp_pos (-s * t)).le
  have hCmp := setIntegral_mono_on hg (hf.const_mul (c⁻¹)) measurableSet_Ioi hPoint
  rw [integral_const_mul] at hCmp
  have hI : imagePotential p L u = c⁻¹ * ∫ s : ℝ in Ioi 0, g s := by
    unfold imagePotential
    rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => (hEq s).symm),
      integral_comp_mul_right_Ioi g 0 hc,zero_mul,smul_eq_mul]
  have hF : c⁻¹ * c⁻¹ = (t / u) ^ 2 := by
    rw [show t / u = c⁻¹ by unfold c; rw [inv_div],pow_two]
  rw [hI,← hF,mul_assoc]
  exact mul_le_mul_of_nonneg_left hCmp (inv_nonneg.mpr hc.le)

end ACS12.Pressure

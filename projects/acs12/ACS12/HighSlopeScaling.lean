import ACS12.GammaSourceElasticity
import ACS12.PressureUnit

/-! Full shifted-slope comparison under the high Gamma likelihood. -/
namespace ACS12.Pressure

open Set Filter MeasureTheory CenteredCircle.AllN
open GammaMeasure
open GammaDeficit (lineDensity)

theorem high_imageSlope_scaled_lower {p L t u : ℝ} (hp : 2 ≤ p)
    (hL : 0 < L) (ht : 0 < t) (htu : t ≤ u) :
    (t / u) ^ (p + 1) * imageSlope p L t ≤ imageSlope p L u := by
  let c := u / t
  have hp₀ : 0 < p := by linarith only [hp]
  have hu := ht.trans_le htu
  have hc : 0 < c := div_pos hu ht
  have hc₁ : 1 ≤ c := (le_div_iff₀ ht).mpr (by simpa only [one_mul] using htu)
  let f (s : ℝ) := imageDensity p L s * s * Real.exp (-s * t)
  let g (s : ℝ) := imageDensity p L (s / c) * (s / c) * Real.exp (-s * t)
  have hEq (s : ℝ) : g (s * c) = imageDensity p L s * s * Real.exp (-s * u) := by
    dsimp only [g]
    rw [mul_div_cancel_right₀ _ hc.ne']
    have h : -(s * c) * t = -s * u := by dsimp only [c]; field_simp [ht.ne']
    rw [h]
  have hf : IntegrableOn f (Ioi 0) := imageSlope_integrable hp₀ hL ht
  have hg : IntegrableOn g (Ioi 0) := by
    have h : IntegrableOn (fun s => g (s * c)) (Ioi 0) :=
      (imageSlope_integrable hp₀ hL hu).congr (Eventually.of_forall fun s => (hEq s).symm)
    simpa only [zero_mul] using (integrableOn_Ioi_comp_mul_right_iff g 0 hc).mp h
  have hPoint (s : ℝ) (hs : 0 < s) : c ^ (-p) * f s ≤ g s := by
    have hd := div_pos hs hc
    have hLe := div_le_self hs.le hc₁
    have h := imageDensity_div_lineDensity_antitone hp hL hd hs hLe
    have hρ : lineDensity p (s / c) = c ^ (1 - p) * lineDensity p s := by
      unfold lineDensity
      rw [Real.div_rpow hs.le hc.le,show 1 - p = -(p - 1) by ring,Real.rpow_neg hc.le]
      ring
    have h' := (div_le_div_iff₀ (lineDensity_pos hp₀ hs) (lineDensity_pos hp₀ hd)).mp h
    rw [hρ] at h'
    have hW : c ^ (1 - p) * imageDensity p L s ≤ imageDensity p L (s / c) :=
      (mul_le_mul_iff_right₀ (lineDensity_pos hp₀ hs)).mp (by nlinarith only [h'])
    have hS := mul_le_mul_of_nonneg_right hW (show 0 ≤ (s / c) * Real.exp (-s * t) by positivity)
    have hPow : c ^ (1 - p) / c = c ^ (-p) := by
      rw [← Real.rpow_sub_one hc.ne',show 1 - p - 1 = -p by ring]
    calc
      _ = (c ^ (1 - p) / c) * (imageDensity p L s * s * Real.exp (-s * t)) := by rw [hPow]
      _ = (c ^ (1 - p) * imageDensity p L s) * (s / c * Real.exp (-s * t)) := by ring
      _ ≤ _ := hS.trans_eq (by unfold g; ring)
  have hC := setIntegral_mono_on (hf.const_mul (c ^ (-p))) hg measurableSet_Ioi hPoint
  rw [integral_const_mul] at hC
  have hI : imageSlope p L u = c⁻¹ * ∫ s : ℝ in Ioi 0, g s := by
    unfold imageSlope
    rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => (hEq s).symm),
      integral_comp_mul_right_Ioi g 0 hc,zero_mul,smul_eq_mul]
  have hPow : (t / u) ^ (p + 1) = c⁻¹ * c ^ (-p) := by
    have hFrac : t / u = c⁻¹ := by unfold c; rw [inv_div]
    rw [hFrac,Real.inv_rpow hc.le,Real.rpow_add hc,Real.rpow_one,mul_inv_rev,
      Real.rpow_neg hc.le]
  rw [hI,hPow,mul_assoc]
  exact mul_le_mul_of_nonneg_left hC (inv_nonneg.mpr hc.le)

end ACS12.Pressure

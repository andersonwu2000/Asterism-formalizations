import ACS12.HighMaximumReference
import ACS12.PressureMaximum

/-! Exact simultaneous scaling of the full Gamma density and maximum fee. -/
namespace ACS12.GammaMeasure

open Set MeasureTheory

theorem imageDensity_mass_scale {p L Q s : ℝ} (hL : 0 < L) (hQ : 0 < Q) :
    imageDensity p L (s / Q) = Q ^ (1 - p) * imageDensity p (L / Q) s := by
  have hArg : L * (s / Q) = (L / Q) * s := by ring
  have hPow : Q ^ (1 - p) * (L / Q) ^ (1 - p) = L ^ (1 - p) := by
    rw [Real.div_rpow hL.le hQ.le]
    field_simp [(Real.rpow_pos_of_pos hQ (1 - p)).ne']
  unfold imageDensity
  rw [hArg]
  calc
    _ = Q ^ (1 - p) * (L / Q) ^ (1 - p) *
        ((2 : ℝ) ^ (p - 1) * Real.pi ^ (p - 2) / Real.Gamma p *
          Real.sinh (L / Q * s / 2) *
          ‖Complex.Gamma ((p / 2 : ℝ) + ((L / Q * s / (2 * Real.pi) : ℝ) : ℂ) * Complex.I)‖ ^ 2) := by rw [hPow]; ring
    _ = _ := by ring

theorem imageIntegral_mass_scale {p L Q : ℝ} (hL : 0 < L) (hQ : 0 < Q) (f : ℝ → ℝ) :
    (∫ s : ℝ in Ioi 0, imageDensity p L s * f (Q * s)) =
      Q ^ (-p) * ∫ s : ℝ in Ioi 0, imageDensity p (L / Q) s * f s := by
  let g (s : ℝ) := imageDensity p (L / Q) s * f s
  have hD (s : ℝ) : imageDensity p L s = Q ^ (1 - p) * imageDensity p (L / Q) (Q * s) := by
    simpa only [mul_div_cancel_left₀ s hQ.ne'] using imageDensity_mass_scale (s := Q * s) hL hQ
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun s => Q ^ (1 - p) * g (Q * s))
    (fun s _ => by rw [hD]; unfold g; ring),integral_const_mul,
    integral_comp_mul_left_Ioi g 0 hQ,mul_zero,smul_eq_mul,← mul_assoc]
  have hPow : Q ^ (1 - p) * Q⁻¹ = Q ^ (-p) := by
    rw [← div_eq_mul_inv,← Real.rpow_sub_one hQ.ne',show 1 - p - 1 = -p by ring]
  rw [hPow]

theorem imagePotential_mass_scale {p L Q t : ℝ} (hL : 0 < L) (hQ : 0 < Q) :
    imagePotential p L (Q * t) = Q ^ (-p) * imagePotential p (L / Q) t := by
  unfold imagePotential
  convert imageIntegral_mass_scale (p := p) hL hQ (fun s => Real.exp (-s * t)) using 1
  congr 1
  ext s
  congr 2
  ring

theorem maximumDebit_normalized {p L Q : ℝ} (hL : 0 < L) (hQ : 0 < Q) :
    Pressure.maximumDebit p L Q / (Q * imagePotential p L Q) = maximumActualFee p (L / Q) := by
  have hFee (s : ℝ) : Pressure.pressureWeight p L s * Pressure.pressureBose Q s ^ 2 =
      Q * (imageDensity p L s * (Real.exp (-(Q * s)) * maximumFeeShape (Q * s))) := by
    unfold Pressure.pressureWeight Pressure.pressureBose Pressure.periodicDen maximumFeeShape
    rw [show -s * Q = -(Q * s) by ring]
    simp only [Real.exp_neg]
    field_simp
    <;> ring
  have hD : Pressure.maximumDebit p L Q =
      (Q * Q ^ (-p)) * ∫ s : ℝ in Ioi 0, imageDensity p (L / Q) s * Real.exp (-s) * maximumFeeShape s := by
    unfold Pressure.maximumDebit
    rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => hFee s),integral_const_mul,
      imageIntegral_mass_scale hL hQ (fun s => Real.exp (-s) * maximumFeeShape s)]
    rw [mul_assoc]
    congr 2
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun s => by ring
  have hK : imagePotential p L Q = Q ^ (-p) * imagePotential p (L / Q) 1 := by
    simpa only [mul_one] using imagePotential_mass_scale (t := 1) hL hQ
  unfold maximumActualFee
  rw [hD,hK]
  field_simp [(Real.rpow_pos_of_pos hQ (-p)).ne',hQ.ne']

end ACS12.GammaMeasure

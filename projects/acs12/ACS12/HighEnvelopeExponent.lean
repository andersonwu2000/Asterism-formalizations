import ACS12.HighEnvelopeExponentPayment

/-! Separate exponent convexity of the complete clipped high pressure envelope. -/
namespace ACS12.Pressure

open Set

theorem highPressureEnvelope_convex_exponent {R : ℝ} (hR : 0 < R) (hRU : R ≤ 33 / 10) :
    ConvexOn ℝ (Icc 2 4) (fun p => highPressureEnvelope p R) := by
  let c := Real.sqrt (R / 7)
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have hcSq : c ^ 2 = R / 7 := Real.sq_sqrt (by positivity)
  have hCap : c ^ 2 ≤ 33 / 70 := by rw [hcSq]; linarith only [hRU]
  have hScale (p : ℝ) (hp : 0 < p) :
      highPressureScale p R = highExponentScale c p := by
    unfold highPressureScale highExponentScale c
    rw [show R / (7 * p) = (R / 7) / p by ring,Real.sqrt_div]
    simp only [Real.sqrt_eq_rpow,Real.rpow_neg hp.le,div_eq_mul_inv]
    positivity
  have hB (p : ℝ) (hp : p ∈ Icc 2 4) :
      highMinimumUnitPrice p (highPressureScale p R) = highExponentLinear c p + highExponentTail c p := by
    have hp₀ : 0 < p := by linarith only [hp.1]
    rw [hScale p hp₀,highExponentTail_eq hc hp₀]
    rfl
  have hConst : ConvexOn ℝ (Icc (2 : ℝ) 4) (fun _ => (1 : ℝ)) := convexOn_const (c := (1 : ℝ)) (convex_Icc 2 4)
  have h : 0 ≤ R / 2 := by positivity
  have hConvex := ConvexOn.smul h (hConst.sup (highExponent_combined_convex hc hCap))
  simp only [smul_eq_mul] at hConvex
  apply hConvex.congr
  intro p hp
  change R / 2 * max 1 (highExponentLinear c p + highExponentTail c p) = highPressureEnvelope p R
  rw [highPressureEnvelope_eq hR]
  unfold highPressureSmooth
  rw [hB p hp,mul_max_of_nonneg _ _ h,mul_one]

end ACS12.Pressure

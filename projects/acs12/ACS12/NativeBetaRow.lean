import ACS12.NativeTranslatedSpectrum
import ACS12.GammaOrdinaryOrder

/-! Ordinary-beta order for the original Bose integral and its fixed zero-count normalization. -/
namespace ACS12.NativeCells
open MeasureTheory Set GammaMeasure

noncomputable def nativeBetaCoefficient (p : ℝ) : ℝ :=
  nativeGammaScale p * Real.Gamma (p/2)^2 / 6

noncomputable def nativeBetaShape (p z : ℝ) : ℝ :=
  24 * ∫ x : ℝ in Ioi 0, baseBose x * gammaNormalizedRatio (p/2) (Real.sqrt z*x)

theorem nativeBetaCoefficient_pos {p : ℝ} (hp : 0 < p) : 0 < nativeBetaCoefficient p := by
  unfold nativeBetaCoefficient nativeGammaScale
  positivity

private theorem normalizedBose_integrable {p N : ℝ} (hp : 0 < p) (hN : 0 ≤ N) :
    IntegrableOn (fun x => baseBose x * gammaNormalizedRatio (p/2) (N*x)) (Ioi 0) := by
  rcases hN.eq_or_lt with rfl | hN
  · simpa only [zero_mul,gammaNormalizedRatio_zero (by positivity : 0 < p/2),mul_one] using
      baseBose_calibration.1
  · have h := (boseRow_scaled_ratio hp hN).1.const_mul ((Real.Gamma (p/2)^2)⁻¹)
    apply h.congr
    exact Filter.Eventually.of_forall fun x => by
      dsimp only
      rw [gammaModulusRatio_eq_normalized (by positivity : 0 < p/2)]
      field_simp [(Real.Gamma_pos_of_pos (by positivity : 0 < p/2)).ne']
      <;> ring

theorem nativeBetaShape_zero {p : ℝ} (hp : 0 < p) : nativeBetaShape p 0 = 1 := by
  unfold nativeBetaShape
  simp only [Real.sqrt_zero,zero_mul,gammaNormalizedRatio_zero (by positivity : 0 < p/2),mul_one]
  rw [baseBose_calibration.2]
  norm_num

theorem boseRow_beta_normalization {p N : ℝ} (hp : 0 < p) (hN : 0 < N) :
    boseRow p N / N^2 = nativeBetaCoefficient p * nativeBetaShape p (N^2) := by
  rw [(boseRow_scaled_ratio hp hN).2]
  have hPoint : (fun x => baseBose x * gammaModulusRatio (p/2) (N*x)) =
      (fun x => Real.Gamma (p/2)^2 * (baseBose x * gammaNormalizedRatio (p/2) (N*x))) := by
    funext x
    rw [gammaModulusRatio_eq_normalized (by positivity : 0 < p/2)]
    ring
  rw [hPoint,integral_const_mul]
  unfold nativeBetaCoefficient nativeBetaShape
  rw [Real.sqrt_sq hN.le]
  ring

theorem nativeBetaShape_mono {p r z : ℝ} (hp : 0 < p) (hpr : p ≤ r) :
    nativeBetaShape p z ≤ nativeBetaShape r z := by
  have hr := hp.trans_le hpr
  unfold nativeBetaShape
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply setIntegral_mono_on (normalizedBose_integrable hp (Real.sqrt_nonneg z))
    (normalizedBose_integrable hr (Real.sqrt_nonneg z)) measurableSet_Ioi
  intro x hx
  change 0 < x at hx
  have hB : 0 ≤ baseBose x := by
    unfold baseBose
    exact div_nonneg hx.le (CenteredCircle.AllN.expTail_den_pos (by positivity : 0 < 2*Real.pi*x)).le
  exact mul_le_mul_of_nonneg_left
    (gammaNormalizedRatio_mono (by positivity : 0 < p/2) (by linarith : p/2 ≤ r/2) _) hB

end ACS12.NativeCells

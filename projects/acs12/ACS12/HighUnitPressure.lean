import ACS12.HighSlopeScaling

/-! The actual exponent-dependent incident pressure on the original source. -/
namespace ACS12.Pressure

open Set Filter MeasureTheory CenteredCircle.AllN
open GammaMeasure

theorem high_pressure_unit_gt {n : ℕ} {p : ℝ} (hp : 2 ≤ p)
    (F : Configuration n p) (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi)) :
    let S := C.source
    let b := S.mass S.neighbor
    b * imageSlope p S.period 1 * (1 + b * (2 : ℝ) ^ (-(p + 1))) < pressureAt p S S.root := by
  have hp₀ : 0 < p := by linarith only [hp]
  let S := C.source
  let L := S.period
  let i := S.root
  let j := S.neighbor
  let b := S.mass j
  let W := pressureWeight p L
  let A := leftRay S i
  let B := rightRay S i
  let d (k : Fin n) := S.forwardDistance k i
  let e (k : Fin n) := S.forwardDistance i k
  have hL := S.period_pos
  have hb := S.mass_pos j
  have hD (k : Fin n) : 1 ≤ d k := by
    by_cases hk : k = i
    · subst k
      dsimp only [d]
      rw [S.forwardDistance_self]
      linarith only [S.period_ge_two]
    · have h := (S.forwardDistance_caps C.circular_caps hk).2
      change S.mass i ≤ d k at h
      simpa only [i,S.mass_root] using h
  have hA_nonneg (s : ℝ) (hs : 0 < s) : 0 ≤ A s := by
    unfold A leftRay rayWeight
    apply Finset.sum_nonneg
    intro k _
    exact mul_nonneg (S.mass_pos k).le (div_nonneg (Real.exp_pos _).le (periodicDen_pos hL hs).le)
  have hAi : IntegrableOn (fun s => W s * A s) (Ioi 0) := ray_integrable hp₀ hL S.mass d (fun k => S.forwardDistance_pos k i)
  have hBi : IntegrableOn (fun s => W s * B s) (Ioi 0) := ray_integrable hp₀ hL S.mass e (S.forwardDistance_pos i)
  have hAB : IntegrableOn (fun s => W s * (A s * B s)) (Ioi 0) :=
    rays_product_integrable_all hp₀ hL S.mass d e (fun k => S.forwardDistance_pos k i) (S.forwardDistance_pos i)
  have hShift : IntegrableOn (fun s => W s * (Real.exp (-s) * A s)) (Ioi 0) := by
    apply (ray_integrable hp₀ hL S.mass (fun k => d k + 1) (fun k => by have := hD k; positivity)).congr
    exact Eventually.of_forall fun s => by dsimp only [W,A,leftRay]; rw [shifted_ray_eq]
  have hAeq := ray_slope_integral hp₀ hL S.mass d (fun k => S.forwardDistance_pos k i)
  have hTor := ray_slope_torque_eq hp₀ F C i
  change (∫ s : ℝ in Ioi 0, W s * A s) = ∫ s : ℝ in Ioi 0, W s * B s at hTor
  let U := imageSlope p L
  have hShiftBound : ((2 : ℝ) ^ (-(p + 1))) * (∫ s : ℝ in Ioi 0, W s * A s) ≤
      ∫ s : ℝ in Ioi 0, W s * (Real.exp (-s) * A s) := by
    change ((2 : ℝ) ^ (-(p + 1))) * (∫ s : ℝ in Ioi 0, pressureWeight p L s * rayWeight L S.mass d s) ≤ _
    rw [hAeq, setIntegral_congr_fun measurableSet_Ioi (g := fun s =>
      pressureWeight p L s * rayWeight L S.mass (fun k => d k + 1) s)
      (fun s _ => by dsimp only [W,A,leftRay]; rw [shifted_ray_eq]),
      ray_slope_integral hp₀ hL S.mass _ (fun k => by have := hD k; positivity),Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    rw [show ((2 : ℝ) ^ (-(p + 1))) * (S.mass k * imageTail U L (d k)) = S.mass k * (((2 : ℝ) ^ (-(p + 1))) * imageTail U L (d k)) by ring]
    apply mul_le_mul_of_nonneg_left _ (S.mass_pos k).le
    have hI := (imageSlope_samples_hasSum hp₀ hL (S.forwardDistance_pos k i)).summable
    have hI' := (imageSlope_samples_hasSum hp₀ hL (show 0 < d k + 1 by have := hD k; positivity)).summable
    unfold imageTail
    rw [← tsum_mul_left]
    apply (hI.mul_left ((2 : ℝ) ^ (-(p + 1)))).tsum_le_tsum _ hI'
    intro n
    let t := d k + (n : ℝ) * L
    have ht : 1 ≤ t := le_add_of_nonneg_right (by positivity) |>.trans' (hD k)
    have ht₀ := zero_lt_one.trans_le ht
    have hU₀ : 0 ≤ U t := by
      unfold U imageSlope
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact mul_nonneg (mul_nonneg (imageDensity_pos hp₀ hL hs).le (show 0 < s from hs).le) (Real.exp_pos _).le
    have hFrac : (1 / 2 : ℝ) ≤ t / (t + 1) := (le_div_iff₀ (by positivity)).mpr (by linarith only [ht])
    have hPow := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2) hFrac
      (by linarith only [hp] : 0 ≤ p + 1)
    have h := (mul_le_mul_of_nonneg_right hPow hU₀).trans
      (high_imageSlope_scaled_lower hp hL ht₀ (by linarith : t ≤ t + 1))
    change ((2 : ℝ) ^ (-(p + 1))) * U t ≤ U (d k + 1 + (n : ℝ) * L)
    rw [show d k + 1 + (n : ℝ) * L = t + 1 by dsimp only [t]; ring]
    have hPowEq : (1 / 2 : ℝ) ^ (p + 1) = (2 : ℝ) ^ (-(p + 1)) := by
      rw [one_div,Real.inv_rpow (by norm_num),Real.rpow_neg (by norm_num)]
    rwa [hPowEq] at h
  have hTB : b * U 1 < ∫ s : ℝ in Ioi 0, W s * B s := root_right_slope_gt hp₀ S
  have hProd := setIntegral_mono_on (hShift.const_mul b) hAB measurableSet_Ioi (fun s hs => by
    have h := mul_le_mul_of_nonneg_left (root_rightRay_neighbor_lt S hs).le (hA_nonneg s hs)
    have hW : 0 ≤ W s := mul_nonneg (imageDensity_pos hp₀ hL hs).le (show 0 < s from hs).le
    linarith only [mul_le_mul_of_nonneg_left h hW])
  rw [integral_const_mul] at hProd
  have hPi : pressureAt p S i = (∫ s : ℝ in Ioi 0, W s * (A s * B s)) + ∫ s : ℝ in Ioi 0, W s * B s := by
    unfold pressureAt
    rw [show S.mass i = 1 from S.mass_root]
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun s => W s * (A s * B s) + W s * B s)
      (fun s _ => by dsimp only [W,A,B]; ring),integral_add hAB hBi]
  have hS := mul_le_mul_of_nonneg_left hShiftBound hb.le
  rw [hTor] at hS
  have hT := mul_lt_mul_of_pos_left hTB (show 0 < 1 + b * (2 : ℝ) ^ (-(p + 1)) by positivity)
  change _ < pressureAt p S i
  rw [hPi]
  nlinarith only [hProd,hS,hT]

end ACS12.Pressure

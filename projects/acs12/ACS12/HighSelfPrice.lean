import ACS12.HighMinimumReference
import ACS12.PressureTestedImage

/-! The complete high-band literal self-ray price, with every image retained. -/
namespace ACS12.Pressure

open Set Filter MeasureTheory CenteredCircle.AllN
open GammaMeasure

theorem minimumSelfTest_quadratic {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    minimumAtomTest a a a s ≤ 1 + (a / 2) * s + (a ^ 2 / 12) * s ^ 2 := by
  have h := mul_lt_mul_of_pos_left (bose_inverse_B2 (mul_pos hs ha)) (mul_pos hs ha)
  have hD := (periodicDen_pos ha hs).ne'
  have hE : minimumAtomTest a a a s = (s * a) * (1 - Real.exp (-(s * a)))⁻¹ := by
    unfold minimumAtomTest oppositeRayBose pressureBose periodicDen
    simp only [sub_self,neg_zero,zero_mul,Real.exp_zero,one_mul]
    rw [show -s * a = -(s * a) by ring]
    have hD' : 1 - Real.exp (-(s * a)) ≠ 0 := by simpa only [periodicDen,neg_mul] using hD
    field_simp [hD']
    <;> ring
  rw [hE]
  have hInv : (s * a) * (s * a)⁻¹ = 1 := mul_inv_cancel₀ (mul_pos hs ha).ne'
  nlinarith only [h,hInv]

noncomputable def highSelfCoefficient (p : ℝ) : ℝ :=
  1 + p / 4 + p * (p + 1) / 48

theorem testedImage_self_high_le {p L a t : ℝ} (hp : 2 ≤ p) (hL : 0 < L)
    (ha : 0 < a) (ht : 0 < t) (haT : 2 * a ≤ t) :
    testedImage p L (minimumAtomTest a a a) t ≤ highSelfCoefficient p * imagePotential p L t := by
  have hp₀ : 0 < p := by linarith only [hp]
  let W (s : ℝ) := imageDensity p L s * Real.exp (-s * t)
  let M (j : ℕ) := sourceLaplaceMoment p L j t
  let G (s : ℝ) := W s * minimumAtomTest a a a s
  let U (s : ℝ) := W s + (a / 2) * (W s * s) + (a ^ 2 / 12) * (W s * s ^ 2)
  have hI (j : ℕ) : IntegrableOn (fun s => W s * s ^ j) (Ioi 0) := by
    simpa only [W,mul_right_comm] using sourceLaplaceMoment_integrable hp₀ hL ht j
  have hI₀ : IntegrableOn W (Ioi 0) := imagePotential_integrable hp₀ hL ht
  have hI₁ : IntegrableOn (fun s => W s * s) (Ioi 0) := by simpa only [pow_one] using hI 1
  have hU : IntegrableOn U (Ioi 0) := (hI₀.add (hI₁.const_mul (a / 2))).add ((hI 2).const_mul _)
  have hPoint (s : ℝ) (hs : 0 < s) : 0 ≤ G s ∧ G s ≤ U s := by
    have hw : 0 ≤ W s := mul_nonneg (imageDensity_pos hp₀ hL hs).le (Real.exp_pos _).le
    refine ⟨mul_nonneg hw (minimumAtomTest_bounds ha.le ha le_rfl hs).1,?_⟩
    have h := mul_le_mul_of_nonneg_left (minimumSelfTest_quadratic ha hs) hw
    unfold G U
    linarith only [h]
  have hG : IntegrableOn G (Ioi 0) := by
    have hMT : Measurable (minimumAtomTest a a a) := by
      unfold minimumAtomTest oppositeRayBose pressureBose periodicDen
      fun_prop
    have hM : Measurable G := ((continuous_imageDensity hp₀ hL).measurable.mul (by fun_prop)).mul hMT
    apply hU.mono' hM.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_of_nonneg (hPoint s hs).1]
    exact (hPoint s hs).2
  have hCmp := setIntegral_mono_on hG hU measurableSet_Ioi (fun s hs => (hPoint s hs).2)
  have hMom (j : ℕ) : (∫ s : ℝ in Ioi 0, W s * s ^ j) = M j := by
    unfold M sourceLaplaceMoment W
    apply integral_congr_ae
    exact Eventually.of_forall fun s => by ring
  have h0 : (∫ s : ℝ in Ioi 0, W s) = M 0 := by simpa only [pow_zero,mul_one] using hMom 0
  have h1 : (∫ s : ℝ in Ioi 0, W s * s) = M 1 := by simpa only [pow_one] using hMom 1
  have hUE : (∫ s : ℝ in Ioi 0, U s) = M 0 + (a / 2) * M 1 + (a ^ 2 / 12) * M 2 := by
    unfold U
    rw [integral_add (f := fun s => W s + (a / 2) * (W s * s)) (g := fun s => (a ^ 2 / 12) * (W s * s ^ 2))
      (hI₀.add (hI₁.const_mul _)) ((hI 2).const_mul _),
      integral_add hI₀ (hI₁.const_mul _),integral_const_mul,integral_const_mul,h0,h1,hMom 2]
  rw [hUE] at hCmp
  have hM₀ (j : ℕ) : 0 ≤ M j := by
    unfold M sourceLaplaceMoment
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_nonneg (mul_nonneg (imageDensity_pos hp₀ hL hs).le (pow_nonneg (show 0 < s from hs).le _)) (Real.exp_pos _).le
  have hB₀ := (sourceLaplaceMoment_bounds hp hL ht 0).2
  have hB₁ := (sourceLaplaceMoment_bounds hp hL ht 1).2
  norm_num only [Nat.cast_zero,Nat.cast_one,zero_add,Nat.reduceAdd] at hB₀ hB₁
  change t * M 1 ≤ p * M 0 at hB₀
  change t * M 2 ≤ (1 + p) * M 1 at hB₁
  have hTM₂ : t ^ 2 * M 2 ≤ p * (p + 1) * M 0 := by
    have h := mul_le_mul_of_nonneg_left hB₁ ht.le
    have h' := mul_le_mul_of_nonneg_left hB₀ (show 0 ≤ p + 1 by positivity)
    nlinarith only [h,h']
  have hAM₁ : a * M 1 ≤ (p / 2) * M 0 := by
    have h := mul_le_mul_of_nonneg_right haT (hM₀ 1)
    linarith only [h,hB₀]
  have hA₂ : a ^ 2 ≤ t ^ 2 / 4 := by nlinarith only [haT,ha,ht,sq_nonneg (t - 2 * a)]
  have hAM₂ : a ^ 2 * M 2 ≤ (p * (p + 1) / 4) * M 0 := by
    have h := mul_le_mul_of_nonneg_right hA₂ (hM₀ 2)
    nlinarith only [h,hTM₂]
  have hPrice : M 0 + (a / 2) * M 1 + (a ^ 2 / 12) * M 2 ≤ highSelfCoefficient p * M 0 := by
    unfold highSelfCoefficient
    linarith only [hAM₁,hAM₂]
  have hK : M 0 = imagePotential p L t := by simp only [M,sourceLaplaceMoment,imagePotential,pow_zero,mul_one]
  change (∫ s : ℝ in Ioi 0, imageDensity p L s * minimumAtomTest a a a s * Real.exp (-s * t)) ≤ _
  have hGE : (∫ s : ℝ in Ioi 0, imageDensity p L s * minimumAtomTest a a a s * Real.exp (-s * t)) =
      ∫ s : ℝ in Ioi 0, G s := by
    apply integral_congr_ae
    exact Eventually.of_forall fun s => by unfold G W; ring
  rw [hGE,← hK]
  exact hCmp.trans hPrice

end ACS12.Pressure

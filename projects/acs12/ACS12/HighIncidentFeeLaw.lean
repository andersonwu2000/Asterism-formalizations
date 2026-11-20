import ACS12.HighIncidentFee
import ACS12.GammaSourceElasticity
import ACS12.PressureLikelihood

/-! The exact high incident fee against the actual density and the common parameter chord. -/
namespace ACS12.GammaMeasure

open Set Filter MeasureTheory CenteredCircle.AllN
open GammaDeficit (lineDensity_exp_integral)

private noncomputable def formalIncidentFee (u : ℝ) : ℝ :=
  ∫ s : ℝ in Ioi 0, highIncidentFeeWeight s * highIncidentFeeTest u (u - 1 / 8) s

private theorem formalIncidentFee_convex :
    ConvexOn ℝ (Icc (1 / 4 : ℝ) (1 / 3)) formalIncidentFee := by
  refine ⟨convex_Icc _ _,?_⟩
  intro x hx y hy a b ha hb hab
  let t := a * x + b * y
  let F (u s : ℝ) := highIncidentFeeWeight s * highIncidentFeeTest u (u - 1 / 8) s
  have ht : t ∈ Icc (1 / 4 : ℝ) (1 / 3) := convex_Icc _ _ hx hy ha hb hab
  have hI (u : ℝ) (hu : u ∈ Icc (1 / 4 : ℝ) (1 / 3)) : IntegrableOn (F u) (Ioi 0) :=
    highIncidentFee_integrable ((by norm_num : (0 : ℝ) ≤ 1 / 4).trans hu.1) (by linarith only [hu.1])
  have h := integral_mono_ae (hI t ht) (((hI x hx).const_mul a).add ((hI y hy).const_mul b)) ?_
  · simp only [Pi.add_apply] at h
    rw [integral_add ((hI x hx).const_mul a) ((hI y hy).const_mul b),integral_const_mul,integral_const_mul] at h
    exact h
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hW : 0 ≤ highIncidentFeeWeight s := mul_nonneg (show 0 < s from hs).le (Real.exp_pos _).le
    have hF : highIncidentFeeRaw t (t - 1 / 8) s =
        a * highIncidentFeeRaw x (x - 1 / 8) s + b * highIncidentFeeRaw y (y - 1 / 8) s := by
      unfold t highIncidentFeeRaw
      linear_combination (-(7 / 8 : ℝ) - expHeadFactor s / 8 + s / 8) * hab
    have hX : 0 ≤ highIncidentFeeTest x (x - 1 / 8) s := le_max_left _ _
    have hY : 0 ≤ highIncidentFeeTest y (y - 1 / 8) s := le_max_left _ _
    have hT : highIncidentFeeTest t (t - 1 / 8) s ≤
        a * highIncidentFeeTest x (x - 1 / 8) s + b * highIncidentFeeTest y (y - 1 / 8) s := by
      unfold highIncidentFeeTest
      rw [hF]
      exact max_le (add_nonneg (mul_nonneg ha hX) (mul_nonneg hb hY))
        (add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) ha)
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hb))
    have h := mul_le_mul_of_nonneg_left hT hW
    change F t s ≤ a * F x s + b * F y s
    unfold F
    nlinarith only [h]

private theorem formalIncidentFee_lt {u : ℝ} (hu : 1 / 4 ≤ u) (hu' : u ≤ 1 / 3) :
    formalIncidentFee u < 31 / 40 - (39 / 40) * u := by
  let z := 12 * (u - 1 / 4)
  have hz : 0 ≤ z := by unfold z; linarith only [hu]
  have hz' : z ≤ 1 := by unfold z; linarith only [hu']
  have hz₁ : 0 ≤ 1 - z := sub_nonneg.mpr hz'
  have h := formalIncidentFee_convex.2 (show (1 / 4 : ℝ) ∈ Icc (1 / 4 : ℝ) (1 / 3) by norm_num)
    (show (1 / 3 : ℝ) ∈ Icc (1 / 4 : ℝ) (1 / 3) by norm_num) hz₁ hz (sub_add_cancel 1 z)
  simp only [smul_eq_mul] at h
  rw [show (1 - z) * (1 / 4 : ℝ) + z * (1 / 3) = u by unfold z; ring] at h
  have h₀ : formalIncidentFee (1 / 4) < 17 / 32 := by
    unfold formalIncidentFee
    convert highIncidentFee_one_fourth_lt using 2 <;> norm_num
  have h₁ : formalIncidentFee (1 / 3) < 9 / 20 := by
    unfold formalIncidentFee
    convert highIncidentFee_one_third_lt using 2 <;> norm_num
  have hS : (1 - z) * formalIncidentFee (1 / 4) + z * formalIncidentFee (1 / 3) <
      (1 - z) * (17 / 32) + z * (9 / 20) := by
    rcases lt_or_eq_of_le hz with hzP | hzZ
    · exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left h₀.le hz₁)
        (mul_lt_mul_of_pos_left h₁ hzP)
    · simpa only [← hzZ,sub_zero,one_mul,zero_mul,add_zero] using h₀
  have he : (1 - z) * (17 / 32) + z * (9 / 20) = 31 / 40 - (39 / 40) * u := by unfold z; ring
  exact (h.trans_lt hS).trans_eq he

noncomputable def highIncidentActualFee (p L u c : ℝ) : ℝ :=
  ∫ s : ℝ in Ioi 0, imageDensity p L s * Real.exp (-s) * highIncidentFeeTest u c s

theorem highIncidentActualFee_integrable {p L u c : ℝ} (hp : 0 < p) (hL : 0 < L) (hu : 0 ≤ u) (hc : 0 ≤ c) :
    IntegrableOn (fun s => imageDensity p L s * Real.exp (-s) * highIncidentFeeTest u c s) (Ioi 0) := by
  have hM : Measurable (fun s => imageDensity p L s * Real.exp (-s) * highIncidentFeeTest u c s) :=
    (((continuous_imageDensity hp hL).measurable.mul (by fun_prop)).mul (highIncidentFee_measurable u c))
  have hB : IntegrableOn (fun s => imageDensity p L s * Real.exp (-s)) (Ioi 0) := by
    simpa only [mul_one] using imagePotential_integrable hp hL zero_lt_one
  apply (hB.const_mul (1 + c)).mono' hM.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hW := mul_nonneg (imageDensity_pos hp hL hs).le (Real.exp_pos (-s)).le
  have hT : 0 ≤ highIncidentFeeTest u c s := le_max_left _ _
  rw [Real.norm_of_nonneg (mul_nonneg hW hT)]
  have h := mul_le_mul_of_nonneg_left (highIncidentFee_le hs hu hc) hW
  nlinarith only [h]

theorem highIncidentActualFee_lt {p L u c : ℝ} (hp : 2 ≤ p) (hL : 0 < L)
    (hu : 1 / 4 ≤ u) (hu' : u ≤ 1 / 3) (hc : 0 ≤ c) (hcU : c ≤ u - 1 / 8) :
    highIncidentActualFee p L u c < imagePotential p L 1 * (31 / 40 - (39 / 40) * u) := by
  let W := highIncidentFeeWeight
  let V (s : ℝ) := imageDensity p L s * Real.exp (-s)
  let T := highIncidentFeeTest u c
  have hp₀ : 0 < p := by linarith only [hp]
  have hu₀ : 0 ≤ u := (by norm_num : (0 : ℝ) ≤ 1 / 4).trans hu
  have hc' : 0 ≤ u - 1 / 8 := by linarith only [hu]
  have hcu : c ≤ u := by linarith only [hcU]
  have hV : IntegrableOn V (Ioi 0) := by simpa only [V,mul_one] using imagePotential_integrable hp₀ hL zero_lt_one
  have hR : MonotoneOn (fun s => V s / W s) (Ioi 0) := by
    have he (s : ℝ) : V s / W s = imageDensity p L s / s := by
      unfold V W highIncidentFeeWeight
      exact mul_div_mul_right _ _ (Real.exp_ne_zero _)
    intro x hx y hy hxy
    change V x / W x ≤ V y / W y
    rw [he x,he y]
    exact imageDensity_div_monotone hp hL hx hy hxy
  have hW₁ : (∫ s : ℝ in Ioi 0, W s) = 1 := by
    have he (s : ℝ) : W s = GammaDeficit.lineDensity 2 s * Real.exp (-s * 1) := by
      unfold W highIncidentFeeWeight GammaDeficit.lineDensity
      norm_num
    rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => he s),
      lineDensity_exp_integral (by norm_num : (0 : ℝ) < 2) zero_lt_one,Real.one_rpow]
  have hV₁ : (∫ s : ℝ in Ioi 0, V s) = imagePotential p L 1 := by
    simp only [V,imagePotential,mul_one]
  have h := Pressure.likelihood_test_anti highIncidentFeeWeight_integrable hV
    (highIncidentFee_integrable hu₀ hc) (highIncidentActualFee_integrable hp₀ hL hu₀ hc)
    (fun s hs => mul_pos hs (Real.exp_pos _)) hR (highIncidentFee_antitone hc hcu)
  rw [hW₁,hV₁,mul_one] at h
  have hT : (∫ s : ℝ in Ioi 0, W s * T s) ≤ formalIncidentFee u := by
    apply integral_mono_ae (highIncidentFee_integrable hu₀ hc) (highIncidentFee_integrable hu₀ hc')
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_le_mul_of_nonneg_left (highIncidentFee_mono_coeff hs hcU)
      (mul_nonneg (show 0 < s from hs).le (Real.exp_pos _).le)
  exact h.trans_lt (mul_lt_mul_of_pos_right (hT.trans_lt (formalIncidentFee_lt hu hu'))
    (imagePotential_pos hp₀ hL zero_lt_one)) |>.trans_eq (mul_comm _ _)

end ACS12.GammaMeasure

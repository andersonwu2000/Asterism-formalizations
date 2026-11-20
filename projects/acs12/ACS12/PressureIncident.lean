import ACS12.HighIncidentEntrance
import ACS12.IncidentFeeGamma
import ACS12.PressureElasticity

/-! The complete incident fee pays for the original adjacent-mass lower bound. -/
namespace ACS12.Pressure

open Set MeasureTheory CenteredCircle.AllN
open GammaMeasure (imageDensity imageDensity_pos imagePotential imagePotential_pos imageSlope
  imageSelf imageA imageB imageMoment imageMoment_pos imageMoment_ratio_lower
  imageMoment_samples_summable imageTail_moment_zero_a imageTail_moment_zero_b
  imagePotential_integrable imageDensity_two imageDensity_div_lineDensity_strictMono
  imageSelf_pos incidentGammaWeight incidentGammaWeight_integrable incidentGammaWeight_integral
  incidentGammaWeight_pos gammaWeight_mul_fee_integrable incidentGammaFee_antitone_shape
  incidentGammaFee_one_lt incidentGammaFee_three_halves_lt highIncidentFeeTest
  highIncidentFee_mono_coeff highIncidentFee_antitone highIncidentActualFee highIncidentActualFee_integrable)

private theorem rightExterior_ratio {n : ℕ} {p : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (S : AnchoredCircleSource (Fin n)) (hcap : S.HasCircularMassCaps) :
    ratioFloor (S.mass S.neighbor) * S.rightExterior (imageB p S.period) ≤
      S.rightExterior (imageA p S.period) := by
  let b := S.mass S.neighbor
  let L := S.period
  have hb : 0 < b := S.mass_pos _
  have hL : 0 < L := S.period_pos
  unfold AnchoredCircleSource.rightExterior
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [mul_left_comm]
  apply mul_le_mul_of_nonneg_left _ (S.mass_pos i).le
  let t := S.rightDistance i
  have ht : 0 < t := S.rightDistance_pos i
  change ratioFloor b * imageTail (imageB p L) L t ≤ imageTail (imageA p L) L t
  rw [← imageTail_moment_zero_a hp hL ht,← imageTail_moment_zero_b hp hL ht]
  unfold imageTail
  rw [← tsum_mul_left]
  apply ((imageMoment_samples_summable hp hp₂ hL ht hL .b).mul_left _).tsum_le_tsum
    _ (imageMoment_samples_summable hp hp₂ hL ht hL .a)
  intro j
  let x := t + (j : ℝ) * L
  have hbx : b ≤ x := (S.rightDistance_ge_neighbor hcap i).trans (le_add_of_nonneg_right (by positivity))
  have hx := hb.trans_le hbx
  exact (mul_le_mul_of_nonneg_right (strictMonoOn_ratioFloor.monotoneOn hb hx hbx)
    (imageMoment_pos hp hp₂ hL hx .b 0).le).trans (imageMoment_ratio_lower hp hp₂ hL hx)

private theorem rightExterior_nonneg {n : ℕ} {p : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (S : AnchoredCircleSource (Fin n)) : 0 ≤ S.rightExterior (imageB p S.period) := by
  unfold AnchoredCircleSource.rightExterior
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (S.mass_pos i).le
  rw [← imageTail_moment_zero_b hp S.period_pos (S.rightDistance_pos i)]
  exact tsum_nonneg fun j => (imageMoment_pos hp hp₂ S.period_pos
    (add_pos_of_pos_of_nonneg (S.rightDistance_pos i)
      (mul_nonneg (Nat.cast_nonneg j) S.period_pos.le)) .b 0).le

private theorem incident_actualFee_le_gamma {p L u c : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hu : 0 ≤ u) (hc : 0 ≤ c) (hcu : c ≤ u) :
    highIncidentActualFee p L u c ≤ imagePotential p L 1 *
      ∫ s : ℝ in Ioi 0, incidentGammaWeight p s * highIncidentFeeTest u c s := by
  let W := incidentGammaWeight p
  let V (s : ℝ) := imageDensity p L s * Real.exp (-s)
  let T := highIncidentFeeTest u c
  have hp₀ := zero_lt_one.trans_le hp
  have hV : IntegrableOn V (Ioi 0) := by simpa only [V,mul_one] using imagePotential_integrable hp₀ hL zero_lt_one
  have hR : MonotoneOn (fun s => V s / W s) (Ioi 0) := by
    have hE (s : ℝ) : V s / W s = imageDensity p L s / GammaDeficit.lineDensity p s := by
      unfold V W incidentGammaWeight
      exact mul_div_mul_right _ _ (Real.exp_ne_zero _)
    intro x hx y hy hxy
    change V x / W x ≤ V y / W y
    rw [hE x,hE y]
    rcases hp₂.eq_or_lt with rfl | hp₂'
    · have hρ (s : ℝ) : GammaDeficit.lineDensity 2 s = s := by
        norm_num [GammaDeficit.lineDensity,Real.Gamma_two]
      rw [imageDensity_two hL hx,imageDensity_two hL hy,hρ,hρ,div_self (show 0 < x from hx).ne',
        div_self (show 0 < y from hy).ne']
    · exact (imageDensity_div_lineDensity_strictMono hp hp₂' hL).monotoneOn hx hy hxy
  have h := likelihood_test_anti (incidentGammaWeight_integrable hp₀) hV
    (gammaWeight_mul_fee_integrable hp₀ hu hc) (highIncidentActualFee_integrable hp₀ hL hu hc)
    (fun _ hs => incidentGammaWeight_pos hp₀ hs) hR (highIncidentFee_antitone hc hcu)
  rw [incidentGammaWeight_integral hp₀,mul_one] at h
  simpa only [highIncidentActualFee,V,imagePotential,mul_one,mul_comm] using h

private theorem incident_neighbor_gt_of_fee {n : ℕ} {p u b₀ a : ℝ}
    (hp : 1 ≤ p) (hp₂ : p ≤ 2) (ha : 0 < a) (hap : a ≤ p)
    (hu : 0 ≤ u) (hu₁ : u < 1) (hb₀ : 0 ≤ b₀) (hb₁ : b₀ ≤ 1)
    (hRatio : ∀ b, 0 < b → b ≤ b₀ → u * b ≤ ratioFloor b)
    (hFee : (∫ s : ℝ in Ioi 0, incidentGammaWeight a s * highIncidentFeeTest u (u * b₀) s) <
      (1 - b₀) * (1 + u * b₀))
    (F : Configuration n p) (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi)) :
    b₀ < C.source.mass C.source.neighbor := by
  let S := C.source
  let L := S.period
  let b := S.mass S.neighbor
  let K := imagePotential p L 1
  let D := K + imageSelf p L
  have hp₀ := zero_lt_one.trans_le hp
  have hL := S.period_pos
  have hb := S.mass_pos S.neighbor
  change b₀ < b
  by_contra! hB
  have hR := (mul_le_mul_of_nonneg_right (hRatio b hb hB) (rightExterior_nonneg hp₀ hp₂ S)).trans
    (rightExterior_ratio hp₀ hp₂ S C.circular_caps)
  have hNeed := F.occupiedEdge_fee_required C hp₀ hu hu₁ hR
  change (1 - b) * (1 + u * b) * D < highIncidentActualFee p L u (u * b) at hNeed
  have hC := mul_nonneg hu hb.le
  have hU := mul_nonneg hu hb₀
  have hCU : u * b ≤ u * b₀ := mul_le_mul_of_nonneg_left hB hu
  have hCb : u * b₀ ≤ u := mul_le_of_le_one_right hu hb₁
  have hActual := incident_actualFee_le_gamma hp hp₂ hL hu hC (hCU.trans hCb)
  have hMono := setIntegral_mono_on (gammaWeight_mul_fee_integrable hp₀ hu hC)
    (gammaWeight_mul_fee_integrable hp₀ hu hU) measurableSet_Ioi (fun s hs =>
      mul_le_mul_of_nonneg_left (highIncidentFee_mono_coeff hs hCU) (incidentGammaWeight_pos hp₀ hs).le)
  have hLaw := incidentGammaFee_antitone_shape ha hap hu hU hCb
  have hCost : (1 - b₀) * (1 + u * b₀) ≤ (1 - b) * (1 + u * b) := by
    have h := mul_nonneg (sub_nonneg.mpr hB)
      (show 0 ≤ 1 - u + u * (b₀ + b) from add_nonneg (sub_pos.mpr hu₁).le
        (mul_nonneg hu (add_nonneg hb₀ hb.le)))
    nlinarith only [h]
  have hK := imagePotential_pos hp₀ hL zero_lt_one
  have hD : K ≤ D := le_add_of_nonneg_right (imageSelf_pos hp₀ hL).le
  have hPrice : 0 ≤ (1 - b) * (1 + u * b) :=
    mul_nonneg (sub_nonneg.mpr (hB.trans hb₁)) (by linarith only [hC])
  have hCharge := mul_le_mul hCost hD hK.le hPrice
  exact hNeed.not_ge (hActual.trans ((mul_lt_mul_of_pos_left (hMono.trans_lt (hLaw.trans_lt hFee)) hK).le.trans
    ((mul_comm K _).trans_le hCharge)))

private theorem ratio_of_endpoint {b u B : ℝ} (hb : 0 < b) (hB : b ≤ B) (hu : 0 ≤ u)
    (h0 : 2 * u ≤ 1) (h1 : u * ((B + 1) * (3 * B + 2)) ≤ 3 * B + 1) :
    u * b ≤ ratioFloor b := by
  have hD : 0 < (b + 1) * (3 * b + 2) := by positivity
  have hBn := hb.le.trans hB
  have hPoly : u * ((b + 1) * (3 * b + 2)) ≤ 3 * b + 1 := by
    have h := mul_le_mul_of_nonneg_left h1 hb.le
    have hA := mul_nonneg (sub_nonneg.mpr h0) (sub_nonneg.mpr hB)
    have hC := mul_nonneg (mul_nonneg (mul_nonneg (show 0 ≤ 3 * u by positivity) hb.le) hBn)
      (sub_nonneg.mpr hB)
    by_contra! hBad
    have hBad' := mul_lt_mul_of_pos_left hBad (hb.trans_le hB)
    nlinarith only [h,hA,hC,hBad']
  unfold ratioFloor
  apply (le_div_iff₀ hD).mpr
  have h := mul_le_mul_of_nonneg_left hPoly hb.le
  nlinarith only [h]

theorem incident_neighbor_gt_two_thirds {n : ℕ} {p : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (F : Configuration n p) (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi)) :
    2 / 3 < C.source.mass C.source.neighbor := by
  apply incident_neighbor_gt_of_fee (u := 4 / 9) (a := 1) hp hp₂ zero_lt_one hp
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ _ F C
  · exact fun b hb hB => ratio_of_endpoint hb hB (by norm_num) (by norm_num) (by norm_num)
  · rw [show (4 / 9 : ℝ) * (2 / 3) = 8 / 27 by norm_num,
      show (1 - 2 / 3 : ℝ) * (1 + 8 / 27) = 35 / 81 by norm_num]
    exact incidentGammaFee_one_lt

theorem incident_neighbor_gt_five_sevenths {n : ℕ} {p : ℝ} (hp : 3 / 2 ≤ p) (hp₂ : p ≤ 2)
    (F : Configuration n p) (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi)) :
    5 / 7 < C.source.mass C.source.neighbor := by
  apply incident_neighbor_gt_of_fee (u := 7 / 16) (a := 3 / 2) (by linarith only [hp]) hp₂
    (by norm_num) hp (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ _ F C
  · exact fun b hb hB => ratio_of_endpoint hb hB (by norm_num) (by norm_num) (by norm_num)
  · rw [show (7 / 16 : ℝ) * (5 / 7) = 5 / 16 by norm_num,
      show (1 - 5 / 7 : ℝ) * (1 + 5 / 16) = 3 / 8 by norm_num]
    exact incidentGammaFee_three_halves_lt

end ACS12.Pressure

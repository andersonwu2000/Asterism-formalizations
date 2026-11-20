import ACS12.JointPureUpperStream
import ACS12.JointLawDifference

/-! The exact corrected pure value and its complete upper diagonal bound. -/
namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaDeficit (lineDensity lineDensity_exp_integrable lineDensity_exp_integral)

noncomputable def jointPureValue (p L u m r mu : ℝ) : ℝ :=
  adjacentLawSignedValue p L 0 u m + jointPureLambda * adjacentSourceLaw p L 0 u m m r +
    mu * fourthSourceRow p L 0 u m r m

private theorem jointPure_upperDiag_eq {p L u mu : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hu : 0 < u) (hu₁ : u ≤ 1) (hmu : 0 ≤ mu) (hmuU : mu ≤ 9 / 500) :
    jointPureValue p L u u u mu = -(1 - u) * (1 + middleA u * p) +
      (jointPureRStream p mu u u - jointPureRStream p mu u 1) := by
  let ρ := lineDensity p
  let f (s : ℝ) := ρ s * outerNativeDensity u u s
  let q (s : ℝ) := ρ s * polyB (u * s) * (scaledExpTail s u - scaledExpTail s 1)
  let h (s : ℝ) := ρ s * fourthDensity u u u u s
  let A (s : ℝ) := ρ s * Real.exp (-s)
  let B (s : ℝ) := ρ s * s * Real.exp (-s)
  let K (s : ℝ) := A s + middleA u * B s
  let R (t s : ℝ) := ρ s * jointPureR mu u s * scaledExpTail s t
  have h0 : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  obtain ⟨hf,hfE⟩ := outerLawSignedValue_integral (m := u) hp hp₂ hL h0 hu
  simp only [lawDensity, sub_zero, one_mul, zero_mul, add_zero, lawSelf, mul_zero] at hf hfE
  change IntegrableOn f (Ioi 0) at hf
  obtain ⟨hq,hqE⟩ := pureOuterDeficit_integral hp hp₂ hL hu
  change IntegrableOn q (Ioi 0) at hq
  obtain ⟨hh,hhE⟩ := fourthSourceRow_integral (m := u) hp hp₂ hL h0 hu hu hu
  simp only [lawDensity, sub_zero, one_mul, zero_mul, add_zero, lawSelf, mul_zero] at hh hhE
  change IntegrableOn h (Ioi 0) at hh
  have hp₀ := zero_lt_one.trans_le hp
  have hA : IntegrableOn A (Ioi 0) := by
    simpa only [A,ρ,mul_one] using lineDensity_exp_integrable hp₀ zero_lt_one
  have hB : IntegrableOn B (Ioi 0) := by
    simpa only [B,ρ,lawDensity,sub_zero,one_mul,zero_mul,add_zero,pow_one,mul_one] using
      lawMoment_integrable hp hp₂ hL h0 zero_lt_one 1
  have hK : IntegrableOn K (Ioi 0) := hA.add (hB.const_mul (middleA u))
  have hKE : (∫ s : ℝ in Ioi 0, K s) = 1 + middleA u * p := by
    rw [integral_add hA (hB.const_mul _), integral_const_mul]
    have hAE : (∫ s : ℝ in Ioi 0, A s) = 1 := by
      simpa only [A,ρ,mul_one,Real.one_rpow] using lineDensity_exp_integral hp₀ zero_lt_one
    have hBE : (∫ s : ℝ in Ioi 0, B s) = lawMoment p L 0 1 1 := by
      simp only [B,ρ,lawMoment,lawDensity,sub_zero,one_mul,zero_mul,add_zero,pow_one,mul_one]
    rw [hAE,hBE,lawMoment_zero_slope hp₀ zero_lt_one,Real.one_rpow,mul_one]
  obtain ⟨B₀, _, hB₀⟩ := pureLinear_envelope hp hp₂ (by norm_num : (0 : ℝ) ≤ 2)
    (jointPureR_linear hmu hmuU hu hu₁)
  have hM : Measurable (fun s => ρ s * jointPureR mu u s) :=
    (by unfold ρ lineDensity; fun_prop : Measurable ρ).mul (jointPureR_measurable mu u)
  have hR (t : ℝ) (ht : 0 < t) : IntegrableOn (R t) (Ioi 0) := boseStream_integrable hM hB₀ ht
  have hPoint (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      f s - jointPureLambda * q s + mu * h s = -(1 - u) * K s + (R u s - R 1 s) := by
    have hs₀ : 0 < s := hs
    have hn := outerNativeResponse_eq (m := u) hu hs₀
    simp only [outerNativeResponse,sub_self,mul_zero,zero_sub,mul_neg,sub_neg_eq_add,middleA0] at hn
    have hBose : adjacentBoseGap u u s = 0 := by unfold adjacentBoseGap; ring_nf
    have hH := fourthSourceResponse_eq (r := u) hu hu hs₀
    rw [hBose,mul_zero,add_zero,sub_self,zero_add,fourthSourceResponse,sub_self,zero_sub] at hH
    dsimp only [f,q,h,K,A,B,R,ρ,jointPureR]
    linear_combination -(lineDensity p s) * hn - mu * lineDensity p s * hH
  have hFQ : IntegrableOn (fun s => f s - jointPureLambda * q s) (Ioi 0) :=
    hf.sub (hq.const_mul jointPureLambda)
  have hInt := setIntegral_congr_fun (μ := volume) measurableSet_Ioi hPoint
  have hDiff : IntegrableOn (fun s => R u s - R 1 s) (Ioi 0) := (hR u hu).sub (hR 1 zero_lt_one)
  rw [integral_add hFQ (hh.const_mul mu), integral_sub hf (hq.const_mul jointPureLambda),
    integral_const_mul, integral_const_mul, integral_add (hK.const_mul _) hDiff,
    integral_sub (hR u hu) (hR 1 zero_lt_one), integral_const_mul, hKE] at hInt
  have hOuter : adjacentSourceLaw p L 0 u u u u = -outerLawDeficit p L 0 u := by
    rw [outerSourceLaw_eq hp hp₂ hL h0 hu, outerLawMass, sub_mul, sub_mul,
      div_mul_cancel₀ _ (outerLawDenom_pos hp hp₂ hL h0 hu).ne']
    ring
  rw [jointPureValue, hOuter]
  have hDiag : adjacentLawSignedValue p L 0 u u = outerLawSignedValue p L 0 u u := by
    unfold adjacentLawSignedValue outerLawSignedValue
    ring
  rw [hDiag]
  rw [hfE, hqE, hhE]
  change _ = -(1 - u) * (1 + middleA u * p) +
    ((∫ s : ℝ in Ioi 0, R u s) - ∫ s : ℝ in Ioi 0, R 1 s)
  dsimp only [f,q,h,ρ] at hInt
  linear_combination hInt

theorem jointPure_unit_zero {p L mu : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hL : 0 < L)
    (hmu : 0 ≤ mu) (hmuU : mu ≤ 9 / 500) :
    jointPureValue p L 1 1 1 mu = 0 := by
  rw [jointPure_upperDiag_eq hp hp₂ hL zero_lt_one le_rfl hmu hmuU]
  simp

theorem jointPure_upperDiag_bound {p L u mu : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hL : 0 < L) (huL : 7 / 8 ≤ u) (hu₁ : u < 1) (hmu : 0 ≤ mu) (hmuU : mu ≤ 9 / 500) :
    jointPureValue p L u u u mu ≤ (1 - u) * jointUnitValue p mu - (43 / 10000) * (1 - u) ^ 2 := by
  let δ := 1 - u
  have hδ : 0 < δ := sub_pos.mpr hu₁
  have hδU : δ ≤ 1 / 8 := by dsimp only [δ]; linarith only [huL]
  have ha : middleA u = (6 / 25) * (1 - δ ^ 2) := by unfold middleA; dsimp only [δ]; ring
  have hu := (by norm_num : (0 : ℝ) < 7 / 8).trans_le huL
  have h := jointPureRStream_gap_le hp hP hmu hmuU huL hu₁
  rw [jointPure_upperDiag_eq hp (hP.trans (by norm_num)) hL hu hu₁.le hmu hmuU,ha]
  have hpδ := mul_le_mul hP hδU hδ.le (by norm_num : (0 : ℝ) ≤ 9 / 5)
  have hCost := mul_le_mul_of_nonneg_right hpδ (sq_nonneg δ)
  change jointPureRStream p mu u u - jointPureRStream p mu u 1 ≤
    δ * (1 + (6 / 25) * p + jointUnitValue p mu) - (583 / 10000) * δ ^ 2 at h
  change _ ≤ δ * jointUnitValue p mu - (43 / 10000) * δ ^ 2
  nlinarith only [h,hCost]

end ACS12.GammaMeasure

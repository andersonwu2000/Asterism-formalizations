import ACS12.JointFarNativePrice
import ACS12.JointFarAdjacentPrice
import ACS12.JointFarFourthPrice
import ACS12.JointFarValue

/-! The exponent chord for the zero-gap far envelope. -/
namespace ACS12.GammaMeasure

open Set

private noncomputable def farBase (p : ℝ) : ℝ :=
  jointFarNative p + jointPureLambda * jointFarAdjacent p + jointCanonicalMu * jointFarFourth p

private noncomputable def farBaseCorrected (p : ℝ) : ℝ := farBase p + (57 / 1000) * p ^ 2

private noncomputable def farBaseCorrectedPrime (p : ℝ) : ℝ :=
  farNativeJet 1 p + jointPureLambda * farAdjacentJet 1 p + jointCanonicalMu * farFourthJet 1 p +
    (114 / 1000) * p

private theorem farBaseCorrected_deriv {p : ℝ} (hp : 0 < p) :
    HasDerivAt farBaseCorrected (farBaseCorrectedPrime p) p := by
  have hN := farNativeJet_deriv (k := 0) (by decide) hp
  have hQ := farAdjacentJet_deriv (k := 0) (by decide) hp
  have hH := farFourthJet_deriv (k := 0) (by decide) hp
  have h := (((hN.add (hQ.const_mul jointPureLambda)).add (hH.const_mul jointCanonicalMu)).add
    (((hasDerivAt_id p).pow 2).const_mul (57 / 1000)))
  have h' : HasDerivAt (fun q => farNativeJet 0 q + jointPureLambda * farAdjacentJet 0 q +
      jointCanonicalMu * farFourthJet 0 q + (57 / 1000) * q ^ 2) (farBaseCorrectedPrime p) p := by
    convert h using 1
    norm_num [farBaseCorrectedPrime,id_eq]
    ring
  apply h'.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds hp] with q hq
  simp only [farBaseCorrected,farBase,Pi.add_apply,id_eq,farNativeJet_zero,farAdjacentJet_zero hq,farFourthJet_zero]

private theorem farBaseCorrectedPrime_deriv {p : ℝ} (hp : 0 < p) :
    HasDerivAt farBaseCorrectedPrime (farNativeJet 2 p + jointPureLambda * farAdjacentJet 2 p +
      jointCanonicalMu * farFourthJet 2 p + 114 / 1000) p := by
  have hN := farNativeJet_deriv (k := 1) (by decide) hp
  have hQ := farAdjacentJet_deriv (k := 1) (by decide) hp
  have hH := farFourthJet_deriv (k := 1) (by decide) hp
  simpa only [farBaseCorrectedPrime,mul_one] using
    (((hN.add (hQ.const_mul jointPureLambda)).add (hH.const_mul jointCanonicalMu)).add
      ((hasDerivAt_id p).const_mul (114 / 1000)))

private theorem farBaseCorrected_convex : ConvexOn ℝ (Icc 1 (9 / 5)) farBaseCorrected := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (D := Icc (1 : ℝ) (9 / 5)) (f' := farBaseCorrectedPrime)
    (convex_Icc _ _)
    (fun p hp => (farBaseCorrected_deriv (zero_lt_one.trans_le hp.1)).continuousAt.continuousWithinAt)
    (fun p hp => (farBaseCorrected_deriv (zero_lt_one.trans_le (show p ∈ Icc (1 : ℝ) (9 / 5) from interior_subset hp).1)).hasDerivWithinAt)
    (fun p hp => (farBaseCorrectedPrime_deriv (zero_lt_one.trans_le (show p ∈ Icc (1 : ℝ) (9 / 5) from interior_subset hp).1)).hasDerivWithinAt)
  intro p hp
  have hI : p ∈ Icc (1 : ℝ) (9 / 5) := interior_subset hp
  have hN := farNative_second_gt hI.1 hI.2
  have hQ := mul_le_mul_of_nonneg_left (farAdjacent_second_gt hI.1 hI.2).le (by norm_num [jointPureLambda] : 0 ≤ jointPureLambda)
  have hμ₀ : 0 ≤ jointCanonicalMu := by linarith only [jointCanonicalMu_bounds.1]
  have hH := (mul_le_mul_of_nonneg_left (farFourth_second_gt hI.1 hI.2).le hμ₀)
  have hH' := mul_le_mul_of_nonpos_right jointCanonicalMu_bounds.2.le (by norm_num : -(52 / 100 : ℝ) ≤ 0)
  norm_num [jointPureLambda] at hQ ⊢
  linarith only [hN,hQ,hH,hH']

private theorem farMismatch_price_le {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    (1 / 10) * (3 / 4 : ℝ) ^ (-p) * max 0 (jointPureMismatch p) ≤
      (93 / 10000) * (1 - (5 / 4) * (p - 1)) := by
  have hS : (3 / 4 : ℝ) ^ (-p) ≤ 1679 / 1000 := by
    have hE : (3 / 4 : ℝ) ^ (-p) = (3 / 4 : ℝ) ^ (1 - p) * (4 / 3) := by
      rw [show (4 / 3 : ℝ) = (3 / 4 : ℝ) ^ (-(1 : ℝ)) by norm_num [Real.rpow_neg_one],
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 3 / 4),show 1 - p + -1 = -p by ring]
    rw [hE]
    linarith only [jointLowerMassScale_le hP]
  have hC := jointPureMismatch_posPart_le hp hP
  have hR := mul_le_mul hS hC (le_max_left _ _) (by norm_num : (0 : ℝ) ≤ 1679 / 1000)
  have hT := mul_nonneg (show 0 ≤ 9 / 5 - p by linarith only [hP]) (by norm_num : (0 : ℝ) ≤
    (93 / 10000) * (5 / 4) - (1 / 10) * (1679 / 1000) * (69 / 1000))
  nlinarith only [hR,hT]

theorem jointFarValue_linear_margin {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    jointFarValue p < -(52 / 100000 : ℝ) - (9 / 1000) * (9 / 5 - p) := by
  let P : ℝ := 9 / 5
  let θ : ℝ := (5 / 4) * (p - 1)
  have hθ₀ : 0 ≤ θ := by unfold θ; linarith only [hp]
  have hθU : θ ≤ 1 := by unfold θ; linarith only [hP]
  have hθ₁ : 0 ≤ 1 - θ := sub_nonneg.mpr hθU
  have h₁ : (1 : ℝ) ∈ Icc 1 (9 / 5) := by norm_num
  have hP' : P ∈ Icc 1 (9 / 5) := by norm_num [P]
  have hArg : (1 - θ) • (1 : ℝ) + θ • P = p := by simp only [smul_eq_mul,θ,P]; ring
  have hB := farBaseCorrected_convex.2 h₁ hP' hθ₁ hθ₀ (sub_add_cancel 1 θ)
  have hClip := jointClipPrice_convex.2 h₁ hP' hθ₁ hθ₀ (sub_add_cancel 1 θ)
  rw [hArg] at hB hClip
  simp only [farBaseCorrected,smul_eq_mul] at hB hClip
  have hSq : (1 - θ) * (57 / 1000 : ℝ) * 1 ^ 2 + θ * (57 / 1000) * P ^ 2 -
      (57 / 1000) * p ^ 2 = (3648 / 100000) * θ * (1 - θ) := by unfold θ P; ring
  have hM := farMismatch_price_le hp hP
  change _ ≤ (93 / 10000) * (1 - θ) at hM
  have hMC₀ : 0 ≤ (1 / 10) * (3 / 4 : ℝ) ^ (-(1 : ℝ)) * max 0 (jointPureMismatch 1) :=
    mul_nonneg (by positivity) (le_max_left _ _)
  have hAdd := mul_nonneg hθ₁ hMC₀
  have hCost := mul_le_mul_of_nonneg_right hθU (show 0 ≤ (3648 / 100000) * (1 - θ) by positivity)
  have hE₁ : jointFarValue 1 = farBase 1 + jointClipPrice 1 / 8 +
      (1 / 10) * (3 / 4 : ℝ) ^ (-(1 : ℝ)) * max 0 (jointPureMismatch 1) := rfl
  have hEP : jointFarValue P = farBase P + jointClipPrice P / 8 := by
    unfold jointFarValue
    rw [show jointPureMismatch P = 0 from jointPureMismatch_endpoint,max_self,mul_zero,add_zero]
    rfl
  have hTotal : jointFarValue p ≤
      (1 - θ) * jointFarValue 1 + θ * jointFarValue P + (4578 / 100000) * (1 - θ) := by
    rw [hE₁,hEP]
    change farBase p + _ + _ ≤ _
    nlinarith only [hB,hClip,hSq,hM,hAdd,hCost]
  have h₁' := mul_le_mul_of_nonneg_left jointFarValue_one_lt.le hθ₁
  have hP'' := mul_le_mul_of_nonneg_left jointFarValue_endpoint_lt.le hθ₀
  change θ * jointFarValue P ≤ _ at hP''
  by_cases hEnd : θ = 1
  · have hpEnd : p = 9 / 5 := by dsimp only [θ] at hEnd; linarith only [hEnd]
    rw [hpEnd]
    simpa only [sub_self,mul_zero,sub_zero] using jointFarValue_endpoint_lt
  · have hθStrict : θ < 1 := lt_of_le_of_ne hθU hEnd
    dsimp only [θ] at hTotal h₁' hP'' hθStrict
    linarith only [hTotal,h₁',hP'',hθStrict]

theorem jointFarValue_margin {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    jointFarValue p < -(52 / 100000 : ℝ) :=
  (jointFarValue_linear_margin hp hP).trans_le (sub_le_self _ (mul_nonneg (by norm_num) (sub_nonneg.mpr hP)))

theorem jointFarValue_neg {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) : jointFarValue p < 0 :=
  (jointFarValue_margin hp hP).trans (by norm_num)

end ACS12.GammaMeasure

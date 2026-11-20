import ACS12.JointLogZBand
import ACS12.JointLogQLower
import ACS12.JointClipConvex

/-! The unit value and the complete one-clip convex chord G27–28. -/
namespace ACS12.GammaMeasure

open Set

noncomputable def jointUnitNativeM (p : ℝ) : ℝ :=
  (31 / 25) * pureQ p - pureP p - p - 1 - (6 / 25) * p * (p + 2)

noncomputable def jointUnitK (p : ℝ) : ℝ :=
  -jointUnitNativeM p + jointPureLambda * jointPureD p - jointCanonicalMu * (1 + pureP p)

noncomputable def jointPureUnit (k c p : ℝ) : ℝ :=
  jointUnitValue p jointCanonicalMu + k * jointUnitK p + c * jointPureMismatch p

private noncomputable def expTwoNeg (p : ℝ) : ℝ := (2 : ℝ) ^ (-p)

private theorem expTwoNeg_derivative (p : ℝ) :
    HasDerivAt expTwoNeg (-Real.log 2 * expTwoNeg p) p := by
  convert (hasDerivAt_id p).neg.const_rpow (by norm_num : (0 : ℝ) < 2) using 1
  simp only [expTwoNeg,id_eq,Pi.neg_apply]
  ring

private theorem expTwoNegPrime_derivative (p : ℝ) :
    HasDerivAt (fun q => -Real.log 2 * expTwoNeg q) (Real.log 2 ^ 2 * expTwoNeg p) p := by
  convert (expTwoNeg_derivative p).const_mul (-Real.log 2) using 1
  ring

private theorem expTwoNeg_second_le {p : ℝ} (hp : 1 ≤ p) :
    Real.log 2 ^ 2 * expTwoNeg p ≤ 241 / 1000 := by
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hL : Real.log 2 ≤ 694 / 1000 := by linarith only [Real.log_two_lt_d9]
  have hE : expTwoNeg p ≤ (1 / 2 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (neg_le_neg hp)
    simpa only [expTwoNeg,Real.rpow_neg_one,one_div] using h
  have hQ := mul_le_mul (pow_le_pow_left₀ hl hL 2) hE
    (Real.rpow_nonneg (by norm_num) _) (by positivity : 0 ≤ (694 / 1000 : ℝ) ^ 2)
  exact hQ.trans (by norm_num)

private theorem unit_second_pos {k c p : ℝ} (hk : 0 ≤ k) (hk₁ : k ≤ 1)
    (hc : 0 ≤ c) (hc₁ : c ≤ 4 / 5) (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    0 < (1 - jointPureLambda - jointCanonicalMu) * purePSecond p +
      (jointCanonicalMu - 6 / 25) * pureQSecond p -
      jointCanonicalMu * (Real.log 2 ^ 2 * expTwoNeg p) +
      k * ((1 - jointPureLambda - jointCanonicalMu) * purePSecond p +
        (jointPureLambda - 31 / 25) * pureQSecond p + 12 / 25) +
      c * ((2 * jointPureLambda + jointCanonicalMu) * pureQSecond p -
        (jointPureLambda + jointCanonicalMu) * purePSecond p - 2 * jointPureLambda) := by
  obtain ⟨hmL,hmU⟩ := jointCanonicalMu_bounds
  have hm₀ : 0 ≤ jointCanonicalMu := by linarith only [hmL]
  have hK : 0 ≤ 1 - jointPureLambda - jointCanonicalMu := by unfold jointPureLambda; linarith only [hmU]
  have hJ : 0 ≤ jointPureLambda + jointCanonicalMu := by unfold jointPureLambda; positivity
  have hI : 0 ≤ 2 * jointPureLambda + jointCanonicalMu := by unfold jointPureLambda; positivity
  obtain ⟨hPL,hPU⟩ := purePSecond_bounds hp hP
  have hQL := pureQSecond_gt hp hP
  have hQU := pureQSecond_lt hp hP
  have hP₁ := mul_le_mul_of_nonneg_left hPL.le hK
  have hP₂ := mul_le_mul_of_nonneg_left hPU.le hJ
  have hQ₁ := mul_le_mul_of_nonpos_left hQU.le (show jointCanonicalMu - 6 / 25 ≤ 0 by linarith only [hmU])
  have hQ₂ := mul_le_mul_of_nonpos_left hQU.le (show jointPureLambda - (31 / 25) ≤ 0 by norm_num [jointPureLambda])
  have hQ₃ := mul_le_mul_of_nonneg_left hQL.le hI
  have hE := mul_le_mul_of_nonneg_left (expTwoNeg_second_le hp) hm₀
  have hBase : 710 / 1000 < (1 - jointPureLambda - jointCanonicalMu) * purePSecond p +
      (jointCanonicalMu - 6 / 25) * pureQSecond p -
      jointCanonicalMu * (Real.log 2 ^ 2 * expTwoNeg p) := by
    unfold jointPureLambda at hP₁ hQ₁ ⊢
    linarith only [hP₁,hQ₁,hE,hmL,hmU]
  have hK' : -(357 / 1000) < (1 - jointPureLambda - jointCanonicalMu) * purePSecond p +
        (jointPureLambda - 31 / 25) * pureQSecond p + 12 / 25 := by
    unfold jointPureLambda at hP₁ hQ₂ ⊢
    linarith only [hP₁,hQ₂,hmU]
  have hJ' : -(95 / 1000) < (2 * jointPureLambda + jointCanonicalMu) * pureQSecond p -
        (jointPureLambda + jointCanonicalMu) * purePSecond p - 2 * jointPureLambda := by
    unfold jointPureLambda at hP₂ hQ₃ ⊢
    linarith only [hP₂,hQ₃,hmL,hmU]
  have hA := mul_le_mul_of_nonneg_left hK'.le hk
  have hB := mul_le_mul_of_nonneg_left hJ'.le hc
  linarith only [hBase,hA,hB,hk₁,hc₁]

theorem jointPureUnit_convex {k c : ℝ} (hk : 0 ≤ k) (hk₁ : k ≤ 1) (hc : 0 ≤ c) (hc₁ : c ≤ 4 / 5) :
    ConvexOn ℝ (Icc 1 (9 / 5)) (jointPureUnit k c) := by
  let l := jointPureLambda
  let μ := jointCanonicalMu
  let A := (1 + k) * (1 - l - μ) - c * (l + μ)
  let B := μ - 6 / 25 + k * (l - 31 / 25) + c * (2 * l + μ)
  let C := 6 / 25 * k - l * c
  let D := (37 / 25) * k - 2 * μ - 3 * l * c
  let E := k * (1 - μ) - (1 + c) * l
  let F (p : ℝ) := A * pureP p + B * pureQ p - μ * expTwoNeg p + C * p ^ 2 + D * p + E
  let F₁ (p : ℝ) := A * purePPrime p + B * pureQPrime p - μ * (-Real.log 2 * expTwoNeg p) + 2 * C * p + D
  let F₂ (p : ℝ) := A * purePSecond p + B * pureQSecond p - μ * (Real.log 2 ^ 2 * expTwoNeg p) + 2 * C
  have hE : jointPureUnit k c = F := by
    funext p
    dsimp only [jointPureUnit,F,A,B,C,D,E,l,μ,jointUnitValue,jointUnitK,jointUnitNativeM,jointPureD,
      jointPureMismatch,jointPureB,expTwoNeg]
    ring
  have h₁ (p : ℝ) (hp : 0 < p) : HasDerivAt F (F₁ p) p := by
    have h := hasDerivAt_id p
    have hP := (pureP_derivative hp).const_mul A
    have hQ := (pureQ_derivative (by linarith only [hp])).const_mul B
    have hX := (expTwoNeg_derivative p).const_mul μ
    convert (((((hP.add hQ).sub hX).add ((h.pow 2).const_mul C)).add (h.const_mul D)).add_const E) using 1
    norm_num [F₁,id_eq]
    ring
  have h₂ (p : ℝ) (hp : 0 < p) : HasDerivAt F₁ (F₂ p) p := by
    have hP := (purePPrime_derivative hp).const_mul A
    have hQ := (pureQPrime_derivative (by linarith only [hp])).const_mul B
    have hX := (expTwoNegPrime_derivative p).const_mul μ
    convert ((((hP.add hQ).sub hX).add ((hasDerivAt_id p).const_mul (2 * C))).add_const D) using 1
    simp [F₂]
  rw [hE]
  have hPos (p : ℝ) (hp : p ∈ Icc (1 : ℝ) (9 / 5)) : 0 < p := zero_lt_one.trans_le hp.1
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
    (fun p hp => (h₁ p (hPos p hp)).continuousAt.continuousWithinAt)
    (fun p hp => (h₁ p (hPos p (interior_subset hp))).hasDerivWithinAt)
    (fun p hp => (h₂ p (hPos p (interior_subset hp))).hasDerivWithinAt)
  intro p hp
  have hp' : p ∈ Icc (1 : ℝ) (9 / 5) := interior_subset hp
  have h := unit_second_pos hk hk₁ hc hc₁ hp'.1 hp'.2
  dsimp only [F₂,A,B,C,l,μ]
  linarith only [h]


theorem pureQPrime_bounds {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    (16 / 5 : ℝ) + (8 / 5) * (p - 1) < pureQPrime p ∧
    pureQPrime p < 3211 / 1000 + (231 / 125) * (p - 1) := by
  let f (a b t : ℝ) := a * pureQPrime t + b * (t - 1)
  have hD (a b t : ℝ) (ht : t ∈ Icc (1 : ℝ) (9 / 5)) :
      HasDerivAt (f a b) (a * pureQSecond t + b) t := by
    simpa only [f,mul_one] using ((pureQPrime_derivative (by linarith only [ht.1])).const_mul a).add
      (((hasDerivAt_id t).sub_const 1).const_mul b)
  have hM (a b : ℝ) (h : ∀ x ∈ Icc (1 : ℝ) (9 / 5), 0 ≤ a * pureQSecond x + b) :
      MonotoneOn (f a b) (Icc 1 (9 / 5)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun t ht => (hD a b t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hD a b t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' := interior_subset ht
      rw [(hD a b t ht').deriv]
      exact h t ht'
  have h₁ : (1 : ℝ) ∈ Icc 1 (9 / 5) := ⟨le_rfl,by norm_num⟩
  have hL := hM 1 (-(8 / 5)) (fun x hx => by linarith only [pureQSecond_gt hx.1 hx.2])
    h₁ ⟨hp,hP⟩ hp
  have hU := hM (-1) (231 / 125) (fun x hx => by linarith only [pureQSecond_lt hx.1 hx.2])
    h₁ ⟨hp,hP⟩ hp
  dsimp only [f] at hL hU
  exact ⟨by linarith only [hL,pureQPrime_one_bounds.1],by linarith only [hU,pureQPrime_one_bounds.2]⟩

private theorem mismatchDerivative_gt {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    -(69 / 1000) < jointCanonicalMu * (pureQPrime p - purePPrime p) -
      jointPureLambda * (2 * p + 3 + purePPrime p - 2 * pureQPrime p) := by
  obtain ⟨hP₁,hP₂⟩ := purePPrime_bounds hp hP
  obtain ⟨hQ₁,hQ₂⟩ := pureQPrime_bounds hp hP
  let t := p - 1
  have ht : 0 ≤ t := sub_nonneg.mpr hp
  have ht' : t ≤ 4 / 5 := by dsimp only [t]; linarith only [hP]
  have hSq := pow_le_pow_left₀ ht ht' 2
  have hS := mul_le_mul_of_nonneg_left ht' ht
  have hD : 1555 / 1000 < pureQPrime p - purePPrime p := by
    dsimp only [t] at hS
    nlinarith only [hS,ht,hQ₁,hP₂]
  have hB : 2 * p + 3 + purePPrime p - 2 * pureQPrime p ≤ 54 / 100 := by
    dsimp only [t] at hSq ht'
    nlinarith only [hSq,ht',hP₂,hQ₁]
  obtain ⟨hmL,hmU⟩ := jointCanonicalMu_bounds
  have hM := mul_le_mul hmL.le hD.le (by norm_num : (0 : ℝ) ≤ 1555 / 1000) (by linarith only [hmL])
  have hT := mul_le_mul_of_nonneg_left hB (by norm_num [jointPureLambda] : 0 ≤ jointPureLambda)
  unfold jointPureLambda at hT ⊢
  linarith only [hM,hT]

theorem jointPureMismatch_posPart_le {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    max 0 (jointPureMismatch p) ≤ (69 / 1000) * (9 / 5 - p) := by
  let f (p : ℝ) := jointPureMismatch p + (69 / 1000) * p
  let d (p : ℝ) := jointCanonicalMu * (pureQPrime p - purePPrime p) -
    jointPureLambda * (2 * p + 3 + purePPrime p - 2 * pureQPrime p) + 69 / 1000
  have hD (p : ℝ) (hp : p ∈ Icc (1 : ℝ) (9 / 5)) : HasDerivAt f (d p) p := by
    have h₁ := pureP_derivative (zero_lt_one.trans_le hp.1)
    have h₂ := pureQ_derivative (by linarith only [hp.1])
    have h := hasDerivAt_id p
    have hB := (((((h.pow 2).add (h.const_mul 3)).add_const 1).add h₁).sub (h₂.const_mul 2)).const_mul jointPureLambda
    have hA := (h₂.sub h₁).const_mul jointCanonicalMu
    convert ((hA.sub hB).add (h.const_mul (69 / 1000))) using 1
    norm_num [d,id_eq]
  have hM : MonotoneOn f (Icc 1 (9 / 5)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun p hp => (hD p hp).continuousAt.continuousWithinAt
    · exact fun p hp => (hD p (interior_subset hp)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Icc (1 : ℝ) (9 / 5) := interior_subset hx
      rw [(hD x hx').deriv]
      have h := mismatchDerivative_gt hx'.1 hx'.2
      dsimp only [d]
      linarith only [h]
  have h := hM ⟨hp,hP⟩ (show (9 / 5 : ℝ) ∈ Icc 1 (9 / 5) by constructor <;> norm_num) hP
  dsimp only [f] at h
  rw [jointPureMismatch_endpoint] at h
  exact max_le (mul_nonneg (by norm_num) (sub_nonneg.mpr hP)) (by linarith only [h])

private theorem jointPureUnit_one_lt {k c : ℝ} (hk : 0 ≤ k) (hk₁ : k ≤ 1) (hc : 0 ≤ c) (hc₁ : c ≤ 4 / 5) :
    jointPureUnit k c 1 + jointClipPrice 1 < -(4423 / 10000) := by
  have hP : pureP 1 = 0 := by norm_num [pureP]
  have hQ : (2404 / 1000 : ℝ) < pureQ 1 ∧ pureQ 1 < 24042 / 10000 := by
    obtain ⟨hL,hU⟩ := powerTail_three_bounds
    norm_num [pureQ]
    exact ⟨by linarith only [hL],by linarith only [hU]⟩
  obtain ⟨hmL,hmU⟩ := jointCanonicalMu_bounds
  have hX : 958 / 10000 < (2 : ℝ) + 0 - pureQ 1 + 1 / 2 := by linarith only [hQ.2]
  have hμX := mul_le_mul hmL.le hX.le (by norm_num : (0 : ℝ) ≤ 958 / 10000) (by linarith only [hmL])
  have hBase : jointUnitValue 1 jointCanonicalMu < -(75496 / 100000) := by
    unfold jointUnitValue jointPureLambda
    rw [hP,Real.rpow_neg_one]
    norm_num at ⊢
    linarith only [hQ.1,hμX]
  have hK : jointUnitK 1 < 149226 / 1000000 := by
    unfold jointUnitK jointUnitNativeM jointPureD jointPureLambda
    rw [hP]
    norm_num
    linarith only [hQ.1,hmL]
  have hCQ := mul_le_mul hmU.le hQ.2.le (by linarith only [hQ.1]) (by norm_num : (0 : ℝ) ≤ 17765 / 1000000)
  have hC : jointPureMismatch 1 < 8606 / 1000000 := by
    unfold jointPureMismatch jointPureD jointPureB jointPureLambda
    rw [hP]
    norm_num
    linarith only [hQ.2,hCQ]
  have hK' := mul_le_mul hK.le hk₁ hk (by norm_num : (0 : ℝ) ≤ 149226 / 1000000)
  have hC' := mul_le_mul hC.le hc₁ hc (by norm_num : (0 : ℝ) ≤ 8606 / 1000000)
  rw [jointPureUnit,jointClipPrice_one]
  linarith only [hBase,hK',hC']

private theorem jointPureUnit_endpoint_lt {k c : ℝ} (hk : 0 ≤ k) :
    jointPureUnit k c (9 / 5) + jointClipPrice (9 / 5) < -(39 / 4000) := by
  obtain ⟨hP,hP',hQ,hQ'⟩ := jointPure_endpoint_moments
  obtain ⟨hmL,hmU⟩ := jointCanonicalMu_bounds
  have hX : (2871745 / 10000000 : ℝ) < (2 : ℝ) ^ (-(9 / 5 : ℝ)) := by
    apply (Real.rpow_lt_rpow_iff (by norm_num) (Real.rpow_nonneg (by norm_num) _)
      (z := (5 : ℝ)) (by norm_num)).mp
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hI : 15144 / 100000 < 2 * (9 / 5 : ℝ) + pureP (9 / 5) - pureQ (9 / 5) + (2 : ℝ) ^ (-(9 / 5 : ℝ)) := by
    linarith only [hP,hQ',hX]
  have hμI := mul_le_mul hmL.le hI.le (by norm_num : (0 : ℝ) ≤ 15144 / 100000) (by linarith only [hmL])
  have hBase : jointUnitValue (9 / 5) jointCanonicalMu < -(643 / 20000) := by
    unfold jointUnitValue jointPureLambda
    linarith only [hP',hQ,hμI]
  have hμP := mul_le_mul hmL.le
    (show (279572464 / 100000000 : ℝ) ≤ 1 + pureP (9 / 5) by linarith only [hP])
    (by norm_num : (0 : ℝ) ≤ 279572464 / 100000000) (by linarith only [hmL])
  have hK : jointUnitK (9 / 5) < 0 := by
    unfold jointUnitK jointUnitNativeM jointPureD jointPureLambda
    linarith only [hP',hQ,hμP]
  have hK' := mul_nonpos_of_nonneg_of_nonpos hk hK.le
  rw [jointPureUnit,jointPureMismatch_endpoint,mul_zero,add_zero]
  linarith only [hBase,hK',jointClipPrice_endpoint_lt]

theorem jointPureUnit_clip_lt {k c p : ℝ} (hk : 0 ≤ k) (hk₁ : k ≤ 1)
    (hc : 0 ≤ c) (hc₁ : c ≤ 4 / 5) (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    jointPureUnit k c p + jointClipPrice p < -(97 / 10000) - (54 / 100) * (9 / 5 - p) := by
  let t := (5 / 4) * (p - 1)
  have ht : 0 ≤ t := by dsimp only [t]; linarith only [hp]
  have ht' : t ≤ 1 := by dsimp only [t]; linarith only [hP]
  have hC := (jointPureUnit_convex hk hk₁ hc hc₁).add jointClipPrice_convex
  have h₁ : (1 : ℝ) ∈ Icc 1 (9 / 5) := ⟨le_rfl,by norm_num⟩
  have h₂ : (9 / 5 : ℝ) ∈ Icc 1 (9 / 5) := ⟨by norm_num,le_rfl⟩
  have h := hC.2 h₁ h₂ (sub_nonneg.mpr ht') ht (sub_add_cancel 1 t)
  have hArg : (1 - t) • (1 : ℝ) + t • (9 / 5 : ℝ) = p := by
    simp only [smul_eq_mul,t]
    ring
  rw [hArg] at h
  simp only [smul_eq_mul,Pi.add_apply] at h
  have hL := mul_le_mul_of_nonneg_left (jointPureUnit_one_lt hk hk₁ hc hc₁).le (sub_nonneg.mpr ht')
  have hU := mul_le_mul_of_nonneg_left (jointPureUnit_endpoint_lt (c := c) hk).le ht
  have h' : jointPureUnit k c p + jointClipPrice p ≤
      (1 - t) * (-(4423 / 10000)) + t * (-(39 / 4000)) := by linarith only [h,hL,hU]
  dsimp only [t] at h'
  linarith only [h',hp,hP]

end ACS12.GammaMeasure

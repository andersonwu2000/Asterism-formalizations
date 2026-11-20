import ACS12.BoseNoiseSixMoments

/-! Six complete moments and one signed quadratic square for all positive anchors. -/
namespace ACS12.NativeCells
open MeasureTheory
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000
theorem scaledBose_polynomial_integral (c : Fin 7 → ℝ) :
    Integrable (fun s => ∑ k : Fin 7, c k*(scaledBoseNoise s)^(k:ℕ)) boseNoiseMeasure ∧
    (∫ s, ∑ k : Fin 7, c k*(scaledBoseNoise s)^(k:ℕ) ∂boseNoiseMeasure) =
      ∑ k : Fin 7, c k*(![1,1,20/7,90/7,6000/77,4146000/7007,
        5400000/1001]:Fin 7 → ℝ) k := by
  constructor
  · exact integrable_finsetSum _ (fun (k : Fin 7) _ => (scaledBoseNoise_pow_integrable (k:ℕ)).const_mul (c k))
  · rw [integral_finsetSum _ (fun (k : Fin 7) _ => (scaledBoseNoise_pow_integrable (k:ℕ)).const_mul (c k))]
    simp_rw [integral_const_mul]
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    change scaledBoseMoment k = _
    fin_cases k <;> norm_num [
      scaledBoseMoment_0,scaledBoseMoment_1,scaledBoseMoment_2,scaledBoseMoment_3,
      scaledBoseMoment_4,scaledBoseMoment_5,scaledBoseMoment_6]

noncomputable def compensatedQuadratic (z : ℝ) := 1-z/6+z^2/108

theorem compensatedQuadratic_A :
    Integrable (fun s => scaledBoseNoise s*compensatedQuadratic (scaledBoseNoise s)) boseNoiseMeasure ∧
    (∫ s, scaledBoseNoise s*compensatedQuadratic (scaledBoseNoise s) ∂boseNoiseMeasure) = (9/14:ℝ) := by
  let c : Fin 7 → ℝ := ![0,1,-1/6,1/108,0,0,0]
  have hEq : (fun s => scaledBoseNoise s*compensatedQuadratic (scaledBoseNoise s)) =
      (fun s => ∑ k : Fin 7, c k*(scaledBoseNoise s)^(k:ℕ)) := by
    funext s
    norm_num [c,Fin.sum_univ_succ,compensatedQuadratic]
    <;> ring
  rw [hEq]
  refine ⟨(scaledBose_polynomial_integral c).1,?_⟩
  rw [(scaledBose_polynomial_integral c).2]
  norm_num [c,Fin.sum_univ_succ]

theorem compensatedQuadratic_B :
    Integrable (fun s => (scaledBoseNoise s)*(compensatedQuadratic (scaledBoseNoise s))^2) boseNoiseMeasure ∧
    (∫ s, (scaledBoseNoise s)*(compensatedQuadratic (scaledBoseNoise s))^2 ∂boseNoiseMeasure) = (140267/309582:ℝ) := by
  let c : Fin 7 → ℝ := ![0,1,-1/3,5/108,-1/324,1/11664,0]
  have hEq : (fun s => (scaledBoseNoise s)*(compensatedQuadratic (scaledBoseNoise s))^2) =
      (fun s => ∑ k : Fin 7, c k*(scaledBoseNoise s)^(k:ℕ)) := by
    funext s
    norm_num [c,Fin.sum_univ_succ,compensatedQuadratic]
    <;> ring
  rw [hEq]
  refine ⟨(scaledBose_polynomial_integral c).1,?_⟩
  rw [(scaledBose_polynomial_integral c).2]
  norm_num [c,Fin.sum_univ_succ]

theorem compensatedQuadratic_C :
    Integrable (fun s => (scaledBoseNoise s)^2*(compensatedQuadratic (scaledBoseNoise s))^2) boseNoiseMeasure ∧
    (∫ s, (scaledBoseNoise s)^2*(compensatedQuadratic (scaledBoseNoise s))^2 ∂boseNoiseMeasure) = (51410/63063:ℝ) := by
  let c : Fin 7 → ℝ := ![0,0,1,-1/3,5/108,-1/324,1/11664]
  have hEq : (fun s => (scaledBoseNoise s)^2*(compensatedQuadratic (scaledBoseNoise s))^2) =
      (fun s => ∑ k : Fin 7, c k*(scaledBoseNoise s)^(k:ℕ)) := by
    funext s
    norm_num [c,Fin.sum_univ_succ,compensatedQuadratic]
    <;> ring
  rw [hEq]
  refine ⟨(scaledBose_polynomial_integral c).1,?_⟩
  rw [(scaledBose_polynomial_integral c).2]
  norm_num [c,Fin.sum_univ_succ]

noncomputable def anchorMeanDen (β x z : ℝ) := 5*(β+1)/x+β+(1-β)*z
noncomputable def compensatedA : ℝ := 9/14
noncomputable def compensatedB : ℝ := 140267/309582
noncomputable def compensatedC : ℝ := 51410/63063
noncomputable def compensatedDen (β x : ℝ) :=
  (5*(β+1)/x+β)*compensatedB+(1-β)*compensatedC

theorem compensatedDen_pos {β x : ℝ} (hβ : 0≤β) (hβ₁ : β≤1) (hx : 0<x) :
    0<compensatedDen β x := by
  have h : 0<5*(β+1)/x+β := add_pos_of_pos_of_nonneg (by positivity) hβ
  unfold compensatedDen compensatedB compensatedC
  exact add_pos_of_pos_of_nonneg (mul_pos h (by norm_num)) (mul_nonneg (sub_nonneg.mpr hβ₁) (by norm_num))

theorem anchorMean_square_pointwise {β x z : ℝ}
    (hβ : 0≤β) (hβ₁ : β≤1) (hx : 0<x) (hz : 0≤z) :
    let a := compensatedA/compensatedDen β x
    2*a*z*compensatedQuadratic z-a^2*z*anchorMeanDen β x z*(compensatedQuadratic z)^2 ≤
      z/anchorMeanDen β x z := by
  have hD : 0<anchorMeanDen β x z := by
    unfold anchorMeanDen
    have hP:=mul_nonneg (sub_nonneg.mpr hβ₁) hz
    positivity
  dsimp only
  apply (le_div_iff₀ hD).mpr
  nlinarith only [mul_nonneg hz
    (sq_nonneg (1-compensatedA/compensatedDen β x*anchorMeanDen β x z*compensatedQuadratic z))]


theorem anchorMean_square_integral {β x : ℝ}
    (hβ : 0≤β) (hβ₁ : β≤1) (hx : 0<x) :
    compensatedA^2/compensatedDen β x ≤
      ∫ s, scaledBoseNoise s/anchorMeanDen β x (scaledBoseNoise s) ∂boseNoiseMeasure := by
  let Z:=scaledBoseNoise
  let a:=compensatedA/compensatedDen β x
  let b:=5*(β+1)/x
  let F (s : BoseNoiseSample):=2*a*Z s*compensatedQuadratic (Z s)-
    a^2*Z s*anchorMeanDen β x (Z s)*(compensatedQuadratic (Z s))^2
  have hb : 0<b := by unfold b; positivity
  have hDe : ∀ᵐ s ∂boseNoiseMeasure, b≤anchorMeanDen β x (Z s) := by
    filter_upwards [scaledBoseNoise_ae_pos] with s hs
    have hP:=mul_nonneg (sub_nonneg.mpr hβ₁) hs.le
    change b≤b+β+(1-β)*Z s
    linarith only [hβ,hP]
  have hGI : Integrable (fun s=>Z s/anchorMeanDen β x (Z s)) boseNoiseMeasure := by
    apply ((scaledBoseNoise_pow_integrable 1).div_const b).mono'
      ((scaledBoseNoise_measurable.div
        ((scaledBoseNoise_measurable.const_mul (1-β)).const_add (b+β))).aestronglyMeasurable)
    filter_upwards [scaledBoseNoise_ae_pos,hDe] with s hs hD
    have hDen:=hb.trans_le hD
    change ‖Z s/anchorMeanDen β x (Z s)‖≤(Z s)^1/b
    rw [Real.norm_of_nonneg (div_nonneg hs.le hDen.le),pow_one]
    exact div_le_div_of_nonneg_left hs.le hb hD
  have hF : F=(fun s => (2*a)*(Z s*compensatedQuadratic (Z s))-
      (a^2*(b+β))*(Z s*(compensatedQuadratic (Z s))^2)-
      (a^2*(1-β))*((Z s)^2*(compensatedQuadratic (Z s))^2)) := by
    funext s
    unfold F anchorMeanDen b
    ring
  have hFI : Integrable F boseNoiseMeasure := by
    rw [hF]
    exact ((compensatedQuadratic_A.1.const_mul _).sub
      (compensatedQuadratic_B.1.const_mul _)).sub (compensatedQuadratic_C.1.const_mul _)
  have hCmp:=integral_mono_ae hFI hGI (scaledBoseNoise_ae_pos.mono
    fun s hs=>anchorMean_square_pointwise hβ hβ₁ hx hs.le)
  have hInt : (∫ s,F s ∂boseNoiseMeasure)=
      2*a*compensatedA-a^2*compensatedDen β x := by
    have hAI:=compensatedQuadratic_A.1.const_mul (2*a)
    have hBI:=compensatedQuadratic_B.1.const_mul (a^2*(b+β))
    have hCI:=compensatedQuadratic_C.1.const_mul (a^2*(1-β))
    have hSub₁:=integral_sub hAI hBI
    have hSub₂:=integral_sub (hAI.sub hBI) hCI
    dsimp only [Pi.sub_apply] at hSub₁ hSub₂
    rw [hF]
    dsimp only [Z]
    rw [hSub₂,hSub₁]
    simp only [integral_const_mul,compensatedQuadratic_A.2,compensatedQuadratic_B.2,compensatedQuadratic_C.2]
    unfold compensatedDen compensatedA compensatedB compensatedC b
    ring
  rw [hInt] at hCmp
  have hEq : 2*a*compensatedA-a^2*compensatedDen β x=
      compensatedA^2/compensatedDen β x := by
    unfold a
    field_simp [(compensatedDen_pos hβ hβ₁ hx).ne']
    <;> ring
  rwa [hEq] at hCmp

theorem anchorMean_quadratic_lower {β x : ℝ}
    (hβ : 0≤β) (hβ₁ : β≤1) (hx : 0<x) :
    9*x/(x*(18-8*β)+50*(1+β)) <
      ∫ s, scaledBoseNoise s/anchorMeanDen β x (scaledBoseNoise s) ∂boseNoiseMeasure := by
  let K:=5*(β+1)/x+β+(1-β)*9/5
  let E:=x*(18-8*β)+50*(1+β)
  have hK : 0<K := by
    have h₀ : 0<5*(β+1)/x := by positivity
    have h₁:=mul_nonneg (sub_nonneg.mpr hβ₁) (by norm_num : (0:ℝ)≤13/8)
    unfold K
    linarith only [h₀,h₁,hβ]
  have hE : E=10*x*K := by
    unfold E K
    field_simp [hx.ne']
    <;> ring
  have hE₀ : 0<E := by rw [hE]; exact mul_pos (mul_pos (by norm_num) hx) hK
  have hAB : 9*compensatedB<10*compensatedA^2 := by
    norm_num [compensatedA,compensatedB]
  have hCB : compensatedC≤9/5*compensatedB := by
    norm_num [compensatedB,compensatedC]
  have hD : compensatedDen β x≤K*compensatedB := by
    have h:=mul_le_mul_of_nonneg_left hCB (sub_nonneg.mpr hβ₁)
    unfold compensatedDen K
    nlinarith only [h]
  have hStrict : 9*x*compensatedDen β x<compensatedA^2*E := by
    have h:=mul_le_mul_of_nonneg_left hD (mul_nonneg (by norm_num : (0:ℝ)≤9) hx.le)
    have h':=mul_lt_mul_of_pos_left hAB (mul_pos hx hK)
    rw [hE]
    nlinarith only [h,h']
  have hRatio : 9*x/E<compensatedA^2/compensatedDen β x :=
    (div_lt_div_iff₀ hE₀ (compensatedDen_pos hβ hβ₁ hx)).mpr hStrict
  exact hRatio.trans_le (anchorMean_square_integral hβ hβ₁ hx)

end ACS12.NativeCells

import ACS12.NativeAdaptedAnchor

/-! The exact raw-mean debit paid by the quantitative literal SELF remainder. -/
namespace ACS12.NativeCells
open Set Filter MeasureTheory
set_option maxHeartbeats 1000000

noncomputable def selfTangentShape (t : ℝ) := t-3/2+1/(2*t^2)
noncomputable def rawMeanTangent (m t : ℝ) :=
  (2*m-1)*(t-1)-Real.log ((1-m+m*t^2)/((1+t^2)/2))
noncomputable def rawMeanTangentSlope (m t : ℝ) :=
  (t-1)^2*(2*m*(t+1)-1)/(1-m+m*t^2)

theorem selfTangentShape_pos {t : ℝ} (ht : 0<t) (ht₁ : t≠1) : 0<selfTangentShape t := by
  have hE : selfTangentShape t=(t-1)^2*(2*t+1)/(2*t^2) := by
    unfold selfTangentShape
    field_simp [ht.ne']
    <;> ring
  rw [hE]
  exact div_pos (mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr ht₁)) (by positivity)) (by positivity)

private theorem rawMeanArgument_pos {m t : ℝ} (hm : m∈Icc (0:ℝ) 1) (ht : 0<t) :
    0<1-m+m*t^2 := by
  by_cases hz : m=0
  · simp [hz]
  · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr hm.2)
      (mul_pos (lt_of_le_of_ne hm.1 (Ne.symm hz)) (sq_pos_of_pos ht))

theorem rawMeanTangent_hasDerivAt {m t : ℝ} (hm : m∈Icc (0:ℝ) 1) (ht : 0<t) :
    HasDerivAt (fun a=>rawMeanTangent a t) (rawMeanTangentSlope m t) m := by
  have hA:=rawMeanArgument_pos hm ht
  have hB : 0<(1+t^2)/2 := by positivity
  have hArg:=(((hasDerivAt_id m).const_sub 1).add
    ((hasDerivAt_id m).mul_const (t^2))).div_const ((1+t^2)/2)
  have hLog:=hArg.log (div_pos hA hB).ne'
  have hFirst:=((((hasDerivAt_id m).const_mul 2).sub_const 1).mul_const (t-1))
  convert hFirst.sub hLog using 1
  unfold rawMeanTangentSlope
  simp only [id_eq,mul_one,one_mul,Pi.add_apply]
  field_simp [hA.ne',hB.ne']
  ring_nf at hA ⊢
  field_simp [hA.ne']
  <;> ring

theorem rawMeanSlope_le_shape {m t : ℝ} (hm : m∈Icc (0:ℝ) 1) (ht : 0<t) :
    rawMeanTangentSlope m t≤2*selfTangentShape t := by
  have hA:=rawMeanArgument_pos hm ht
  have hE : 2*selfTangentShape t-rawMeanTangentSlope m t=
      (t-1)^2*(1-m)*(t+1)^2/(t^2*(1-m+m*t^2)) := by
    unfold rawMeanTangentSlope selfTangentShape
    field_simp [ht.ne',hA.ne']
    ring_nf at hA ⊢
    field_simp [hA.ne']
    <;> ring
  have hP : 0≤(t-1)^2*(1-m)*(t+1)^2/(t^2*(1-m+m*t^2)) :=
    div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hm.2)) (sq_nonneg _))
      (mul_nonneg (sq_nonneg _) hA.le)
  linarith only [hE,hP]

theorem rawMeanTangent_debit {m t : ℝ} (hm : m∈Icc (0:ℝ) 1) (ht : 0<t) :
    -max (1-2*m) 0*selfTangentShape t≤rawMeanTangent m t := by
  have hB : 0<(1+t^2)/2 := by positivity
  by_cases hHalf : 1/2≤m
  · have hA:=rawMeanArgument_pos hm ht
    have hLog:=Real.log_le_sub_one_of_pos (div_pos hA hB)
    have hE : (2*m-1)*(t-1)-((1-m+m*t^2)/((1+t^2)/2)-1)=
        (2*m-1)*((t-1)^2*t)/(1+t^2) := by
      field_simp
      <;> ring
    have hP : 0≤(2*m-1)*((t-1)^2*t)/(1+t^2) := by
      apply div_nonneg
      · exact mul_nonneg (by linarith only [hHalf]) (mul_nonneg (sq_nonneg _) ht.le)
      · positivity
    rw [max_eq_right (by linarith only [hHalf]),neg_zero,zero_mul]
    unfold rawMeanTangent
    linarith only [hLog,hE,hP]
  · have hmHalf : m≤1/2 := (lt_of_not_ge hHalf).le
    let H (a : ℝ):=rawMeanTangent a t-2*a*selfTangentShape t
    have hD (a : ℝ) (ha : a∈Icc (0:ℝ) 1) :
        HasDerivAt H (rawMeanTangentSlope a t-2*selfTangentShape t) a := by
      convert (rawMeanTangent_hasDerivAt ha ht).sub
        (((hasDerivAt_id a).const_mul 2).mul_const (selfTangentShape t)) using 1 <;> simp [H]
    have hAnti : AntitoneOn H (Icc (0:ℝ) 1) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      · exact fun a ha=>(hD a ha).continuousAt.continuousWithinAt
      · exact fun a ha=>(hD a (interior_subset ha)).differentiableAt.differentiableWithinAt
      · intro a ha
        rw [(hD a (interior_subset ha)).deriv]
        exact sub_nonpos.mpr (rawMeanSlope_le_shape (interior_subset ha) ht)
    have h:=hAnti hm (show (1/2:ℝ)∈Icc (0:ℝ) 1 by norm_num) hmHalf
    have hContact : rawMeanTangent (1/2) t=0 := by
      unfold rawMeanTangent
      rw [show 1-(1/2:ℝ)+(1/2)*t^2=(1+t^2)/2 by ring,
        div_self hB.ne',Real.log_one]
      ring
    dsimp only [H] at h
    rw [hContact] at h
    rw [max_eq_left (by linarith only [hmHalf])]
    linarith only [h]


theorem adaptedAnchor_logTangent_debit {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {Y : Ω→ℝ} (hY : Measurable Y)
    (hYrange : ∀ᵐ s ∂μ,Y s∈Icc (0:ℝ) 1) {β t : ℝ}
    (hβ : 0≤β) (hβ₁ : β≤1) (ht : 0<t)
    (hU : 0<∫ s,(1+Y s*(t^2-1))^β ∂μ) :
    -β*max (1-2*(∫ s,Y s ∂μ)) 0*selfTangentShape t≤
      β*(2*(∫ s,Y s ∂μ)-1)*(t-1)-
        Real.log ((∫ s,(1+Y s*(t^2-1))^β ∂μ)/((1+t^2)/2)^β) := by
  let m:=∫ s,Y s ∂μ
  let A:=1-m+m*t^2
  let B:=(1+t^2)/2
  let U:=∫ s,(1+Y s*(t^2-1))^β ∂μ
  have hI : MeasureTheory.Integrable Y μ := by
    apply (MeasureTheory.integrable_const (μ:=μ) (1:ℝ)).mono' hY.aestronglyMeasurable
    filter_upwards [hYrange] with s hs
    simpa only [Real.norm_of_nonneg hs.1] using hs.2
  have hm₀ : 0≤m:=MeasureTheory.integral_nonneg_of_ae (hYrange.mono fun _ hs=>hs.1)
  have hm₁ : m≤1:=by
    have h:=MeasureTheory.integral_mono_ae hI (MeasureTheory.integrable_const (μ:=μ) (1:ℝ))
      (hYrange.mono fun _ hs=>hs.2)
    simpa only [MeasureTheory.integral_const,MeasureTheory.probReal_univ,one_smul] using h
  have hA : 0<A:=rawMeanArgument_pos ⟨hm₀,hm₁⟩ ht
  have hB : 0<B:=by unfold B;positivity
  have hJ : U≤A^β:=by
    by_cases hz : β=0
    · subst β
      simp only [U,Real.rpow_zero,MeasureTheory.integral_const,MeasureTheory.probReal_univ,one_smul,le_refl]
    · exact adaptedAnchor_Jensen hY hYrange (lt_of_le_of_ne hβ (Ne.symm hz)) hβ₁
  have hLog : Real.log (U/B^β)≤β*Real.log (A/B):=by
    have h:=Real.log_le_log (div_pos hU (Real.rpow_pos_of_pos hB _))
      (div_le_div_of_nonneg_right hJ (Real.rpow_nonneg hB.le β))
    rw [←Real.div_rpow hA.le hB.le,Real.log_rpow (div_pos hA hB)] at h
    exact h
  have hScalar:=rawMeanTangent_debit ⟨hm₀,hm₁⟩ ht
  have hPay:=mul_le_mul_of_nonneg_left hScalar hβ
  change -β*max (1-2*m) 0*selfTangentShape t≤β*(2*m-1)*(t-1)-Real.log (U/B^β)
  unfold rawMeanTangent at hPay
  change _≤β*((2*m-1)*(t-1)-Real.log (A/B)) at hPay
  nlinarith only [hPay,hLog]

end ACS12.NativeCells

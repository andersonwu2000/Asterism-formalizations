import ACS12.JointFarEnvelopes
import ACS12.PowerConvex
import ACS12.ConcaveSupport
import ACS12.JointLawDifference

/-! W40 for the complete pure fourth source, including the shifted Bose moment. -/
namespace ACS12.GammaMeasure

open Set MeasureTheory Filter CenteredCircle.AllN
open GammaDeficit (lineDensity)

private noncomputable def farFourthMoment (p : ℝ) (k : ℕ) : ℝ :=
  ∫ s : ℝ in Ioi 0, lineDensity p s * polyB s * Real.exp (-s * (k : ℝ)) * BoseShape.C s

private theorem farFourthMoment_scaled {p t : ℝ} (ht : 0 < t) (k : ℕ) :
    (∫ s : ℝ in Ioi 0, lineDensity p s * polyB (t * s) * Real.exp (-(t * s) * (k : ℝ)) * BoseShape.C (t * s)) =
      t ^ (-p) * farFourthMoment p k := by
  let F (s : ℝ) := lineDensity p s * polyB s * Real.exp (-s * (k : ℝ)) * BoseShape.C s
  have hE (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      lineDensity p s * polyB (t * s) * Real.exp (-(t * s) * (k : ℝ)) * BoseShape.C (t * s) =
        t ^ (-(p - 1)) * F (s * t) := by
    have hs₀ : 0 < s := hs
    have hρ : lineDensity p (t * s) = t ^ (p - 1) * lineDensity p s := by
      unfold lineDensity
      rw [Real.mul_rpow ht.le hs₀.le]
      ring
    have hP : t ^ (-(p - 1)) * t ^ (p - 1) = 1 := by
      rw [← Real.rpow_add ht,neg_add_cancel,Real.rpow_zero]
    unfold F
    rw [mul_comm s t,hρ]
    calc
      _ = (t ^ (-(p - 1)) * t ^ (p - 1)) *
        (lineDensity p s * polyB (t * s) * Real.exp (-(t * s) * (k : ℝ)) * BoseShape.C (t * s)) := by rw [hP,one_mul]
      _ = _ := by ring
  rw [setIntegral_congr_fun measurableSet_Ioi hE,integral_const_mul,
    integral_comp_mul_right_Ioi F 0 ht,zero_mul,smul_eq_mul,← mul_assoc]
  change t ^ (-(p - 1)) * t⁻¹ * farFourthMoment p k = _
  rw [← div_eq_mul_inv,← Real.rpow_sub_one ht.ne',show -(p - 1) - 1 = -p by ring]

private theorem farFourthMoment_nonneg {p : ℝ} (hp : 0 < p) (k : ℕ) :
    0 ≤ farFourthMoment p k := by
  unfold farFourthMoment
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs₀ : 0 < s := hs
  exact mul_nonneg (mul_nonneg (mul_nonneg (lineDensity_pos hp hs₀).le (polyB_pos hs₀).le)
    (Real.exp_pos _).le) (BoseShape.C_pos hs₀).le

private theorem farFourth_rpow_midpoint {a b q : ℝ} (ha : 0 < a) (hab : a ≤ b) (hq : 0 < q) :
    (b - a) * ((a + b) / 2) ^ (-q) ≤ ∫ t : ℝ in a..b, t ^ (-q) := by
  let c := (a + b) / 2
  have hc : 0 < c := by unfold c; linarith only [ha,hab]
  let f (x : ℝ) := -(x ^ (-q))
  let D := q * c ^ (-q - 1)
  have hD : HasDerivAt f D c := by
    simpa only [f,D,neg_mul,neg_neg] using (Real.hasDerivAt_rpow_const (p := -q) (Or.inl hc.ne')).neg
  have h (x : ℝ) (hx : x ∈ Icc a b) : c ^ (-q) - D * (x - c) ≤ x ^ (-q) := by
    have h := ACS12.concave_tangent_upper (negativePower_convex hq).neg (ha.trans_le hx.1) hc hD
    change -(x ^ (-q)) ≤ -(c ^ (-q)) + D * (x - c) at h
    linarith only [h]
  have hI : IntervalIntegrable (fun t : ℝ => t ^ (-q)) volume a b :=
    (continuousOn_id.rpow_const (fun x hx => Or.inl (ha.trans_le (mem_Icc.mp hx).1).ne')).intervalIntegrable_of_Icc hab
  have hT : IntervalIntegrable (fun x : ℝ => c ^ (-q) - D * (x - c)) volume a b := by
    exact (by fun_prop : Continuous (fun x : ℝ => c ^ (-q) - D * (x - c))).intervalIntegrable _ _
  have hK := intervalIntegral.integral_mono_on hab hT hI h
  have hId : IntervalIntegrable (fun t : ℝ => t) volume a b := continuous_id.intervalIntegrable _ _
  have hLin : (∫ x : ℝ in a..b, x - c) = 0 := by
    rw [intervalIntegral.integral_sub hId (intervalIntegrable_const),
      integral_id,intervalIntegral.integral_const,smul_eq_mul]
    unfold c
    ring
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    ((hId.sub intervalIntegrable_const).const_mul D),
    intervalIntegral.integral_const,smul_eq_mul,intervalIntegral.integral_const_mul,hLin,mul_zero,sub_zero] at hK
  exact hK

private theorem farFourth_component {p m a b : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hm : 0 < m) (hma : m ≤ a) (hab : a ≤ b) (k : ℕ) :
    m ^ 2 * farFourthMoment p k * ((b - a) * ((a + b) / 2) ^ (-p - 2)) ≤
      ∫ s : ℝ in Ioi 0, lineDensity p s * polyB (m * s) * Real.exp (-(a * s) * (k : ℝ)) *
        (scaledExpTail s a - scaledExpTail s b) := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  let ν := volume.restrict (Ioc a b)
  let F (s t : ℝ) := (m / t) ^ 2 *
    (lineDensity p s * polyB (t * s) * Real.exp (-(t * s) * (k : ℝ)) * BoseShape.C (t * s))
  let G (s : ℝ) := lineDensity p s * polyB (m * s) * BoseShape.C (m * s)
  let B (s : ℝ) := lineDensity p s * polyB (m * s) * Real.exp (-(a * s) * (k : ℝ)) *
    (scaledExpTail s a - scaledExpTail s b)
  have ha := hm.trans_le hma
  have hb := ha.trans_le hab
  have hp₀ := zero_lt_one.trans_le hp
  have hG : Integrable G μ := by
    apply Integrable.of_integral_ne_zero
    change (∫ s : ℝ in Ioi 0, lineDensity p s * polyB (m * s) * BoseShape.C (m * s)) ≠ 0
    rw [pureBoseB_moment_scaled hp hp₂ hm]
    have hz := powerTail_pos (show 1 < p + 1 by linarith only [hp]) (m := 1) (by decide)
    exact (mul_pos (Real.rpow_pos_of_pos hm _) (add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg (mul_nonneg hp₀.le (sub_nonneg.mpr hp)) hz.le))).ne'
  have hP (s : ℝ) (hs : 0 < s) (t : ℝ) (hmt : m ≤ t) :
      0 ≤ F s t ∧ F s t ≤ lineDensity p s * polyB (m * s) *
        Real.exp (-(t * s) * (k : ℝ)) * BoseShape.C (t * s) := by
    have ht := hm.trans_le hmt
    have hB := polyB_scale_lower (div_pos hm ht) ((div_le_one ht).mpr hmt) (mul_pos ht hs)
    rw [show m / t * (t * s) = m * s by field_simp [ht.ne']] at hB
    have hρ := (lineDensity_pos hp₀ hs).le
    have hC := (BoseShape.C_pos (mul_pos ht hs)).le
    have hX := (Real.exp_pos (-(t * s) * (k : ℝ))).le
    have h := mul_le_mul_of_nonneg_right hB (mul_nonneg (mul_nonneg hρ hX) hC)
    constructor
    · unfold F
      exact mul_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg
        (mul_nonneg hρ (polyB_pos (mul_pos ht hs)).le) hX) hC)
    · unfold F
      nlinarith only [h]
  have hDom (s : ℝ) (hs : 0 < s) (t : ℝ) (hmt : m ≤ t) : F s t ≤ G s := by
    have ht := hm.trans_le hmt
    have hC := BoseShape.C_antitone (mul_pos hm hs) (mul_pos ht hs) (mul_le_mul_of_nonneg_right hmt hs.le)
    have hE : Real.exp (-(t * s) * (k : ℝ)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_pos ht hs).le) (Nat.cast_nonneg _))
    have h := mul_le_mul hE hC (BoseShape.C_pos (mul_pos ht hs)).le zero_le_one
    have hρ := mul_nonneg (lineDensity_pos hp₀ hs).le (polyB_pos (mul_pos hm hs)).le
    have he := mul_le_mul_of_nonneg_left h hρ
    unfold G
    exact (hP s hs t hmt).2.trans (by simpa only [mul_assoc,one_mul] using he)
  have hMF : Measurable (Function.uncurry F) := by
    unfold Function.uncurry F lineDensity polyB BoseShape.C
    fun_prop
  have hMI : Integrable (Function.uncurry F) (μ.prod ν) := by
    haveI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr (by simp)
    apply (hG.comp_fst ν).mono' hMF.aestronglyMeasurable
    have hAE : ∀ᵐ z ∂μ.prod ν, z ∈ Ioi (0 : ℝ) ×ˢ Ioc a b := by
      apply (Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Ioi.prod measurableSet_Ioc)).mpr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact ⟨hs,ht⟩
    filter_upwards [hAE] with z hz
    have hz₁ : 0 < z.1 := hz.1
    have hz₂ : m ≤ z.2 := hma.trans hz.2.1.le
    simpa only [Function.uncurry,Real.norm_of_nonneg (hP z.1 hz₁ z.2 hz₂).1] using hDom z.1 hz₁ z.2 hz₂
  have hGap (s : ℝ) (hs : 0 < s) :
      scaledExpTail s a - scaledExpTail s b = ∫ t : ℝ in a..b, BoseShape.C (s * t) := by
    have hD (t : ℝ) (ht : t ∈ uIcc a b) :
        HasDerivAt (fun t => -scaledExpTail s t) (BoseShape.C (s * t)) t := by
      rw [uIcc_of_le hab] at ht
      simpa only [neg_neg] using (scaledExpTail_derivative hs (ha.trans_le ht.1)).neg
    have hC : ContinuousOn (fun t : ℝ => BoseShape.C (s * t)) (Icc a b) := by
      intro t ht
      exact (((BoseShape.C_deriv (mul_pos hs (ha.trans_le ht.1))).comp t
        ((hasDerivAt_id t).const_mul s)).continuousAt.continuousWithinAt)
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hD (hC.intervalIntegrable_of_Icc hab)
    linarith only [h]
  have hGapped (s : ℝ) (hs : 0 < s) : (∫ t, F s t ∂ν) ≤ B s := by
    let A := lineDensity p s * polyB (m * s) * Real.exp (-(a * s) * (k : ℝ))
    have hA := mul_nonneg (mul_nonneg (lineDensity_pos hp₀ hs).le (polyB_pos (mul_pos hm hs)).le)
      (Real.exp_pos (-(a * s) * (k : ℝ))).le
    change (∫ t : ℝ in Ioc a b, F s t) ≤ A * _
    rw [← intervalIntegral.integral_of_le hab,hGap s hs,← intervalIntegral.integral_const_mul]
    have hF : ContinuousOn (F s) (Icc a b) := by
      intro t ht
      have ht₀ : 0 < t := ha.trans_le ht.1
      have hC := ((BoseShape.C_deriv (mul_pos ht₀ hs)).comp t ((hasDerivAt_id t).mul_const s)).continuousAt
      have hB := ((hasDerivAt_polyB (t * s)).comp t ((hasDerivAt_id t).mul_const s)).continuousAt
      unfold F
      have h₁ : ContinuousAt (fun t : ℝ => (m / t) ^ 2) t := by fun_prop (disch := exact ht₀.ne')
      have h₂ : ContinuousAt (fun t : ℝ => Real.exp (-(t * s) * (k : ℝ))) t := by fun_prop
      exact (h₁.mul (((continuousAt_const.mul hB).mul h₂).mul hC)).continuousWithinAt
    have hU : ContinuousOn (fun t : ℝ => A * BoseShape.C (s * t)) (Icc a b) := by
      intro t ht
      exact ((((BoseShape.C_deriv (mul_pos hs (ha.trans_le ht.1))).comp t
        ((hasDerivAt_id t).const_mul s)).continuousAt.const_mul A).continuousWithinAt)
    apply intervalIntegral.integral_mono_on hab (hF.intervalIntegrable_of_Icc hab) (hU.intervalIntegrable_of_Icc hab)
    intro t ht
    have ht₀ := ha.trans_le ht.1
    have hE := Real.exp_le_exp.mpr (show -(t * s) * (k : ℝ) ≤ -(a * s) * (k : ℝ) from
      mul_le_mul_of_nonneg_right (neg_le_neg (mul_le_mul_of_nonneg_right ht.1 hs.le)) (Nat.cast_nonneg _))
    have he := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE
      (mul_nonneg (lineDensity_pos hp₀ hs).le (polyB_pos (mul_pos hm hs)).le))
      (BoseShape.C_pos (mul_pos ht₀ hs)).le
    exact (hP s hs t (hma.trans ht.1)).2.trans (by unfold A; simpa only [mul_comm t s] using he)
  have hBI : Integrable B μ := by
    have hM : Measurable B := by
      unfold B lineDensity polyB scaledExpTail
      fun_prop
    apply (hG.const_mul (b - a)).mono' hM.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0 < s := hs
    have hGap₀ := sub_nonneg.mpr ((scaledExpTail_strictAnti hs₀).antitoneOn ha hb hab)
    have hGapU : scaledExpTail s a - scaledExpTail s b ≤ (b - a) * BoseShape.C (m * s) := by
      rw [hGap s hs₀,show (b - a) * BoseShape.C (m * s) = (∫ _ : ℝ in a..b, BoseShape.C (m * s)) by
        rw [intervalIntegral.integral_const,smul_eq_mul]]
      have hC : ContinuousOn (fun t : ℝ => BoseShape.C (s * t)) (Icc a b) := by
        intro t ht
        exact (((BoseShape.C_deriv (mul_pos hs₀ (ha.trans_le ht.1))).comp t
          ((hasDerivAt_id t).const_mul s)).continuousAt.continuousWithinAt)
      apply intervalIntegral.integral_mono_on hab (hC.intervalIntegrable_of_Icc hab) intervalIntegrable_const
      intro t ht
      exact BoseShape.C_antitone (mul_pos hm hs₀) (mul_pos hs₀ (ha.trans_le ht.1))
        (by rw [mul_comm s t]; exact mul_le_mul_of_nonneg_right (hma.trans ht.1) hs₀.le)
    have hE : Real.exp (-(a * s) * (k : ℝ)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_pos ha hs₀).le) (Nat.cast_nonneg _))
    have hρ := mul_nonneg (lineDensity_pos hp₀ hs₀).le (polyB_pos (mul_pos hm hs₀)).le
    have h := mul_le_mul hE hGapU hGap₀ zero_le_one
    have he := mul_le_mul_of_nonneg_left h hρ
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg hρ (Real.exp_pos _).le) hGap₀)]
    unfold G
    nlinarith only [he]
  have hCompare : (∫ s, ∫ t, F s t ∂ν ∂μ) ≤ ∫ s, B s ∂μ := by
    apply integral_mono_ae hMI.integral_prod_left hBI
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact hGapped s hs
  rw [integral_integral_swap hMI] at hCompare
  have hValue (t : ℝ) (ht : t ∈ Ioc a b) : (∫ s, F s t ∂μ) =
      m ^ 2 * farFourthMoment p k * t ^ (-p - 2) := by
    have ht₀ : 0 < t := ha.trans ht.1
    unfold F μ
    rw [integral_const_mul,farFourthMoment_scaled ht₀ k,show -p - 2 = -p - ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_sub_natCast ht₀.ne' (-p) 2]
    norm_num only [Nat.cast_ofNat]
    ring
  change (∫ t : ℝ in Ioc a b, ∫ s, F s t ∂μ) ≤ _ at hCompare
  rw [setIntegral_congr_fun measurableSet_Ioc hValue,integral_const_mul,
    ← intervalIntegral.integral_of_le hab] at hCompare
  have hMid := farFourth_rpow_midpoint ha hab (show 0 < p + 2 by positivity)
  rw [show -(p + 2) = -p - 2 by ring] at hMid
  exact (mul_le_mul_of_nonneg_left hMid
    (mul_nonneg (sq_nonneg _) (farFourthMoment_nonneg hp₀ k))).trans hCompare

theorem jointFarFourth_full_upper {p L : ℝ} (hp : 1 ≤ p) (hpP : p ≤ 9 / 5) (hL : 0 < L) :
    fourthSourceRow p L 0 (7 / 8) (3 / 4) (3 / 4) (3 / 4) ≤ jointFarFourth p := by
  let m : ℝ := 3 / 4
  let u : ℝ := 7 / 8
  let μ := volume.restrict (Ioi (0 : ℝ))
  let A (s : ℝ) := lineDensity p s * polyB (m * s) * Real.exp (-(m * s) * (0 : ℝ)) *
    (scaledExpTail s m - scaledExpTail s u)
  let B (s : ℝ) := lineDensity p s * polyB (m * s) * Real.exp (-(u * s) * (1 : ℝ)) *
    (scaledExpTail s u - scaledExpTail s 1)
  have hm : 0 < m := by norm_num [m]
  have hu : 0 < u := by norm_num [u]
  have hp₂ : p ≤ 2 := hpP.trans (by norm_num)
  have hθ : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl,zero_le_one⟩
  obtain ⟨hI,hEq⟩ := fourthSourceRow_integral (p := p) (u := u) (v := m) (r := m) (m := m) hp hp₂ hL hθ hu hm hm
  simp only [lawDensity,sub_zero,one_mul,zero_mul,add_zero,sub_self] at hI hEq
  have hSum (s : ℝ) (hs : s ∈ Ioi 0) : - (lineDensity p s * fourthDensity u m m m s) = A s + B s := by
    have hF := fourthSourceResponse_eq (r := m) hu hm (mem_Ioi.mp hs)
    simp only [fourthSourceResponse,sub_self,zero_sub,adjacentBoseGap,zero_add, mul_zero,add_zero] at hF
    unfold A B
    simp only [mul_zero,Real.exp_zero,mul_one]
    rw [show -(u * s) = -s * u by ring]
    have h : lineDensity p s * (-fourthDensity u m m m s) =
        lineDensity p s * (polyB (m * s) * (scaledExpTail s m - scaledExpTail s u +
          Real.exp (-s * u) * (scaledExpTail s u - scaledExpTail s 1))) :=
      congrArg (fun z : ℝ => lineDensity p s * z) hF
    nlinarith only [h]
  have hAI : Integrable A μ := by
    apply (hI.neg).mono' (by unfold A lineDensity polyB scaledExpTail; fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    change ‖A s‖ ≤ -(lineDensity p s * fourthDensity u m m m s)
    rw [hSum s hs]
    have hs₀ : 0 < s := hs
    have hA₀ : 0 ≤ A s := by
      unfold A
      exact mul_nonneg (by have := lineDensity_pos (zero_lt_one.trans_le hp) hs₀; have := polyB_pos (mul_pos hm hs₀); positivity)
        (sub_nonneg.mpr ((scaledExpTail_strictAnti hs₀).antitoneOn hm hu (by norm_num [m,u])))
    have hB₀ : 0 ≤ B s := by
      unfold B
      exact mul_nonneg (by have := lineDensity_pos (zero_lt_one.trans_le hp) hs₀; have := polyB_pos (mul_pos hm hs₀); positivity)
        (sub_nonneg.mpr ((scaledExpTail_strictAnti hs₀).antitoneOn hu (mem_Ioi.mpr zero_lt_one) (by norm_num [u])))
    rw [Real.norm_of_nonneg hA₀]
    exact le_add_of_nonneg_right hB₀
  have hBI : Integrable B μ := by
    apply (hI.neg.sub hAI).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    change -(lineDensity p s * fourthDensity u m m m s) - A s = B s
    rw [hSum s hs,add_sub_cancel_left]
  change fourthSourceRow p L 0 u m m m ≤ _
  have hTotal : -fourthSourceRow p L 0 u m m m = (∫ s, A s ∂μ) + ∫ s, B s ∂μ := by
    rw [hEq,← integral_neg,setIntegral_congr_fun measurableSet_Ioi hSum,integral_add hAI hBI]
  have hA := farFourth_component (m := m) (a := m) (b := u) hp hp₂ hm le_rfl (by norm_num [m,u]) 0
  have hB := farFourth_component (m := m) (a := u) (b := 1) hp hp₂ hm (by norm_num [m,u]) (by norm_num [u]) 1
  have h0 : farFourthMoment p 0 = 1 + pureP p := by
    have h := pureBoseB_moment hp hp₂ 0
    simpa only [farFourthMoment,pureP,Nat.cast_zero,zero_add,mul_zero,neg_zero,Real.exp_zero,mul_one,
      Real.one_rpow,zero_mul,sub_zero,Nat.zero_add] using h
  have h1 : farFourthMoment p 1 = 2 * p + pureP p - pureQ p + (2 : ℝ) ^ (-p) := by
    simpa only [farFourthMoment,Nat.cast_one,mul_one] using pureBoseBX_moment hp hp₂
  norm_num only [Nat.cast_zero] at hA
  norm_num only [Nat.cast_one] at hB
  change _ ≤ ∫ s, A s ∂μ at hA
  change _ ≤ ∫ s, B s ∂μ at hB
  rw [h0] at hA
  rw [h1] at hB
  norm_num [m,u] at hA hB
  unfold jointFarFourth
  linarith only [hA,hB,hTotal]

end ACS12.GammaMeasure

import ACS12.JointBoseSquaredMoment

/-! Exact integration by parts for the original sharp source-gap moments. -/
namespace ACS12.GammaMeasure

open MeasureTheory Set Filter CenteredCircle.AllN
open scoped Topology
open GammaDeficit (lineDensity)

noncomputable def sharpGapPrimitive (p b s : ℝ) : ℝ :=
  lineDensity p s * s * Real.exp (-s * b) * polyA s * BoseShape.C s

noncomputable def sharpGapDerivative (p b s : ℝ) : ℝ :=
  (p * (lineDensity p s * Real.exp (-s * b) * polyA s * BoseShape.C s) -
    b * (lineDensity p s * s * Real.exp (-s * b) * polyA s * BoseShape.C s) +
    lineDensity p s * s ^ 2 * Real.exp (-s * (b + 1)) * BoseShape.C s) -
    lineDensity p s * Real.exp (-s * b) * polyA s * s * (-BoseShape.C₁ s)

private theorem lineDensity_mul_eq {p s : ℝ} (hs : 0 < s) :
    lineDensity p s * s = s ^ p / Real.Gamma p := by
  rw [lineDensity,Real.rpow_sub_one hs.ne']
  field_simp [hs.ne']

theorem sharpGapPrimitive_deriv (p b : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (sharpGapPrimitive p b) (sharpGapDerivative p b s) s := by
  have hP : HasDerivAt (fun t => lineDensity p t * t) (p * lineDensity p s) s := by
    have h := (Real.hasDerivAt_rpow_const (p := p) (Or.inl hs.ne')).div_const (Real.Gamma p)
    apply (show HasDerivAt (fun t => t ^ p / Real.Gamma p) (p * lineDensity p s) s from
      by simpa only [lineDensity,mul_div_assoc] using h).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hs] with t ht
    exact lineDensity_mul_eq (p := p) ht
  have hX (b : ℝ) : HasDerivAt (fun t => Real.exp (-t * b)) (-b * Real.exp (-s * b)) s := by
    convert (((hasDerivAt_id s).neg.mul_const b).exp) using 1
    simp only [Pi.neg_apply,id_eq]
    ring
  have hA : HasDerivAt polyA (s * Real.exp (-s)) s := by
    convert (((hasDerivAt_id s).const_add 1).mul ((hasDerivAt_id s).neg.exp)).const_sub 1 using 1
    simp only [id_eq,Pi.neg_apply,one_mul,mul_one]
    ring
  convert (((hP.mul (hX b)).mul hA).mul (BoseShape.C_deriv hs)) using 1
  unfold sharpGapDerivative
  simp only [Pi.mul_apply,show -(b * s) = -s * b by ring]
  rw [show -s * (b + 1) = -s * b + -s by ring,Real.exp_add]
  ring

private theorem sharpGapPrimitive_nonneg {p b s : ℝ} (hp : 0 < p) (hs : 0 < s) :
    0 ≤ sharpGapPrimitive p b s := by
  have := (polyA_pos hs).le
  have := (BoseShape.C_pos hs).le
  unfold sharpGapPrimitive lineDensity
  positivity

private theorem sharpGapPrimitive_le {p b s : ℝ} (hp : 0 < p) (hb : 0 ≤ b) (hs : 0 < s) :
    sharpGapPrimitive p b s ≤ (s ^ p / Real.Gamma p) * BoseShape.C s := by
  unfold sharpGapPrimitive
  rw [lineDensity_mul_eq hs]
  have hE : Real.exp (-s * b) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) hb)
  have hA : polyA s ≤ 1 := sub_le_self _ (by positivity)
  have h₀ : 0 ≤ s ^ p / Real.Gamma p := by positivity
  have h₁ := mul_le_of_le_one_right h₀ hE
  have h₂ := mul_le_mul h₁ hA (polyA_pos hs).le h₀
  rw [mul_one] at h₂
  exact mul_le_mul_of_nonneg_right h₂ (BoseShape.C_pos hs).le

private theorem sharpGapPrimitive_zero {p b : ℝ} (hp : 0 < p) (hb : 0 ≤ b) :
    Tendsto (sharpGapPrimitive p b) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hC : ContinuousAt (fun s : ℝ => s ^ p / Real.Gamma p) 0 :=
    (Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).div_const _
  have h := hC.tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  simp only [Real.zero_rpow hp.ne',zero_div] at h
  refine squeeze_zero' ?_ ?_ h
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact sharpGapPrimitive_nonneg hp hs
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hs₀ : 0 < s := hs
    exact (sharpGapPrimitive_le hp hb hs₀).trans (mul_le_of_le_one_right (by positivity)
      (BoseShape.C_lt_one hs₀).le)

private theorem sharpGapPrimitive_infinity {p b : ℝ} (hp : 0 < p) (hb : 0 ≤ b) :
    Tendsto (sharpGapPrimitive p b) atTop (𝓝 0) := by
  let A := BoseShape.decayConstant / Real.Gamma p
  have hA : 0 ≤ A := div_nonneg BoseShape.decayConstant_pos.le (Real.Gamma_pos_of_pos hp).le
  have h₀ := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p 1 zero_lt_one
  have h₁ := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p + 1) 1 zero_lt_one
  have h := (h₁.add h₀).const_mul A
  simp only [neg_one_mul,zero_add,mul_zero] at h
  refine squeeze_zero' ?_ ?_ h
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    exact sharpGapPrimitive_nonneg hp hs
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    refine (sharpGapPrimitive_le hp hb hs).trans
      (mul_le_mul_of_nonneg_left (BoseShape.C_le_decay hs) (by positivity)) |>.trans_eq ?_
    have hR : s ^ (p + 1) = s ^ p * s := Real.rpow_add_one hs.ne' p
    rw [hR]
    unfold A
    ring

theorem sharpGapDerivative_integral_zero {p b : ℝ} (hp : 0 < p) (hb : 0 ≤ b)
    (hI : IntegrableOn (sharpGapDerivative p b) (Ioi 0)) :
    (∫ s : ℝ in Ioi 0, sharpGapDerivative p b s) = 0 := by
  have h0 : sharpGapPrimitive p b 0 = 0 := by simp [sharpGapPrimitive]
  have hC : ContinuousWithinAt (sharpGapPrimitive p b) (Ici 0) 0 := by
    rw [← continuousWithinAt_Ioi_iff_Ici]
    change Tendsto (sharpGapPrimitive p b) (𝓝[>] 0) (𝓝 (sharpGapPrimitive p b 0))
    rw [h0]
    exact sharpGapPrimitive_zero hp hb
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hC
    (fun s hs => sharpGapPrimitive_deriv p b hs) hI (sharpGapPrimitive_infinity hp hb)
  rw [h0,sub_zero] at h
  exact h

end ACS12.GammaMeasure

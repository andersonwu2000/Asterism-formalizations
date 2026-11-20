import ACS12.JointRectangleSeeds
import ACS12.JointBoseMassMotion

/-! At zero gap the adjacent row pays the fourth-row mass curvature debit. -/
namespace ACS12.GammaMeasure

open Set MeasureTheory Filter CenteredCircle.AllN
open GammaDeficit (lineDensity)

private theorem pureMassKernel_scaled {p m : ℝ} (hm : 0 < m) (K : ℝ → ℝ) :
    (∫ s : ℝ in Ioi 0, lineDensity p s * s * K (m * s)) =
      m ^ (-p - 1) * ∫ s : ℝ in Ioi 0, lineDensity p s * s * K s := by
  let F (s : ℝ) := lineDensity p s * s * K s
  have he (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      lineDensity p s * s * K (m * s) = m ^ (-p) * F (s * m) := by
    have hρ : lineDensity p (m * s) = m ^ (p - 1) * lineDensity p s := by
      unfold lineDensity
      rw [Real.mul_rpow hm.le (show 0 < s from hs).le]
      ring
    have hPow : m ^ (-p) * m ^ (p - 1) * m = 1 := by
      rw [← Real.rpow_add hm,show -p + (p - 1) = -1 by ring,Real.rpow_neg_one,inv_mul_cancel₀ hm.ne']
    unfold F
    rw [mul_comm s m,hρ]
    linear_combination lineDensity p s * s * K (m * s) * (-hPow)
  rw [setIntegral_congr_fun measurableSet_Ioi he,integral_const_mul,integral_comp_mul_right_Ioi F 0 hm,
    zero_mul,smul_eq_mul,← mul_assoc,← div_eq_mul_inv,← Real.rpow_sub_one hm.ne']

private theorem adjacentMass_head_eq {p L u m : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hL : 0 < L)
    (hu : 0 < u) (hm : 0 < m) :
    samplingHead (lawPeanoKernel p L 0 u .a) m m =
      ∫ s : ℝ in Ioi 0, lawPeanoDensity p L 0 u .a s * scaledExpTail s m := by
  rw [(lawPeanoHead_sampling hp hp₂ hL (by norm_num : (0 : ℝ) ∈ Icc 0 1) hu hm hm .a).2]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  have hS : Real.exp (-s * m) * (m + scaledExpTail s m) = scaledExpTail s m := by
    unfold scaledExpTail
    rw [show -s * m = -(s * m) by ring,Real.exp_neg]
    field_simp [Real.exp_ne_zero _,(expTail_den_pos (mul_pos (show 0 < s from hs) hm)).ne']
    ring
  dsimp only
  rw [mul_assoc,hS]

theorem adjacentDiagonal_convex_paid {p L u : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) (hL : 0 < L)
    (huL : 7 / 8 ≤ u) :
    ConvexOn ℝ (Icc (2 * u - 1) u) (fun m =>
      jointPureLambda * adjacentSourceLaw p L 0 u m m m -
        jointCanonicalMu * (pureZ p - 1) * m ^ (1 - p)) := by
  let J := Icc (2 * u - 1) u
  let g (s : ℝ) := lawPeanoDensity p L 0 u .a s
  let A := jointPureLambda
  let B := jointCanonicalMu * (pureZ p - 1)
  let U := u * lawMoment p L 0 1 u + lawMoment p L 0 0 u + lawSelf p L 0
  let f (m : ℝ) := A * adjacentSourceLaw p L 0 u m m m - B * m ^ (1 - p)
  let f' (m : ℝ) := A * (-U - ∫ s : ℝ in Ioi 0, g s * BoseShape.C (s * m)) -
    B * ((1 - p) * m ^ (-p))
  let f'' (m : ℝ) := A * (∫ s : ℝ in Ioi 0, g s * (s * (-BoseShape.C₁ (s * m)))) -
    B * (p * (p - 1) * m ^ (-p - 1))
  have hu : 0 < u := (by norm_num : (0 : ℝ) < 7 / 8).trans_le huL
  have hp₀ := zero_lt_one.trans_le hp
  have hp₂ := hP.trans (by norm_num : (9 / 5 : ℝ) ≤ 2)
  have hθ : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have hg : Measurable g := lawPeanoDensity_measurable hp₀ hL .a
  obtain ⟨M,hM,hG⟩ := lawPeanoDensity_quadratic_bound hp hp₂ hL hθ hu .a
  have hgB (s : ℝ) (hs : 0 < s) : |g s| ≤ M * (s + s ^ 2) :=
    (hG s hs).trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hs.le) hM)
  have hD₁ (m : ℝ) (hm : 0 < m) : HasDerivAt f (f' m) m := by
    have hT := (boseStream_derivative hg hgB hm).2
    have hF := (((hasDerivAt_id m).const_mul (-U)).add hT).const_mul A
    have hP' := ((hasDerivAt_id m).rpow_const (p := 1 - p) (Or.inl hm.ne')).const_mul B
    have hE := hF.sub hP'
    have hDer : HasDerivAt (fun x => A * (-(U * x) + ∫ s : ℝ in Ioi 0, g s * scaledExpTail s x) -
        B * x ^ (1 - p)) (f' m) m := by
      convert hE using 1
      · funext x
        simp only [Pi.add_apply,Pi.sub_apply,Function.comp_apply,id_eq]
        ring
      · unfold f'
        simp only [id_eq,mul_one,show 1 - p - 1 = -p by ring]
        ring
    let C := A * (samplingTail (lawPeanoKernel p L 0 u .b) 0 1 +
      u * (lawMoment p L 0 0 u + lawSelf p L 0))
    apply (hDer.add_const C).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hm] with x hx
    unfold f adjacentSourceLaw C U
    rw [adjacentMass_head_eq hp hp₂ hL hu hx]
    ring
  have hD₂ (m : ℝ) (hm : 0 < m) : HasDerivAt f' (f'' m) m := by
    have hT := (boseStream_second hg hgB hm).2
    have hF := (hT.const_add (-U)).const_mul A
    have hP' := (((hasDerivAt_id m).rpow_const (p := -p) (Or.inl hm.ne')).const_mul (1 - p)).const_mul B
    convert hF.sub hP' using 1
    unfold f''
    simp only [id_eq,mul_one,one_mul]
    ring
  have hPos (m : ℝ) (hm : m ∈ J) : 0 < m := by linarith only [hm.1,huL]
  change ConvexOn ℝ J f
  apply convexOn_of_hasDerivWithinAt2_nonneg (D := J) (f' := f') (f'' := f'') (convex_Icc _ _)
    (fun m hm => (hD₁ m (hPos m hm)).continuousAt.continuousWithinAt)
    (fun m hm => (hD₁ m (hPos m (interior_subset hm))).hasDerivWithinAt)
    (fun m hm => (hD₂ m (hPos m (interior_subset hm))).hasDerivWithinAt)
  intro m hm'
  have hmJ : m ∈ J := interior_subset hm'
  have hm := hPos m hmJ
  let K (s : ℝ) := polyA s * (-BoseShape.C₁ s)
  have hI : IntegrableOn (fun s => g s * (s * (-BoseShape.C₁ (s * m)))) (Ioi 0) :=
    (boseStream_second hg hgB hm).1
  let F (s : ℝ) := lineDensity p s * s * K (m * s)
  let V (s : ℝ) := lawPeanoDensity p L 0 m .a s
  have hV : Measurable V := lawPeanoDensity_measurable hp₀ hL .a
  obtain ⟨N,hN,hB⟩ := lawPeanoDensity_quadratic_bound hp hp₂ hL hθ hm .a
  have hFI : IntegrableOn F (Ioi 0) := by
    apply ((boseStream_second hV (fun s hs => (hB s hs).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hs.le) hN)) hm).1).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    unfold F K V lawPeanoDensity
    simp only [lawDensity,sub_zero,one_mul,zero_mul,add_zero,densityPolynomial]
    rw [mul_comm s m]
    ring
  have hTop : m ^ (-p - 1) * jointGapKp p ≤
      ∫ s : ℝ in Ioi 0, g s * (s * (-BoseShape.C₁ (s * m))) := by
    have hh := setIntegral_mono_on hFI hI measurableSet_Ioi ?_
    · rw [pureMassKernel_scaled hm K] at hh
      have hK : (∫ s : ℝ in Ioi 0, lineDensity p s * s * K s) = jointGapKp p := by
        unfold jointGapKp
        apply setIntegral_congr_fun measurableSet_Ioi
        intro s _
        unfold K
        ring
      rwa [hK] at hh
    · intro s hs
      have hs₀ : 0 < s := hs
      have hA := polyA_monotone_nonneg (mul_pos hm hs₀).le (mul_pos hu hs₀).le
        (mul_le_mul_of_nonneg_right hmJ.2 hs₀.le)
      have hC := mul_le_mul_of_nonneg_right hA (neg_nonneg.mpr (BoseShape.C₁_neg (mul_pos hm hs₀)).le)
      have h := mul_le_mul_of_nonneg_left hC (mul_nonneg (lineDensity_pos hp₀ hs₀).le hs₀.le)
      unfold g F K lawPeanoDensity
      simp only [lawDensity,sub_zero,one_mul,zero_mul,add_zero,densityPolynomial]
      rw [mul_comm s m]
      linarith only [h]
  have hZ : 0 ≤ pureZ p - 1 := by linarith only [(pureZ_band_bounds hp hP).1,hp]
  have hZu : pureZ p - 1 ≤ 1245 / 1000 := by linarith only [(pureZ_band_bounds hp hP).2,hP]
  have hPrice : B * (p - 1) ≤ A * (7 / 10) := by
    have hZp := mul_le_mul hZu (show p - 1 ≤ 4 / 5 by linarith only [hP]) (sub_nonneg.mpr hp)
      (by norm_num : (0 : ℝ) ≤ 1245 / 1000)
    have hC := mul_le_mul jointCanonicalMu_bounds.2.le hZp (mul_nonneg hZ (sub_nonneg.mpr hp))
      (by norm_num : (0 : ℝ) ≤ 17765 / 1000000)
    unfold A B jointPureLambda
    nlinarith only [hC]
  have hPwr : 0 ≤ m ^ (-p - 1) := Real.rpow_nonneg hm.le _
  have hK := mul_le_mul_of_nonneg_left (jointGapKp_lower hp).le hPwr
  have hA : 0 ≤ A := by norm_num [A,jointPureLambda]
  have hT := mul_le_mul_of_nonneg_left (show m ^ (-p - 1) * ((7 / 10) * p) ≤
      ∫ s : ℝ in Ioi 0, g s * (s * (-BoseShape.C₁ (s * m))) by nlinarith only [hK,hTop]) hA
  have hFinal := mul_le_mul_of_nonneg_right hPrice (mul_nonneg hp₀.le hPwr)
  unfold f''
  change 0 ≤ A * (∫ s : ℝ in Ioi 0, g s * (s * (-BoseShape.C₁ (s * m)))) - _
  nlinarith only [hT,hFinal]

end ACS12.GammaMeasure

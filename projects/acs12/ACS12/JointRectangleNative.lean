import ACS12.JointRectangleSeeds
import ACS12.JointBoseMassMotion
import ACS12.AdjacentReturnDensity

/-! Convexity of the complete signed native value at the physical source masses. -/
namespace ACS12.GammaMeasure

open Set MeasureTheory Filter CenteredCircle.AllN
open GammaDeficit (lineDensity)

private theorem positive_monotone_product {W Q R : ℝ → ℝ}
    (hW : IntegrableOn W (Ioi 0))
    (hQ : IntegrableOn (fun s => W s * Q s) (Ioi 0))
    (hR : IntegrableOn (fun s => W s * R s) (Ioi 0))
    (hP : IntegrableOn (fun s => W s * Q s * R s) (Ioi 0))
    (hW₀ : ∀ s > 0, 0 < W s) (hR₀ : ∀ s > 0, 0 < R s)
    (hQM : MonotoneOn Q (Ioi 0)) (hRM : MonotoneOn R (Ioi 0))
    (hSeed : 0 < ∫ s : ℝ in Ioi 0, W s * Q s) :
    0 < ∫ s : ℝ in Ioi 0, W s * Q s * R s := by
  have hC := integral_product_comparison hP hW hQ hR (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hE : W x * Q x * R x * W y + W y * Q y * R y * W x -
        W x * Q x * (W y * R y) - W y * Q y * (W x * R x) =
        (W x * W y) * ((Q x - Q y) * (R x - R y)) := by ring
    rw [hE]
    apply mul_nonneg (mul_nonneg (hW₀ x hx).le (hW₀ y hy).le)
    rcases le_total x y with hxy | hyx
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hQM hx hy hxy)) (sub_nonpos.mpr (hRM hx hy hxy))
    · exact mul_nonneg (sub_nonneg.mpr (hQM hy hx hyx)) (sub_nonneg.mpr (hRM hy hx hyx)))
  let μ := volume.restrict (Ioi (0 : ℝ))
  letI : NeZero μ := ⟨positiveHalfLine_ne_zero⟩
  have hRpos : 0 < ∫ s : ℝ in Ioi 0, W s * R s := by
    have h := integral_strict_of_ae_lt μ (integrable_zero ℝ ℝ _) hR ?_
    · simpa only [μ,integral_zero] using h
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact mul_pos (hW₀ s hs) (hR₀ s hs)
  exact pos_of_mul_pos_left ((mul_pos hSeed hRpos).trans_le hC) (integral_nonneg_of_ae (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hW₀ s hs).le))

theorem adjacentSignedValue_mass_convex {p L u : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hL : 0 < L) (huL : 7 / 8 ≤ u) (hu₁ : u ≤ 1) :
    ConvexOn ℝ (Icc (2 * u - 1) u) (adjacentLawSignedValue p L 0 u) := by
  let J := Icc (2 * u - 1) u
  let g (s : ℝ) := lawRightDensity p L 0 u s * Real.exp (-s * u)
  let g₀ (s : ℝ) := lineDensity p s * s * Real.exp (-s * u)
  let Q := rightMultiplier (middleA u) (middleZ u)
  let f' (m : ℝ) := lawRightTest p L 0 u u - ∫ s : ℝ in Ioi 0, g s * BoseShape.C (s * m)
  let f'' (m : ℝ) := ∫ s : ℝ in Ioi 0, g s * (s * (-BoseShape.C₁ (s * m)))
  have hp₂ : p ≤ 2 := hP.trans (by norm_num)
  have hp₀ := zero_lt_one.trans_le hp
  have hu : 0 < u := (by norm_num : (0 : ℝ) < 7 / 8).trans_le huL
  have hθ : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have hgm : Measurable g := (lawRightDensity_measurable hp₀ hL).mul (by fun_prop)
  obtain ⟨B,hB,hBound⟩ := lawRightDensity_bound (u := u) hp hp₂ hL hθ
  have hgB (s : ℝ) (hs : 0 < s) : |g s| ≤ B * (s + s ^ 2) := by
    unfold g
    rw [abs_mul,abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul (hBound s hs) (Real.exp_le_one_iff.mpr (by
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) hu.le))
      (Real.exp_pos _).le (by positivity)).trans_eq (mul_one _)
  have hD₁ (m : ℝ) (hm : 0 < m) : HasDerivAt (adjacentLawSignedValue p L 0 u) (f' m) m := by
    have hT := (boseStream_derivative hgm hgB hm).2
    have h := (((hasDerivAt_id m).mul_const (lawRightTest p L 0 u u)).const_add
      (middleLawBase p L 0 u)).add hT
    have h' : HasDerivAt (fun x => middleLawBase p L 0 u + x * lawRightTest p L 0 u u +
        ∫ s : ℝ in Ioi 0, g s * scaledExpTail s x) (f' m) m := by
      convert h using 1
      simp only [f',one_mul,sub_eq_add_neg]
    apply h'.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hm] with x hx
    exact congrArg (fun v => middleLawBase p L 0 u + x * lawRightTest p L 0 u u + v)
      (lawRightTail_sampling hp hp₂ hL hθ hu.le hx).2
  have hD₂ (m : ℝ) (hm : 0 < m) : HasDerivAt f' (f'' m) m := by
    simpa only [f',f'',sub_eq_add_neg] using ((boseStream_second hgm hgB hm).2).const_add (lawRightTest p L 0 u u)
  have hM (m : ℝ) (hm : m ∈ J) : 0 < m := by linarith only [hm.1,huL]
  change ConvexOn ℝ J _
  apply convexOn_of_hasDerivWithinAt2_nonneg (D := J) (f' := f') (f'' := f'') (convex_Icc _ _)
    (fun m hm => (hD₁ m (hM m hm)).continuousAt.continuousWithinAt)
    (fun m hm => (hD₁ m (hM m (interior_subset hm))).hasDerivWithinAt)
    (fun m hm => (hD₂ m (hM m (interior_subset hm))).hasDerivWithinAt)
  intro m hm
  have hmJ : m ∈ J := interior_subset hm
  have hm₀ := hM m hmJ
  let W (s : ℝ) := lineDensity p s * s * Real.exp (-s * (u + m))
  let R (s : ℝ) := s * BoseShape.curvatureHeat (s * m)
  have hW : IntegrableOn W (Ioi 0) := by simpa only [W,pow_one] using
    (lineDensity_moment hp₀ (add_pos hu hm₀) 1).1
  have hQ₁ (s : ℝ) (hs : 0 < s) : W s * Q s = lawRightDensity p L 0 u s * Real.exp (-s * (u + m)) := by
    unfold W Q lawRightDensity
    rw [middleRightDensity_eq hs]
    simp only [lawDensity,sub_zero,one_mul,zero_mul,add_zero]
    ring
  have hQ : IntegrableOn (fun s => W s * Q s) (Ioi 0) := by
    apply (lawRightDensity_integrable hp hp₂ hL hθ (u := u) (add_pos hu hm₀)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hQ₁ s hs).symm
  have hSeed : 0 < ∫ s : ℝ in Ioi 0, W s * Q s := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun s hs => hQ₁ s hs)]
    change 0 < lawRightTest p L 0 u (u + m)
    rw [lawRightTest_zero hp hp₂ hL (add_pos hu hm₀)]
    exact jointNative_seed_pos hp hP huL hu₁ hmJ.1 hmJ.2
  have hK (s : ℝ) : Real.exp (-s * (u + m)) * Real.exp (s * m) = Real.exp (-s * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hR₁ (s : ℝ) : W s * R s = g₀ s * (s * (-BoseShape.C₁ (s * m))) := by
    unfold W R g₀ BoseShape.curvatureHeat
    linear_combination -(lineDensity p s * s ^ 2 * BoseShape.C₁ (s * m)) * hK s
  have hR₂ (s : ℝ) (hs : 0 < s) : W s * Q s * R s = g s * (s * (-BoseShape.C₁ (s * m))) := by
    rw [hQ₁ s hs]
    unfold R g BoseShape.curvatureHeat
    linear_combination -(lawRightDensity p L 0 u s * s * BoseShape.C₁ (s * m)) * hK s
  obtain ⟨C,hC,hCbound⟩ := lawDensity_linear_envelope hp hp₂ hL hθ
  have hMeas : Measurable g₀ := by unfold g₀ lineDensity; fun_prop
  have hC' (s : ℝ) (hs : 0 < s) : |g₀ s| ≤ C * (s + s ^ 2) := by
    have hI := hCbound s hs
    simp only [lawDensity,sub_zero,one_mul,zero_mul,add_zero] at hI
    have hExp : Real.exp (-s * u) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) hu.le)
    have hX := mul_le_mul (mul_le_mul_of_nonneg_right hI hs.le) hExp (Real.exp_pos _).le (by positivity)
    unfold g₀
    rw [abs_mul,abs_mul,abs_of_pos hs,abs_of_pos (Real.exp_pos _)]
    exact hX.trans_eq (by ring)
  have hR : IntegrableOn (fun s => W s * R s) (Ioi 0) :=
    (boseStream_second hMeas hC' hm₀).1.congr (Eventually.of_forall (fun s => (hR₁ s).symm))
  have hP' : IntegrableOn (fun s => W s * Q s * R s) (Ioi 0) := by
    apply (boseStream_second hgm hgB hm₀).1.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hR₂ s hs).symm
  have hW₀ (s : ℝ) (hs : 0 < s) : 0 < W s := mul_pos (mul_pos (lineDensity_pos hp₀ hs) hs) (Real.exp_pos _)
  have hR₀ (s : ℝ) (hs : 0 < s) : 0 < R s := mul_pos hs (BoseShape.curvatureHeat_pos (mul_pos hs hm₀))
  have hRM : MonotoneOn R (Ioi 0) := by
    intro x hx y hy hxy
    exact mul_le_mul hxy
      (BoseShape.curvatureHeat_mono (mul_pos (show 0 < x from hx) hm₀) (mul_pos (show 0 < y from hy) hm₀)
        (mul_le_mul_of_nonneg_right hxy hm₀.le))
      (BoseShape.curvatureHeat_pos (mul_pos (show 0 < x from hx) hm₀)).le (show 0 < y from hy).le
  have h := positive_monotone_product hW hQ hR hP' hW₀ hR₀
    (rightMultiplier_mono ((middleA_le u).trans (by norm_num))) hRM hSeed
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s hs => hR₂ s hs)] at h
  exact h.le

end ACS12.GammaMeasure

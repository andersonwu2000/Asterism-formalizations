import ACS12.GammaLogExact

/-! The exponent concavity of the full logarithmic contrast. -/

namespace ACS12.GammaMeasure

open MeasureTheory Set Filter
open scoped Topology

private noncomputable def shiftedProfile (W : ℝ → ℝ) (q t : ℝ) : ℝ :=
  evenGammaProfile t * Real.exp (-(q - 1 / 2) * t) * W t

private noncomputable def shiftedIntegral (W : ℝ → ℝ) (q : ℝ) : ℝ :=
  ∫ t : ℝ in Ioi 0, shiftedProfile W q t

private theorem shiftedProfile_measurable {W : ℝ → ℝ} (hW : Measurable W) (q : ℝ) :
    Measurable (shiftedProfile W q) := by
  have hE : Measurable evenGammaProfile :=
    (continuous_const.mul ((continuous_gammaDensity (by norm_num : 0 < (2 : ℝ))).comp
      (by fun_prop))).measurable
  unfold shiftedProfile
  exact (hE.mul (by fun_prop)).mul hW

private theorem shiftedProfile_bound {W : ℝ → ℝ} {C q : ℝ} (hq : 1 / 2 ≤ q)
    (hB : ∀ t > 0, |W t| ≤ C) {t : ℝ} (ht : 0 < t) :
    ‖shiftedProfile W q t‖ ≤ C * evenGammaProfile t := by
  have hE : Real.exp (-(q - 1 / 2) * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) ht.le)
  rw [shiftedProfile, norm_mul, norm_mul, Real.norm_eq_abs (W t),
    Real.norm_of_nonneg (evenGammaProfile_pos t).le, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ evenGammaProfile t * |W t| := mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right (evenGammaProfile_pos t).le hE) (abs_nonneg _)
    _ ≤ _ := by rw [mul_comm C]; exact mul_le_mul_of_nonneg_left (hB t ht) (evenGammaProfile_pos t).le

private theorem shiftedProfile_integrable {W : ℝ → ℝ} (hW : Measurable W) {C q : ℝ}
    (hB : ∀ t > 0, |W t| ≤ C) (hq : 1 / 2 ≤ q) :
    IntegrableOn (shiftedProfile W q) (Ioi 0) := by
  refine (evenGammaProfile_integrable.integrableOn.const_mul C).mono'
    (shiftedProfile_measurable hW q).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact shiftedProfile_bound hq hB ht

private theorem continuousOn_shiftedIntegral {W : ℝ → ℝ} (hW : Measurable W)
    {C : ℝ} (hB : ∀ t > 0, |W t| ≤ C) : ContinuousOn (shiftedIntegral W) (Ici (1 / 2)) := by
  intro q hq
  unfold shiftedIntegral
  apply tendsto_integral_filter_of_dominated_convergence (fun t => C * evenGammaProfile t)
  · exact Eventually.of_forall fun r => (shiftedProfile_measurable hW r).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with r hr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact shiftedProfile_bound hr hB ht
  · exact evenGammaProfile_integrable.integrableOn.const_mul C
  · exact Eventually.of_forall fun t => by
      have h : Continuous (fun r : ℝ => shiftedProfile W r t) := by unfold shiftedProfile; fun_prop
      exact h.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

private theorem hasDerivAt_shiftedIntegral {W : ℝ → ℝ} (hW : Measurable W)
    {C C' : ℝ} (hB : ∀ t > 0, |W t| ≤ C) (hB' : ∀ t > 0, |-t * W t| ≤ C')
    {q : ℝ} (hq : 1 / 2 < q) :
    HasDerivAt (shiftedIntegral W) (shiftedIntegral (fun t => -t * W t) q) q := by
  let W' (t : ℝ) := -t * W t
  have hW' : Measurable W' := measurable_id.neg.mul hW
  have hD : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), ∀ r ∈ Ioi (1 / 2 : ℝ),
      HasDerivAt (fun r => shiftedProfile W r t) (shiftedProfile W' r t) r := by
    exact Eventually.of_forall fun t r _ => by
      have hArg : HasDerivAt (fun x : ℝ => -(x - 1 / 2) * t) (-t) r := by
        simpa only [id_eq, neg_one_mul] using
          (((hasDerivAt_id r).sub_const (1 / 2 : ℝ)).neg.mul_const t)
      have h := (hArg.exp.const_mul (evenGammaProfile t)).mul_const (W t)
      convert h using 1
      dsimp only [shiftedProfile, W']
      ring
  have hBound : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), ∀ r ∈ Ioi (1 / 2 : ℝ),
      ‖shiftedProfile W' r t‖ ≤ C' * evenGammaProfile t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact fun r hr => shiftedProfile_bound (mem_Ioi.mp hr).le hB' ht
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ))) (Ioi_mem_nhds hq)
    (Eventually.of_forall fun r => (shiftedProfile_measurable hW r).aestronglyMeasurable)
    (shiftedProfile_integrable hW hB hq.le)
    (shiftedProfile_measurable hW' q).aestronglyMeasurable hBound
    (evenGammaProfile_integrable.integrableOn.const_mul C') hD).2

private theorem norm_cos_sub_cos_le_two (x y : ℝ) : |Real.cos x - Real.cos y| ≤ 2 := by
  exact (abs_sub _ _).trans (by linarith [Real.abs_cos_le_one x, Real.abs_cos_le_one y])

theorem gammaLogContrast_concave_all {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    ConcaveOn ℝ (Ici (1 / 2)) (fun q => gammaLogContrast q x y) := by
  let W (t : ℝ) := (Real.cos (y * t) - Real.cos (x * t)) / t ^ 2
  let W₁ (t : ℝ) := -t * W t
  let W₂ (t : ℝ) := -t * W₁ t
  have hW : Measurable W := by unfold W; fun_prop
  have hW₁ : Measurable W₁ := measurable_id.neg.mul hW
  have hW₀ (t : ℝ) (ht : 0 < t) : |W t| ≤ (x ^ 2 + y ^ 2) / 2 := by
    have h := norm_logContrastIntegrand_le (q := 1 / 2) le_rfl x y ht
    change ‖evenGammaProfile t * Real.exp (-((1 / 2 : ℝ) - 1 / 2) * t) * W t‖ ≤ _ at h
    simp only [sub_self, neg_zero, zero_mul, Real.exp_zero, mul_one, norm_mul,
      Real.norm_of_nonneg (evenGammaProfile_pos t).le, Real.norm_eq_abs (W t)] at h
    exact (mul_le_mul_iff_right₀ (evenGammaProfile_pos t)).mp (h.trans_eq (mul_comm _ _))
  have hW₁B (t : ℝ) (ht : 0 < t) : |W₁ t| ≤ |y - x| := by
    have h : W₁ t = -(Real.cos (y * t) - Real.cos (x * t)) / t := by
      dsimp [W₁, W]
      field_simp [ht.ne']
    rw [h, abs_div, abs_neg, abs_of_pos ht, div_le_iff₀ ht]
    have h := Real.abs_cos_sub_cos_le (y * t) (x * t)
    rw [← sub_mul, abs_mul, abs_of_pos ht] at h
    exact h
  have hW₂E (t : ℝ) (ht : 0 < t) : W₂ t = Real.cos (y * t) - Real.cos (x * t) := by
    dsimp [W₂, W₁, W]
    field_simp [ht.ne']
  have hW₂B (t : ℝ) (ht : 0 < t) : |W₂ t| ≤ 2 := by rw [hW₂E t ht]; exact norm_cos_sub_cos_le_two _ _
  have hI (q : ℝ) (hq : 1 / 2 ≤ q) : gammaLogContrast q x y = shiftedIntegral W q :=
    gammaLogContrast_eq_integral hq x y
  have h₁ (q : ℝ) (hq : 1 / 2 < q) :
      HasDerivAt (fun q => gammaLogContrast q x y) (shiftedIntegral W₁ q) q := by
    apply (hasDerivAt_shiftedIntegral hW hW₀ hW₁B hq).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hq] with r hr
    exact hI r (mem_Ioi.mp hr).le
  have h₂ (q : ℝ) (hq : 1 / 2 < q) :
      HasDerivAt (deriv (fun q => gammaLogContrast q x y)) (shiftedIntegral W₂ q) q := by
    apply (hasDerivAt_shiftedIntegral hW₁ hW₁B hW₂B hq).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hq] with r hr
    exact (h₁ r hr).deriv
  have hSign (q : ℝ) (hq : 1 / 2 < q) : shiftedIntegral W₂ q ≤ 0 := by
    have hX := shiftedProfile_integrable (W := fun t => Real.cos (x * t)) (by fun_prop)
      (fun t _ => Real.abs_cos_le_one (x * t)) hq.le
    have hY := shiftedProfile_integrable (W := fun t => Real.cos (y * t)) (by fun_prop)
      (fun t _ => Real.abs_cos_le_one (y * t)) hq.le
    unfold shiftedIntegral
    calc
      _ = ∫ t : ℝ in Ioi 0,
          shiftedProfile (fun t => Real.cos (y * t)) q t -
            shiftedProfile (fun t => Real.cos (x * t)) q t := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        rw [shiftedProfile, hW₂E t ht]
        simp only [shiftedProfile, mul_sub]
      _ = (∫ t : ℝ in Ioi 0, shiftedProfile (fun t => Real.cos (y * t)) q t) -
          ∫ t : ℝ in Ioi 0, shiftedProfile (fun t => Real.cos (x * t)) q t :=
        integral_sub hY hX
      _ ≤ _ := by
        simp only [shiftedProfile, gammaCosine_moment hq]
        have h := smoothedEvenGamma_antitone (sub_pos.mpr hq) hx (hx.trans hxy) hxy
        linarith
  apply concaveOn_of_deriv2_nonpos (convex_Ici _)
  · exact (continuousOn_shiftedIntegral hW hW₀).congr (fun q hq => hI q hq)
  · intro q hq
    rw [interior_Ici] at hq
    exact (h₁ q hq).differentiableAt.differentiableWithinAt
  · intro q hq
    rw [interior_Ici] at hq
    exact (h₂ q hq).differentiableAt.differentiableWithinAt
  · intro q hq
    rw [interior_Ici] at hq
    change deriv (deriv (fun q => gammaLogContrast q x y)) q ≤ 0
    rw [(h₂ q hq).deriv]
    exact hSign q hq

theorem gammaLogContrast_concave {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    ConcaveOn ℝ (Icc (1 / 2) 1) (fun q => gammaLogContrast q x y) :=
  (gammaLogContrast_concave_all hx hxy).subset (fun _ h => h.1) (convex_Icc _ _)

end ACS12.GammaMeasure

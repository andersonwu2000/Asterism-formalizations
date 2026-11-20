import ACS12.GammaLikelihood

/-! The ordered Gamma likelihood approaches one at high frequency.
The normalization follows from the exact finite-period Abel boundary. -/

namespace ACS12.GammaMeasure

open MeasureTheory Set Filter
open scoped Topology
open GammaDeficit (lineDensity lineDensity_exp_integrable lineDensity_exp_integral)

theorem lineDensity_pos {p s : ℝ} (hp : 0 < p) (hs : 0 < s) : 0 < lineDensity p s :=
  div_pos (Real.rpow_pos_of_pos hs _) (Real.Gamma_pos_of_pos hp)

private theorem scaled_deficit_tendsto_zero {p L : ℝ} (hp : 0 < p) (hp₂ : p < 2) (hL : 0 < L) :
    Tendsto (fun t : ℝ => t ^ p * (t ^ (-p) - imagePotential p L t)) (𝓝[>] 0) (𝓝 0) := by
  have ht := (Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have h := ht.mul (tendsto_line_sub_imagePotential_of_lt_two hp hp₂ hL)
  simpa only [Real.zero_rpow hp.ne', zero_mul] using h

private theorem line_power_mul {p t : ℝ} (ht : 0 < t) : t ^ p * t ^ (-p) = 1 := by
  rw [← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero]

private theorem eventual_density_lower_impossible {p L c s₀ : ℝ} (hp : 0 < p) (hp₂ : p < 2)
    (hL : 0 < L) (hc : 1 < c) (hs₀ : 0 < s₀)
    (hLower : ∀ s ≥ s₀, c * lineDensity p s ≤ imageDensity p L s) : False := by
  let M := ∫ s : ℝ in Ioo 0 s₀, c * lineDensity p s
  have hM : IntegrableOn (fun s : ℝ => c * lineDensity p s) (Ioo 0 s₀) :=
    ((((intervalIntegral.integrableOn_Ioo_rpow_iff hs₀).mpr
      (show -1 < p - 1 by linarith)).div_const (Real.Gamma p)).const_mul c)
  have hBound (t : ℝ) (ht : 0 < t) :
      c * t ^ (-p) - imagePotential p L t ≤ M := by
    let f (s : ℝ) := c * (lineDensity p s * Real.exp (-s * t)) -
      imageDensity p L s * Real.exp (-s * t)
    have hLine := (lineDensity_exp_integrable hp ht).const_mul c
    have hImage := imagePotential_integrable hp hL ht
    have hI : IntegrableOn f (Ioi 0) := hLine.sub hImage
    have hInt : (∫ s : ℝ in Ioi 0, f s) = c * t ^ (-p) - imagePotential p L t := by
      calc
        _ = (∫ s : ℝ in Ioi 0, c * (lineDensity p s * Real.exp (-s * t))) -
            ∫ s : ℝ in Ioi 0, imageDensity p L s * Real.exp (-s * t) :=
          integral_sub hLine hImage
        _ = _ := by rw [integral_const_mul, lineDensity_exp_integral hp ht, imagePotential]
    have hTailSub : Ici s₀ ⊆ Ioi (0 : ℝ) := fun s hs => hs₀.trans_le hs
    have hHeadSub : Ioo (0 : ℝ) s₀ ⊆ Ioi 0 := fun _ hs => hs.1
    have hUnion : Ioo (0 : ℝ) s₀ ∪ Ici s₀ = Ioi 0 := by
      ext s
      constructor
      · exact fun h => h.elim (hHeadSub ·) (hTailSub ·)
      · intro hs
        rcases lt_or_ge s s₀ with h | h
        · exact Or.inl ⟨hs, h⟩
        · exact Or.inr h
    have hDisj : Disjoint (Ioo (0 : ℝ) s₀) (Ici s₀) :=
      Set.disjoint_left.mpr fun s hs hs' => (not_lt_of_ge hs') hs.2
    have hSplit := setIntegral_union hDisj measurableSet_Ici (hI.mono_set hHeadSub) (hI.mono_set hTailSub)
    rw [hUnion, hInt] at hSplit
    have hTail : (∫ s : ℝ in Ici s₀, f s) ≤ 0 := by
      apply integral_nonpos_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
      dsimp only [f]
      rw [← mul_assoc, ← sub_mul]
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hLower s hs)) (Real.exp_pos _).le
    have hHead : (∫ s : ℝ in Ioo 0 s₀, f s) ≤ M := by
      apply integral_mono_ae (hI.mono_set hHeadSub) hM
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      dsimp only [f]
      have hExp : Real.exp (-s * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hs.1])
      have hρ : 0 ≤ c * lineDensity p s := mul_nonneg (by linarith) (lineDensity_pos hp hs.1).le
      have hW := mul_nonneg (imageDensity_pos hp hL hs.1).le (Real.exp_pos (-s * t)).le
      linarith [mul_le_of_le_one_right hρ hExp]
    linarith
  have hLim := (scaled_deficit_tendsto_zero hp hp₂ hL).add_const (c - 1)
  have hR := ((Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)).mul_const M
  have hContr : c - 1 ≤ 0 := by
    simp only [zero_add] at hLim
    simp only [Real.zero_rpow hp.ne', zero_mul] at hR
    apply le_of_tendsto_of_tendsto hLim hR
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht₀ : 0 < t := ht
    have h := mul_le_mul_of_nonneg_left (hBound t ht₀) (Real.rpow_pos_of_pos ht₀ p).le
    have hEq : t ^ p * (c * t ^ (-p) - imagePotential p L t) =
        t ^ p * (t ^ (-p) - imagePotential p L t) + (c - 1) := by
      ring_nf
      have hP := line_power_mul (p := p) ht₀
      linear_combination (c - 1) * hP
    rwa [hEq] at h
  linarith

theorem imageDensity_lt_lineDensity {p L s : ℝ} (hp : 1 ≤ p) (hp₂ : p < 2)
    (hL : 0 < L) (hs : 0 < s) :
    imageDensity p L s < lineDensity p s := by
  have hp₀ : 0 < p := zero_lt_one.trans_le hp
  let r (t : ℝ) := imageDensity p L t / lineDensity p t
  have hMono : StrictMonoOn r (Ioi 0) := imageDensity_div_lineDensity_strictMono hp hp₂ hL
  by_contra! h
  have h₁ : 1 ≤ r s := (le_div_iff₀ (lineDensity_pos hp₀ hs)).mpr (by simpa using h)
  let t := s + 1
  have ht : 0 < t := by dsimp [t]; positivity
  have hst : s < t := by dsimp [t]; linarith
  have hc : 1 < r t := h₁.trans_lt (hMono hs ht hst)
  apply eventual_density_lower_impossible hp₀ hp₂ hL hc ht
  intro u hu
  have hU : 0 < u := ht.trans_le hu
  exact (le_div_iff₀ (lineDensity_pos hp₀ hU)).mp (hMono.monotoneOn ht hU hu)

theorem imageDensity_div_lineDensity_tendsto_one {p L : ℝ} (hp : 1 ≤ p) (hp₂ : p < 2)
    (hL : 0 < L) :
    Tendsto (fun s => imageDensity p L s / lineDensity p s) atTop (𝓝 1) := by
  let r (s : ℝ) := imageDensity p L s / lineDensity p s
  have hp₀ : 0 < p := zero_lt_one.trans_le hp
  have hlt (s : ℝ) (hs : 0 < s) : r s < 1 :=
    (div_lt_one (lineDensity_pos hp₀ hs)).mpr (imageDensity_lt_lineDensity hp hp₂ hL hs)
  have hMono : MonotoneOn r (Ioi 0) := (imageDensity_div_lineDensity_strictMono hp hp₂ hL).monotoneOn
  have hExist (ε : ℝ) (hε : 0 < ε) : ∃ s > 0, 1 - ε < r s := by
    by_contra! h
    have hBound (t : ℝ) (ht : 0 < t) :
        imagePotential p L t ≤ (1 - ε) * t ^ (-p) := by
      have hI := imagePotential_integrable hp₀ hL ht
      have hρ := (lineDensity_exp_integrable hp₀ ht).const_mul (1 - ε)
      have hCmp : (∫ s : ℝ in Ioi 0, imageDensity p L s * Real.exp (-s * t)) ≤
          ∫ s : ℝ in Ioi 0, (1 - ε) * (lineDensity p s * Real.exp (-s * t)) := by
        apply integral_mono_ae hI hρ
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        have hs₀ : 0 < s := hs
        have hw := (div_le_iff₀ (lineDensity_pos hp₀ hs₀)).mp (h s hs₀)
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hw (Real.exp_pos _).le
      rwa [← imagePotential, integral_const_mul, lineDensity_exp_integral hp₀ ht] at hCmp
    have h0 : ε ≤ 0 := by
      apply le_of_tendsto_of_tendsto tendsto_const_nhds (scaled_deficit_tendsto_zero hp₀ hp₂ hL)
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht₀ : 0 < t := ht
      have hb := mul_le_mul_of_nonneg_left (hBound t ht₀) (Real.rpow_pos_of_pos ht₀ p).le
      have hP := line_power_mul (p := p) ht₀
      nlinarith only [hb, hP, congrArg (ε * ·) hP]
    linarith
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨s, hs, hS⟩ := hExist ε hε
  refine ⟨s, fun t ht => ?_⟩
  have ht₀ := hs.trans_le ht
  have hR : r s ≤ r t := hMono hs ht₀ ht
  change dist (r t) 1 < ε
  rw [Real.dist_eq, abs_of_neg (sub_neg.mpr (hlt t ht₀))]
  linarith

end ACS12.GammaMeasure

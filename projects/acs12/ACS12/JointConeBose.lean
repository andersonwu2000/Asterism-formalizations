import ACS12.OuterDeficitMoments
import ACS12.PureAdjacentOneTail
import ACS12.ConcaveSupport
import ACS12.JointMomentScaling
import ACS12.PressureLikelihood

/-! The shifted Bose mean in the actual joint cone. -/
namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaDeficit (lineDensity)

theorem polyB_monotone : MonotoneOn polyB (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
  · exact fun x _ => (hasDerivAt_polyB x).continuousAt.continuousWithinAt
  · exact fun x _ => (hasDerivAt_polyB x).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : 0 ≤ x := interior_subset hx
    rw [(hasDerivAt_polyB x).deriv]
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx'))


private theorem pureUnitBose_eq :
    (∫ s : ℝ in Ioi 0, polyB s * BoseShape.C s) = 1 := by
  simpa [lineDensity,Real.Gamma_one] using pureBoseB_moment (p := 1) le_rfl (by norm_num) 0

private theorem pureUnitBose_shift_lt :
    (∫ s : ℝ in Ioi 0, polyB s * BoseShape.C s * Real.exp (-s)) < 1 / 10 := by
  have h := pureBoseB_moment (p := 1) le_rfl (by norm_num) 1
  norm_num [lineDensity,Real.Gamma_one,Real.rpow_neg_one,Real.one_rpow,mul_right_comm] at h
  rw [powerTail_shift (q := 3) (by norm_num) 1] at h
  norm_num [Real.one_rpow] at h
  have hZ := powerTail_three_gt_six_fifths
  have he : (∫ s : ℝ in Ioi 0, polyB s * BoseShape.C s * Real.exp (-s)) =
      ∫ s : ℝ in Ioi 0, polyB s * Real.exp (-s) * BoseShape.C s := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s _
    ring
  rw [he]
  linarith only [h,hZ]

private theorem integral_bounded_right {f g : ℝ → ℝ} {c : ℝ} (hf : IntegrableOn f (Ioi 0))
    (hg : Measurable g) (hb : ∀ s > 0, ‖g s‖ ≤ c) :
    IntegrableOn (fun s => f s * g s) (Ioi 0) := by
  apply (hf.bdd_mul (c := c) hg.aestronglyMeasurable ?_).congr
  · exact Eventually.of_forall (fun s => mul_comm (g s) (f s))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact hb s hs

private theorem plainBose_integrable {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun s => polyB (u * s) * BoseShape.C (u * s)) (Ioi 0) := by
  let f (s : ℝ) := polyB s * BoseShape.C s
  have hf : IntegrableOn f (Ioi 0) := Integrable.of_integral_ne_zero (pureUnitBose_eq ▸ one_ne_zero)
  apply (integrableOn_Ioi_comp_mul_left_iff f 0 hu).mpr
  simpa only [mul_zero] using hf

private theorem plainBose_scaled_lower {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    (u / v) ^ 2 / v ≤ ∫ s : ℝ in Ioi 0, polyB (u * s) * BoseShape.C (v * s) := by
  have hv := hu.trans_le huv
  let f (s : ℝ) := polyB s * BoseShape.C s
  have hE : (∫ s : ℝ in Ioi 0, f (v * s)) = v⁻¹ := by
    rw [integral_comp_mul_left_Ioi f 0 hv,mul_zero,smul_eq_mul]
    change v⁻¹ * (∫ s : ℝ in Ioi 0, polyB s * BoseShape.C s) = _
    rw [pureUnitBose_eq,mul_one]
  have hF : IntegrableOn (fun s => f (v * s)) (Ioi 0) := plainBose_integrable hv
  have hMeas : Measurable (fun s => polyB (u * s) * BoseShape.C (v * s)) := by
    unfold polyB BoseShape.C
    fun_prop
  have hI : IntegrableOn (fun s => polyB (u * s) * BoseShape.C (v * s)) (Ioi 0) := by
    apply (plainBose_integrable hu).mono' hMeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0 < s := hs
    have hC := BoseShape.C_antitone (mul_pos hu hs₀) (mul_pos hv hs₀)
      (mul_le_mul_of_nonneg_right huv hs₀.le)
    rw [Real.norm_of_nonneg (mul_nonneg (polyB_pos (mul_pos hu hs₀)).le (BoseShape.C_pos (mul_pos hv hs₀)).le)]
    exact mul_le_mul_of_nonneg_left hC (polyB_pos (mul_pos hu hs₀)).le
  have h := setIntegral_mono_on (hF.const_mul ((u / v) ^ 2)) hI measurableSet_Ioi fun s hs => by
    have hs₀ : 0 < s := hs
    have hB := polyB_scale_lower (div_pos hu hv) ((div_le_one hv).mpr huv) (mul_pos hv hs₀)
    rw [show u / v * (v * s) = u * s by field_simp [hv.ne']] at hB
    unfold f
    nlinarith only [mul_le_mul_of_nonneg_right hB (BoseShape.C_pos (mul_pos hv hs₀)).le]
  rw [integral_const_mul,hE] at h
  simpa only [div_eq_mul_inv] using h

noncomputable def jointBoseGap (u s : ℝ) : ℝ := scaledExpTail s u - scaledExpTail s 1

private theorem plainBoseGap_integrable {u : ℝ} (hu : 0 < u) (hu₁ : u < 1) :
    IntegrableOn (fun s => polyB (u * s) * jointBoseGap u s) (Ioi 0) := by
  have hM : Measurable (fun s => polyB (u * s) * jointBoseGap u s) := by
    unfold polyB jointBoseGap scaledExpTail
    fun_prop
  apply ((plainBose_integrable hu).const_mul (1 - u)).mono' hM.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs₀ : 0 < s := hs
  have hGap := scaledExpTail_secant hs₀ hu hu₁.le
  have hP := (polyB_pos (mul_pos hu hs₀)).le
  have hG : 0 ≤ jointBoseGap u s := (mul_nonneg (sub_nonneg.mpr hu₁.le) (BoseShape.C_pos (mul_pos hs₀ zero_lt_one)).le).trans hGap.1
  rw [Real.norm_of_nonneg (mul_nonneg hP hG)]
  have h := mul_le_mul_of_nonneg_left hGap.2 hP
  dsimp only [jointBoseGap] at *
  rw [mul_comm s u] at h
  linarith only [h]

private theorem plainBoseGap_shifted {u : ℝ} (huL : 7 / 8 ≤ u) (hu₁ : u < 1) :
    (∫ s : ℝ in Ioi 0, polyB (u * s) * jointBoseGap u s * Real.exp (-s * u)) <
      (1 / 7) * ∫ s : ℝ in Ioi 0, polyB (u * s) * jointBoseGap u s := by
  let δ := 1 - u
  let v := (u + 1) / 2
  let f (s : ℝ) := polyB (u * s) * jointBoseGap u s
  let T (s : ℝ) := Real.exp (-s * u)
  have hu : 0 < u := by linarith only [huL]
  have hδ : 0 < δ := sub_pos.mpr hu₁
  have huv : u ≤ v := by dsimp only [v]; linarith only [hu₁]
  have hv₁ : v ≤ 1 := by dsimp only [v]; linarith only [hu₁]
  have hv := hu.trans_le huv
  have hT : Measurable T := by unfold T; fun_prop
  have hTb (s : ℝ) (hs : 0 < s) : ‖T s‖ ≤ 1 := by
    unfold T
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) hu.le)
  have hf : IntegrableOn f (Ioi 0) := plainBoseGap_integrable hu hu₁
  have hfT := integral_bounded_right hf hT hTb
  have hDom (t : ℝ) (hut : u ≤ t) :
      IntegrableOn (fun s => polyB (u * s) * BoseShape.C (t * s)) (Ioi 0) := by
    have ht := hu.trans_le hut
    have hM : Measurable (fun s => polyB (u * s) * BoseShape.C (t * s)) := by
      unfold polyB BoseShape.C
      fun_prop
    apply (plainBose_integrable hu).mono' hM.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0 < s := hs
    have hC := BoseShape.C_antitone (mul_pos hu hs₀) (mul_pos ht hs₀)
      (mul_le_mul_of_nonneg_right hut hs₀.le)
    rw [Real.norm_of_nonneg (mul_nonneg (polyB_pos (mul_pos hu hs₀)).le (BoseShape.C_pos (mul_pos ht hs₀)).le)]
    exact mul_le_mul_of_nonneg_left hC (polyB_pos (mul_pos hu hs₀)).le
  have hLower := setIntegral_mono_on
    (((hDom v huv).add (hDom 1 hu₁.le)).const_mul (δ / 2)) hf measurableSet_Ioi (fun s hs => by
      have hs₀ : 0 < s := hs
      have h₁ := (scaledExpTail_secant hs₀ hu huv).1
      have h₂ := (scaledExpTail_secant hs₀ hv hv₁).1
      rw [mul_comm s v] at h₁
      rw [mul_one] at h₂
      have h : δ / 2 * (BoseShape.C (v * s) + BoseShape.C s) ≤ jointBoseGap u s := by
        unfold δ v at *
        unfold jointBoseGap
        linarith only [h₁,h₂]
      exact (by
        dsimp only [f,Pi.add_apply]
        rw [one_mul]
        nlinarith only [mul_le_mul_of_nonneg_right h (polyB_pos (mul_pos hu hs₀)).le]) )
  rw [integral_const_mul] at hLower
  simp only [Pi.add_apply] at hLower
  rw [integral_add (hDom v huv) (hDom 1 hu₁.le)] at hLower
  have hLV := plainBose_scaled_lower hu huv
  have hL1 := plainBose_scaled_lower hu hu₁.le
  have hRat : 14 / 15 ≤ u / v := (le_div_iff₀ hv).mpr (by dsimp only [v]; linarith only [huL])
  have hRat3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 14 / 15) hRat 3
  have hU3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 8) huL 3
  have hLC : (δ / u) * (7 / 10) ≤ ∫ s : ℝ in Ioi 0, f s := by
    have hS := mul_le_mul_of_nonneg_left (add_le_add hLV hL1) (show 0 ≤ δ / 2 by positivity)
    have hNum : (7 / 10 : ℝ) ≤ ((u / v) ^ 3 + u ^ 3) / 2 := by linarith only [hRat3,hU3]
    have hN := mul_le_mul_of_nonneg_left hNum (div_nonneg hδ.le hu.le)
    have hEq : δ / u * (((u / v) ^ 3 + u ^ 3) / 2) = δ / 2 * ((u / v) ^ 2 / v + (u / 1) ^ 2 / 1) := by
      field_simp [hu.ne',hv.ne']
    rw [hEq] at hN
    exact hN.trans (hS.trans hLower)
  let B (s : ℝ) := polyB s * BoseShape.C s * Real.exp (-s)
  have hBE : (∫ s : ℝ in Ioi 0, B (u * s)) = u⁻¹ * ∫ s : ℝ in Ioi 0, B s := by
    rw [integral_comp_mul_left_Ioi B 0 hu,mul_zero,smul_eq_mul]
  have hBI : IntegrableOn (fun s => B (u * s)) (Ioi 0) := by
    apply (integral_bounded_right (plainBose_integrable hu) hT hTb).congr
    exact Eventually.of_forall fun s => by dsimp only [B,T]; rw [mul_comm u s,neg_mul,mul_comm s u]
  have hUpper := setIntegral_mono_on hfT (hBI.const_mul δ) measurableSet_Ioi fun s hs => by
    have hs₀ : 0 < s := hs
    have h := (scaledExpTail_secant hs₀ hu hu₁.le).2
    rw [mul_comm s u] at h
    have hN := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left h (polyB_pos (mul_pos hu hs₀)).le) (Real.exp_pos (-s * u)).le
    dsimp only [f,T,B,jointBoseGap,δ]
    rw [show -(u * s) = -s * u by ring]
    linarith only [hN]
  rw [integral_const_mul,hBE] at hUpper
  have hN := mul_lt_mul_of_pos_left pureUnitBose_shift_lt (div_pos hδ hu)
  have hD := mul_le_mul_of_nonneg_left hLC (by norm_num : (0 : ℝ) ≤ 1 / 7)
  change (∫ s : ℝ in Ioi 0, f s * T s) < _
  change _ < (1 / 7) * ∫ s : ℝ in Ioi 0, f s
  change δ / u * (∫ s : ℝ in Ioi 0, B s) < _ at hN
  rw [div_eq_mul_inv,mul_assoc] at hN
  have hR : δ * u⁻¹ * (1 / 10) = (1 / 7) * (δ * u⁻¹ * (7 / 10)) := by ring
  have hD' : (1 / 7) * (δ * u⁻¹ * (7 / 10)) ≤ (1 / 7) * ∫ s : ℝ in Ioi 0, f s := by
    simpa only [div_eq_mul_inv] using hD
  exact (hUpper.trans_lt hN).trans_le (hR.trans_le hD')

private theorem lawDensity_mono {p L θ : ℝ} (hp : 1 ≤ p) (hp₂ : p < 2) (hL : 0 < L)
    (hθ : θ ∈ Icc (0 : ℝ) 1) : MonotoneOn (lawDensity p L θ) (Ioi 0) := by
  have hp₀ := zero_lt_one.trans_le hp
  intro s hs t ht hst
  have hρ : lineDensity p s ≤ lineDensity p t := by
    unfold lineDensity
    exact div_le_div_of_nonneg_right (Real.rpow_le_rpow (show 0 < s from hs).le hst
      (sub_nonneg.mpr hp)) (Real.Gamma_pos_of_pos hp₀).le
  have hImage := (imageDensity_div_lineDensity_strictMono hp hp₂ hL).monotoneOn hs ht hst
  have hP (x : ℝ) (hx : 0 < x) : 0 < lineDensity p x := lineDensity_pos hp₀ hx
  have hIm (x : ℝ) (hx : 0 < x) : imageDensity p L x =
      (imageDensity p L x / lineDensity p x) * lineDensity p x := (div_mul_cancel₀ _ (hP x hx).ne').symm
  have hW : imageDensity p L s ≤ imageDensity p L t := by
    rw [hIm s hs,hIm t ht]
    exact mul_le_mul hImage hρ (hP s hs).le (div_nonneg (imageDensity_pos hp₀ hL ht).le (hP t ht).le)
  unfold lawDensity
  exact add_le_add (mul_le_mul_of_nonneg_left hρ (sub_nonneg.mpr hθ.2))
    (mul_le_mul_of_nonneg_left hW hθ.1)

theorem jointBoseGap_shifted {p L θ u m : ℝ} (hp : 1 ≤ p) (hp₂ : p < 2) (hL : 0 < L)
    (hθ : θ ∈ Icc (0 : ℝ) 1) (huL : 7 / 8 ≤ u) (hu₁ : u < 1) (hm : 0 < m) (hmu : m ≤ u) :
    IntegrableOn (fun s => lawDensity p L θ s * polyB (m * s) * Real.exp (-s * u) * jointBoseGap u s)
      (Ioi 0) ∧
    (∫ s : ℝ in Ioi 0, lawDensity p L θ s * polyB (m * s) * Real.exp (-s * u) * jointBoseGap u s) <
      (1 / 7) * ∫ s : ℝ in Ioi 0, lawDensity p L θ s * polyB (u * s) * jointBoseGap u s := by
  let w := lawDensity p L θ
  let f (s : ℝ) := polyB (u * s) * jointBoseGap u s
  let g (s : ℝ) := w s * f s
  let E (s : ℝ) := Real.exp (-s * u)
  let F (s : ℝ) := w s * polyB (m * s) * E s * jointBoseGap u s
  have hu : 0 < u := by linarith only [huL]
  have hp₀ := zero_lt_one.trans_le hp
  have hδ := sub_pos.mpr hu₁
  have hf := plainBoseGap_integrable hu hu₁
  have hE : Measurable E := by unfold E; fun_prop
  have hEb (s : ℝ) (hs : 0 < s) : ‖E s‖ ≤ 1 := by
    unfold E
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) hu.le)
  have hfE := integral_bounded_right hf hE hEb
  have hfP (s : ℝ) (hs : 0 < s) : 0 < f s := by
    have hGap := (scaledExpTail_secant hs hu hu₁.le).1
    exact mul_pos (polyB_pos (mul_pos hu hs)) ((mul_pos hδ (BoseShape.C_pos (mul_pos hs zero_lt_one))).trans_le hGap)
  obtain ⟨hg',_⟩ := outerLawDeficit_integral (u := u) hp hp₂.le hL hθ hu
  have hg : IntegrableOn g (Ioi 0) := by
    apply hg'.congr
    exact Eventually.of_forall fun s => by
      dsimp only [g,f,w,jointBoseGap,lawPeanoDensity,densityPolynomial]
      ring
  have hgE := integral_bounded_right hg hE hEb
  have hRat : MonotoneOn (fun s => g s / f s) (Ioi 0) := by
    intro s hs t ht hst
    change w s * f s / f s ≤ w t * f t / f t
    rw [mul_div_cancel_right₀ _ (hfP s hs).ne',mul_div_cancel_right₀ _ (hfP t ht).ne']
    exact lawDensity_mono hp hp₂ hL hθ hs ht hst
  have hEa : AntitoneOn E (Ioi 0) := fun s hs t ht hst =>
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hst) hu.le)
  have hCov := ACS12.Pressure.likelihood_test_anti hf hg hfE hgE hfP hRat hEa
  letI : NeZero (volume.restrict (Ioi (0 : ℝ))) := ⟨positiveHalfLine_ne_zero⟩
  have hInt_pos {q : ℝ → ℝ} (hq : IntegrableOn q (Ioi 0)) (hP : ∀ s > 0, 0 < q s) :
      0 < ∫ s : ℝ in Ioi 0, q s := by
    have h := integral_strict_of_ae_lt (volume.restrict (Ioi (0 : ℝ))) (integrable_zero ℝ ℝ _) hq
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs; exact hP s hs)
    simpa only [integral_zero] using h
  have hfp := hInt_pos hf hfP
  have hgp := hInt_pos hg (fun s hs => mul_pos (lawDensity_pos hp₀ hL hθ hs) (hfP s hs))
  have hRef := mul_lt_mul_of_pos_right (plainBoseGap_shifted huL hu₁) hgp
  have hCov' : (∫ s : ℝ in Ioi 0, g s * E s) < (1 / 7) * ∫ s : ℝ in Ioi 0, g s := by
    apply lt_of_mul_lt_mul_right _ hfp.le
    exact hCov.trans_lt (hRef.trans_eq (by ring))
  have hPoint (s : ℝ) (hs : 0 < s) : 0 ≤ F s ∧ F s ≤ g s * E s := by
    have hG : 0 ≤ jointBoseGap u s := by
      exact (mul_nonneg hδ.le (BoseShape.C_pos (mul_pos hs zero_lt_one)).le).trans
        (scaledExpTail_secant hs hu hu₁.le).1
    have hB := polyB_monotone (show m * s ∈ Ici 0 from (mul_pos hm hs).le)
      (show u * s ∈ Ici 0 from (mul_pos hu hs).le) (mul_le_mul_of_nonneg_right hmu hs.le)
    have hW := (lawDensity_pos hp₀ hL hθ hs).le
    have hE' := (Real.exp_pos (-s * u)).le
    refine ⟨mul_nonneg (mul_nonneg (mul_nonneg hW (polyB_pos (mul_pos hm hs)).le) hE') hG,?_⟩
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB hW) hE') hG
    unfold F g f E
    linarith only [h]
  have hFI : IntegrableOn F (Ioi 0) := by
    have hJ : Measurable (fun s => polyB (m * s) * E s * jointBoseGap u s) := by
      unfold polyB E jointBoseGap scaledExpTail
      fun_prop
    have hM : Measurable F := by
      convert (lawDensity_measurable (θ := θ) hp₀ hL).mul hJ using 1
      funext s
      unfold F w
      ring
    apply hgE.mono' hM.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_of_nonneg (hPoint s hs).1]
    exact (hPoint s hs).2
  refine ⟨hFI,?_⟩
  change (∫ s : ℝ in Ioi 0, F s) <
    (1 / 7) * ∫ s : ℝ in Ioi 0, w s * polyB (u * s) * jointBoseGap u s
  have h := (setIntegral_mono_on hFI hgE measurableSet_Ioi (fun s hs => (hPoint s hs).2)).trans_lt hCov'
  have hEq : (∫ s : ℝ in Ioi 0, g s) =
      ∫ s : ℝ in Ioi 0, w s * polyB (u * s) * jointBoseGap u s := by
    unfold g f
    simp only [mul_assoc]
  rwa [hEq] at h

end ACS12.GammaMeasure

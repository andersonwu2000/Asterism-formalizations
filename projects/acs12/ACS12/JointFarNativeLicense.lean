import ACS12.BoseSignedEuler
import ACS12.JointFarValue

/-! Full signed Euler majorant of the original far native row. -/
namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaDeficit (lineDensity lineDensity_exp_integrable lineDensity_exp_integral)

private theorem farRight_positive {p : ℝ} (hp : 1 ≤ p) (hpP : p ≤ 9 / 5) :
    0 < pureRight p (7 / 8) (13 / 8) := by
  have hp₂ : p ≤ 2 := by linarith only [hpP]
  have h := pureRight_quadratic_lower hp hp₂ (by norm_num : 0 < (7 / 8 : ℝ))
    (by norm_num) (by norm_num : 0 < (13 / 8 : ℝ))
  have hA : middleA (7 / 8) = 189 / 800 := by norm_num [middleA]
  rw [hA] at h
  apply lt_trans _ h
  apply mul_pos (mul_pos (zero_lt_one.trans_le hp) (Real.rpow_pos_of_pos (by norm_num) _))
  have hL : 0 ≤ (1 / 2 - 189 / 800 : ℝ) / (13 / 8) -
      (1 / 6 - 189 / 800 / 2) * (p + 2) / (13 / 8) ^ 2 - 9 / 100 := by
    norm_num
    linarith only [hpP]
  have hN := mul_nonneg hL (show 0 ≤ p + 1 by positivity)
  norm_num at hN ⊢
  nlinarith only [hN,hp]

private theorem farRight_oneCut :
    ∃ c > (0 : ℝ), ∀ s > 0,
      (s ≤ c → rightMultiplier (189 / 800) (511 / 800) s ≤ 0) ∧
      (c ≤ s → 0 ≤ rightMultiplier (189 / 800) (511 / 800) s) := by
  let g := rightMultiplier (189 / 800) (511 / 800)
  have hC : ContinuousOn g (Icc (1 / 16 : ℝ) 2) := by
    intro s hs
    unfold g rightMultiplier
    have hs₀ : 0 < s := (by norm_num : (0 : ℝ) < 1 / 16).trans_le hs.1
    fun_prop (disch := exact hs₀.ne')
  have hLeft : g (1 / 16) ≤ 0 := by
    have hE : Real.exp (-(1 / 16 : ℝ)) ≤ 16 / 17 := by
      rw [Real.exp_neg]
      apply (inv_le_iff_one_le_mul₀ (Real.exp_pos _)).mpr
      linarith only [Real.add_one_le_exp (1 / 16 : ℝ)]
    unfold g rightMultiplier
    linarith only [hE]
  have hRight : 0 ≤ g 2 := by
    unfold g rightMultiplier
    linarith only [(Real.exp_pos (-(2 : ℝ))).le]
  have hRange : (0 : ℝ) ∈ Icc (g (1 / 16)) (g 2) := ⟨hLeft,hRight⟩
  obtain ⟨c,hc,hZ⟩ := intermediate_value_Icc (by norm_num : (1 / 16 : ℝ) ≤ 2) hC hRange
  have hc₀ : 0 < c := (by norm_num : (0 : ℝ) < 1 / 16).trans_le hc.1
  refine ⟨c,hc₀,?_⟩
  intro s hs
  have hM := rightMultiplier_mono (a := 189 / 800) (z := 511 / 800) (by norm_num)
  have hE : g c = 0 := hZ
  refine ⟨fun h => ?_,fun h => ?_⟩
  · exact (hM hs hc₀ h).trans_eq hE
  · exact hE.symm.trans_le (hM hc₀ hs h)

private theorem farDensity_integral_inverse {p x : ℝ} (hp : 0 < p) (hx : 0 < x) :
    (∫ s : ℝ in Ioi 0, lineDensity p s * Real.exp (-s * x) * ((1 - Real.exp (-s)) / s)) =
      ∫ t : ℝ in x..x + 1, t ^ (-p) := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  let ν := volume.restrict (Ioc x (x + 1))
  let f (s : ℝ × ℝ) := lineDensity p s.1 * Real.exp (-s.1 * s.2)
  have hMeas : Measurable f := by unfold f lineDensity; fun_prop
  have hD : Integrable (fun s : ℝ × ℝ => lineDensity p s.1 * Real.exp (-s.1 * x) * (1 : ℝ)) (μ.prod ν) :=
    (lineDensity_exp_integrable hp hx).mul_prod (integrable_const _)
  have hI : Integrable f (μ.prod ν) := by
    apply hD.mono' hMeas.aestronglyMeasurable
    have hS : ∀ᵐ s ∂μ.prod ν, (0 : ℝ) < (s : ℝ × ℝ).1 :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
    have hT : ∀ᵐ s ∂μ.prod ν, (s : ℝ × ℝ).2 ∈ Ioc x (x + 1) :=
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [hS,hT] with s hs ht
    have hL := (lineDensity_pos hp hs).le
    unfold f
    rw [Real.norm_of_nonneg (mul_nonneg hL (Real.exp_pos _).le),mul_one]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith only [mul_nonneg hs.le (sub_nonneg.mpr ht.1.le)])) hL
  have hA : (∫ s, f s ∂μ.prod ν) = ∫ s : ℝ in Ioi 0,
      lineDensity p s * Real.exp (-s * x) * ((1 - Real.exp (-s)) / s) := by
    rw [integral_prod f hI]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    have hs₀ : 0 < s := hs
    have hExp : (∫ t : ℝ in Ioc x (x + 1), Real.exp (-s * t)) =
        (Real.exp (-s * (x + 1)) - Real.exp (-s * x)) / (-s) := by
      rw [← intervalIntegral.integral_of_le (by linarith : x ≤ x + 1)]
      have hDeriv (t : ℝ) : HasDerivAt (fun t => Real.exp (-s * t) / (-s)) (Real.exp (-s * t)) t := by
        have h := ((hasDerivAt_id t).const_mul (-s)).exp.div_const (-s)
        simp only [id_eq,mul_one] at h
        convert h using 1
        field_simp [hs₀.ne']
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hDeriv t)
        ((by fun_prop : Continuous (fun t : ℝ => Real.exp (-s * t))).intervalIntegrable _ _)]
      ring
    change (∫ t : ℝ in Ioc x (x + 1), lineDensity p s * Real.exp (-s * t)) = _
    rw [integral_const_mul,hExp,show -s * (x + 1) = -s * x + -s by ring,Real.exp_add]
    ring
  rw [← hA,integral_prod_symm f hI,intervalIntegral.integral_of_le (by linarith : x ≤ x + 1)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  exact lineDensity_exp_integral hp (hx.trans ht.1)


theorem farG_eq_pureRight {p x : ℝ} (hx : 0 < x) :
    farG p x = pureRight p (7 / 8) x := by
  unfold farG pureRight
  norm_num only [middleZ,middleA]
  rw [show -(p + 1) = -p - 1 by ring,Real.rpow_sub_one hx.ne',
    Real.rpow_sub_one (add_pos hx zero_lt_one).ne']
  ring

theorem farRight_integral_deriv {p x : ℝ} (hp : 1 ≤ p) (hx : 0 < x) :
    (∫ s : ℝ in Ioi 0, lawRightDensity p 1 0 (7 / 8) s * Real.exp (-s * x) * s) =
      -farGx p x := by
  let L (k : ℕ) (t s : ℝ) := lineDensity p s * s ^ k * Real.exp (-s * t)
  have hp₀ := zero_lt_one.trans_le hp
  have hx' := add_pos hx zero_lt_one
  have hI (k : ℕ) {t : ℝ} (ht : 0 < t) : IntegrableOn (L k t) (Ioi 0) := (lineDensity_moment hp₀ ht k).1
  have hF (k : ℕ) {t : ℝ} (ht : 0 < t) :
      (∫ s : ℝ in Ioi 0, L k t s) = Real.Gamma (p + k) / Real.Gamma p * t ^ (-(p + k)) :=
    (lineDensity_moment hp₀ ht k).2
  have hEq (s : ℝ) (hs : 0 < s) :
      lawRightDensity p 1 0 (7 / 8) s * Real.exp (-s * x) * s =
        (511 / 800) * L 2 x s + (189 / 800) * L 2 (x + 1) s - L 1 x s + L 1 (x + 1) s := by
    simp only [lawRightDensity,lawDensity,sub_zero,one_mul,zero_mul,add_zero,middleRightDensity,middleA0,L]
    rw [show -s * (x + 1) = -s * x + -s by ring,Real.exp_add]
    norm_num [middleZ,middleA]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hEq]
  have hC := integral_four_terms (μ := volume.restrict (Ioi (0 : ℝ)))
    (hI 2 hx) (hI 2 hx') (hI 1 hx) (hI 1 hx') (511 / 800) (189 / 800) 1 (-1)
  simp only [one_mul,neg_one_mul,sub_neg_eq_add] at hC
  rw [hC,hF 2 hx,hF 2 hx',hF 1 hx,hF 1 hx']
  norm_num only [Nat.cast_ofNat,Nat.cast_one]
  have hG₁ : Real.Gamma (p + 1) / Real.Gamma p = p := by
    rw [Real.Gamma_add_one hp₀.ne']
    field_simp [(Real.Gamma_pos_of_pos hp₀).ne']
  have hG₂ : Real.Gamma (p + 2) / Real.Gamma p = p * (p + 1) := by
    rw [show p + 2 = (p + 1) + 1 by ring,Real.Gamma_add_one (by positivity : 0 < p + 1).ne',
      Real.Gamma_add_one hp₀.ne']
    field_simp [(Real.Gamma_pos_of_pos hp₀).ne']
  rw [hG₁,hG₂]
  have hPow₁ (t : ℝ) (ht : 0 < t) : t ^ (-(p + 1)) = t ^ (-p) / t := by
    rw [show -(p + 1) = -p - 1 by ring,Real.rpow_sub_one ht.ne']
  have hPow₂ (t : ℝ) (ht : 0 < t) : t ^ (-(p + 2)) = t ^ (-p) / t ^ (2 : ℕ) := by
    rw [show -(p + 2) = -(p + 1) - 1 by ring,Real.rpow_sub_one ht.ne',hPow₁ t ht,div_div,pow_two]
  rw [hPow₁ x hx,hPow₁ (x + 1) hx',hPow₂ x hx,hPow₂ (x + 1) hx']
  unfold farGx
  ring


private theorem farRight_integral_inverse {p x : ℝ} (hp : 0 < p) (hx : 0 < x) :
    let f (s : ℝ) := lawRightDensity p 1 0 (7 / 8) s * Real.exp (-s * x) * s⁻¹
    IntegrableOn f (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, f s) =
        (511 / 800) * x ^ (-p) + (189 / 800) * (x + 1) ^ (-p) - ∫ t : ℝ in x..x + 1, t ^ (-p) := by
  let f (s : ℝ) := lawRightDensity p 1 0 (7 / 8) s * Real.exp (-s * x) * s⁻¹
  let L (t s : ℝ) := lineDensity p s * Real.exp (-s * t)
  let T (s : ℝ) := L x s * ((1 - Real.exp (-s)) / s)
  have hx' := add_pos hx zero_lt_one
  have hL := lineDensity_exp_integrable hp hx
  have hL' := lineDensity_exp_integrable hp hx'
  have hT : IntegrableOn T (Ioi 0) := by
    apply hL.mono' (by unfold T L lineDensity; fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0 < s := hs
    have hD : 0 ≤ (1 - Real.exp (-s)) / s := div_nonneg
      (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs₀.le))) hs₀.le
    have hD' : (1 - Real.exp (-s)) / s ≤ 1 :=
      (div_le_one hs₀).mpr (by linarith only [Real.add_one_le_exp (-s)])
    have h₀ : 0 ≤ L x s := mul_nonneg (lineDensity_pos hp hs₀).le (Real.exp_pos _).le
    rw [show T s = L x s * ((1 - Real.exp (-s)) / s) from rfl,Real.norm_of_nonneg (mul_nonneg h₀ hD)]
    exact mul_le_of_le_one_right h₀ hD'
  have hE (s : ℝ) (hs : 0 < s) : f s = (511 / 800) * L x s + (189 / 800) * L (x + 1) s - T s := by
    unfold f T L
    rw [lawRightDensity,middleRightDensity_eq hs,show -s * (x + 1) = -s * x + -s by ring,Real.exp_add]
    norm_num [lawDensity,rightMultiplier,middleA,middleZ]
    field_simp [hs.ne']
  have hC : IntegrableOn (fun s => (511 / 800) * L x s + (189 / 800) * L (x + 1) s) (Ioi 0) :=
    (hL.const_mul _).add (hL'.const_mul _)
  refine ⟨(hC.sub hT).congr ?_,?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hE s hs).symm
  · change (∫ s : ℝ in Ioi 0, f s) = _
    rw [setIntegral_congr_fun measurableSet_Ioi hE,integral_sub hC hT,
      integral_add (hL.const_mul _) (hL'.const_mul _),integral_const_mul,integral_const_mul]
    unfold T L
    rw [lineDensity_exp_integral hp hx,lineDensity_exp_integral hp hx',farDensity_integral_inverse hp hx]

theorem farNative_sampling_upper {p : ℝ} (hp : 1 ≤ p) (hpP : p ≤ 9 / 5) :
    samplingHead (pureRight p (7 / 8)) (13 / 8) (3 / 4) <
      farGIntegral p + (3 / 8) * farG p (13 / 8) - (3 / 64) * farGx p (13 / 8) := by
  let u : ℝ := 7 / 8
  let x : ℝ := 13 / 8
  let r : ℝ := 3 / 4
  let g := lawRightDensity p 1 0 u
  let f (s : ℝ) := g s * Real.exp (-s * x)
  have hp₂ : p ≤ 2 := by linarith only [hpP]
  have hp₀ := zero_lt_one.trans_le hp
  have hx : 0 < x := by norm_num [x]
  have hr : 0 < r := by norm_num [r]
  have hu : 0 < u := by norm_num [u]
  have hθ : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl,zero_le_one⟩
  obtain ⟨c,hc,hCut⟩ := farRight_oneCut
  have hCutE (s : ℝ) (hs : 0 < s) : f s =
      (lineDensity p s * s * Real.exp (-s * x)) * rightMultiplier (189 / 800) (511 / 800) s := by
    unfold f g lawRightDensity
    rw [middleRightDensity_eq hs]
    norm_num [lawDensity,u,middleA,middleZ]
    ring
  have hLeft (s : ℝ) (hs : 0 < s) (hsc : s < c) : f s ≤ 0 := by
    rw [hCutE s hs]
    exact mul_nonpos_of_nonneg_of_nonpos (by have := lineDensity_pos hp₀ hs; positivity)
      ((hCut s hs).1 hsc.le)
  have hRight (s : ℝ) (hcs : c < s) : 0 ≤ f s := by
    have hs := hc.trans hcs
    rw [hCutE s hs]
    exact mul_nonneg (by have := lineDensity_pos hp₀ hs; positivity) ((hCut s hs).2 hcs.le)
  have hF : IntegrableOn f (Ioi 0) := lawRightDensity_integrable hp hp₂ zero_lt_one hθ hx
  have hP : (∫ s : ℝ in Ioi 0, f s) = pureRight p u x := lawRightTest_zero hp hp₂ zero_lt_one hx
  have hP₀ : 0 < ∫ s : ℝ in Ioi 0, f s := hP ▸ farRight_positive hp hpP
  have hInv := farRight_integral_inverse hp₀ hx
  have hI : IntegrableOn (fun s => f s * s⁻¹) (Ioi 0) := hInv.1
  obtain ⟨B,hB,hDom⟩ := lawRightDensity_bound (u := u) hp hp₂ zero_lt_one hθ
  have hD : IntegrableOn (fun s => f s * s) (Ioi 0) := by
    apply (((expMoment_nat_integrable 2 hx).add (expMoment_nat_integrable 3 hx)).const_mul B).mono'
    · exact (hF.aestronglyMeasurable.mul (measurable_id.aestronglyMeasurable))
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs₀ : 0 < s := hs
      have h := mul_le_mul_of_nonneg_right (hDom s hs₀) (show 0 ≤ Real.exp (-s * x) * s by positivity)
      unfold f
      rw [norm_mul,norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le,Real.norm_of_nonneg hs₀.le]
      dsimp only [Pi.add_apply]
      rw [Real.norm_eq_abs]
      exact (by unfold g; nlinarith only [h])
  have hTail := lawRightTail_sampling (u := u) (t := u) (q := r) hp hp₂ zero_lt_one hθ hu.le hr
  have hTailEq (s : ℝ) (hs : 0 < s) :
      g s * Real.exp (-s * u) * scaledExpTail s r = f s * (r / (1 - Real.exp (-(r * s)))) := by
    have hR : x = u + r := by norm_num [x,u,r]
    have hE : Real.exp (s * r) * Real.exp (-(s * r)) = 1 := by rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
    have hB' : scaledExpTail s r = Real.exp (-(s * r)) * (r / (1 - Real.exp (-(s * r)))) := by
      unfold scaledExpTail
      have hD : Real.exp (-(s * r)) * (Real.exp (s * r) - 1) = 1 - Real.exp (-(s * r)) := by
        rw [mul_sub,mul_comm (Real.exp (-(s * r))) (Real.exp (s * r)),hE,mul_one]
      calc
        _ = (Real.exp (-(s * r)) * r) / (Real.exp (-(s * r)) * (Real.exp (s * r) - 1)) :=
          (mul_div_mul_left _ _ (Real.exp_ne_zero _)).symm
        _ = _ := by rw [hD,mul_div_assoc]
    unfold f
    rw [hR,show -s * (u + r) = -s * u + -(s * r) by ring,Real.exp_add,hB',mul_comm r s]
    ring
  have hQ : IntegrableOn (fun s => f s * (r / (1 - Real.exp (-(r * s))))) (Ioi 0) := by
    apply hTail.1.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact hTailEq s hs
  have hS : samplingHead (pureRight p u) x r =
      ∫ s : ℝ in Ioi 0, f s * (r / (1 - Real.exp (-(r * s)))) := by
    have hE : samplingTail (lawRightTest p 1 0 u) u r = samplingHead (pureRight p u) x r := by
      rw [samplingTail_eq_shift,show u + r = x by norm_num [u,r,x]]
      unfold samplingHead
      apply congrArg (fun v => r * v)
      apply tsum_congr
      intro j
      exact lawRightTest_zero hp hp₂ zero_lt_one (by positivity)
    rw [← hE,hTail.2]
    exact setIntegral_congr_fun measurableSet_Ioi hTailEq
  have h := signedBose_B2_upper hr hc hF hI hD hQ hLeft hRight hP₀
  rw [← hS,hInv.2,hP,← farG_eq_pureRight hx,farRight_integral_deriv hp hx] at h
  unfold x r at h
  unfold farGIntegral
  convert h using 1 <;> norm_num <;> ring


theorem jointFarNative_full_upper {p : ℝ} (hp : 1 ≤ p) (hpP : p ≤ 9 / 5) :
    (7 / 8) * (1 + (189 / 800) * p - pureZ p) +
      samplingHead (pureRight p (7 / 8)) (7 / 8) (3 / 4) < jointFarNative p := by
  have hp₂ : p ≤ 2 := by linarith only [hpP]
  have hθ : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl,zero_le_one⟩
  have hA := lawRight_abs_samples_summable (u := 7 / 8) (t := 1 / 8) (q := 3 / 4)
    hp hp₂ zero_lt_one hθ (by norm_num) (by norm_num)
  have hS : Summable (fun j : ℕ => pureRight p (7 / 8) (7 / 8 + (j : ℝ) * (3 / 4))) := by
    apply Summable.of_norm
    apply hA.congr
    intro j
    simp only [Nat.cast_succ,Real.norm_eq_abs]
    rw [show (1 / 8 : ℝ) + ((j : ℝ) + 1) * (3 / 4) = 7 / 8 + (j : ℝ) * (3 / 4) by ring]
    rw [lawRightTest_zero hp hp₂ zero_lt_one (by positivity)]
  rw [samplingHead_split _ _ _ hS,samplingTail_eq_shift,← farG_eq_pureRight (by norm_num : (0 : ℝ) < 7 / 8),
    show (7 / 8 : ℝ) + 3 / 4 = 13 / 8 by norm_num]
  unfold jointFarNative
  linarith only [farNative_sampling_upper hp hpP]

end ACS12.GammaMeasure

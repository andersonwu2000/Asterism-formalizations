import ACS12.HighIncidentFee
import ACS12.PressureLikelihood
import ACS12.GammaRadialComparison

/-! The clipped occupied-edge fee under the normalized Gamma laws. -/

namespace ACS12.GammaMeasure

open Set Filter MeasureTheory Polynomial CenteredCircle.AllN
open GammaDeficit (lineDensity lineDensity_exp_integrable lineDensity_exp_integral)

noncomputable def incidentGammaWeight (a s : ℝ) : ℝ := lineDensity a s * Real.exp (-s)

theorem incidentGammaWeight_integrable {a : ℝ} (ha : 0 < a) :
    IntegrableOn (incidentGammaWeight a) (Ioi 0) := by
  simpa only [incidentGammaWeight,mul_one] using lineDensity_exp_integrable ha zero_lt_one

theorem incidentGammaWeight_integral {a : ℝ} (ha : 0 < a) :
    (∫ s : ℝ in Ioi 0, incidentGammaWeight a s) = 1 := by
  simpa only [incidentGammaWeight,mul_one,Real.one_rpow] using lineDensity_exp_integral ha zero_lt_one

theorem incidentGammaWeight_pos {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    0 < incidentGammaWeight a s := mul_pos (lineDensity_pos ha hs) (Real.exp_pos _)

theorem gammaWeight_mul_fee_integrable {a u c : ℝ} (ha : 0 < a) (hu : 0 ≤ u) (hc : 0 ≤ c) :
    IntegrableOn (fun s => incidentGammaWeight a s * highIncidentFeeTest u c s) (Ioi 0) := by
  let w := incidentGammaWeight a
  have hw := incidentGammaWeight_integrable ha
  apply (hw.const_mul (1 + c)).mono'
    (hw.aestronglyMeasurable.mul (highIncidentFee_measurable u c).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  change ‖w s * highIncidentFeeTest u c s‖ ≤ (1 + c) * w s
  have hW := (incidentGammaWeight_pos ha hs).le
  have hT : 0 ≤ highIncidentFeeTest u c s := le_max_left _ _
  rw [Real.norm_of_nonneg (mul_nonneg hW hT),mul_comm (1 + c)]
  exact mul_le_mul_of_nonneg_left (highIncidentFee_le hs hu hc) hW

theorem incidentGammaFee_antitone_shape {a b u c : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hu : 0 ≤ u) (hc : 0 ≤ c) (hcu : c ≤ u) :
    (∫ s : ℝ in Ioi 0, incidentGammaWeight b s * highIncidentFeeTest u c s) ≤
      ∫ s : ℝ in Ioi 0, incidentGammaWeight a s * highIncidentFeeTest u c s := by
  have hb := ha.trans_le hab
  have hR : MonotoneOn (fun s => incidentGammaWeight b s / incidentGammaWeight a s) (Ioi 0) := by
    have hE (s : ℝ) (hs : 0 < s) : incidentGammaWeight b s / incidentGammaWeight a s =
        (Real.Gamma a / Real.Gamma b) * s ^ (b - a) := by
      unfold incidentGammaWeight lineDensity
      rw [mul_div_mul_right _ _ (Real.exp_ne_zero _),show b - a = (b - 1) - (a - 1) by ring,
        Real.rpow_sub hs (b - 1) (a - 1)]
      have hGA : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
      have hGB : Real.Gamma b ≠ 0 := (Real.Gamma_pos_of_pos hb).ne'
      have hA : s ^ (a - 1) ≠ 0 := (Real.rpow_pos_of_pos hs _).ne'
      field_simp [hGA,hGB,hA]
    intro x hx y hy hxy
    change incidentGammaWeight b x / incidentGammaWeight a x ≤ incidentGammaWeight b y / incidentGammaWeight a y
    rw [hE x hx,hE y hy]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx.le hxy (sub_nonneg.mpr hab)) (by positivity)
  have h := Pressure.likelihood_test_anti (incidentGammaWeight_integrable ha)
    (incidentGammaWeight_integrable hb) (gammaWeight_mul_fee_integrable ha hu hc)
    (gammaWeight_mul_fee_integrable hb hu hc) (fun _ hs => incidentGammaWeight_pos ha hs)
    hR (highIncidentFee_antitone hc hcu)
  simpa only [incidentGammaWeight_integral ha,incidentGammaWeight_integral hb,mul_one] using h

private theorem exp_three_gt_eighteen : (18 : ℝ) < Real.exp 3 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 6
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  linarith only [h]

theorem incidentGammaFee_one_lt :
    (∫ s : ℝ in Ioi 0, incidentGammaWeight 1 s * highIncidentFeeTest (4 / 9) (8 / 27) s) < 35 / 81 := by
  have hCut : highIncidentFeeRaw (4 / 9) (8 / 27) 3 ≤ 0 := by
    have h := incidentFee_raw_le_poly (C := 1 / 27) (T := 3)
      (by norm_num : (0 : ℝ) ≤ 4 / 9) (by norm_num : (0 : ℝ) ≤ 8 / 27)
      (by norm_num) (by norm_num : (0 : ℝ) < 3) le_rfl
    linarith only [h]
  have h := incidentFee_integral_le_poly (C := 1 / 27) (T := 3)
    (by norm_num : (0 : ℝ) ≤ 4 / 9) (by norm_num : (0 : ℝ) ≤ 8 / 27)
    (by norm_num) (incidentGammaWeight_integrable zero_lt_one)
    (fun s hs => (incidentGammaWeight_pos zero_lt_one hs).le) (by norm_num) hCut (by norm_num) (by
      intro s hs
      have hSq := pow_le_pow_left₀ hs.1.le hs.2 2
      linarith only [hs.2,hSq])
  have hInt :
      (∫ s in (0 : ℝ)..3, incidentGammaWeight 1 s * (1 - 4 / 9 - (4 / 9 - 8 / 27) / 2 * s - (1 / 27) * s ^ 2)) =
        (11 + 10 * Real.exp (-3)) / 27 := by
    let F (s : ℝ) := Real.exp (-s) * (s ^ 2 + 4 * s - 11) / 27
    have hD (s : ℝ) : HasDerivAt F (incidentGammaWeight 1 s *
        (1 - 4 / 9 - (4 / 9 - 8 / 27) / 2 * s - (1 / 27) * s ^ 2)) s := by
      have hi := hasDerivAt_id s
      convert (hi.neg.exp.mul (((hi.pow 2).add (hi.const_mul 4)).sub_const 11)).div_const 27 using 1
      simp only [incidentGammaWeight,lineDensity,sub_self,Real.rpow_zero,Real.Gamma_one,div_one,
        one_mul,Pi.neg_apply,Pi.pow_apply,Pi.add_apply,id_eq,mul_one]
      ring
    have hC : Continuous (fun s => incidentGammaWeight 1 s *
        (1 - 4 / 9 - (4 / 9 - 8 / 27) / 2 * s - (1 / 27) * s ^ 2)) := by
      simp only [incidentGammaWeight,lineDensity,sub_self,Real.rpow_zero,Real.Gamma_one,div_one,one_mul]
      fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hD s) (hC.intervalIntegrable _ _)]
    norm_num [F]
    ring
  rw [hInt] at h
  have hE : Real.exp (-3) < 1 / 18 := by
    rw [Real.exp_neg,one_div]
    exact inv_strictAnti₀ (by norm_num) exp_three_gt_eighteen
  linarith only [h,hE]

theorem incidentGammaFee_three_halves_lt :
    (∫ s : ℝ in Ioi 0, incidentGammaWeight (3 / 2) s * highIncidentFeeTest (7 / 16) (5 / 16) s) < 3 / 8 := by
  have hCut : highIncidentFeeRaw (7 / 16) (5 / 16) 3 ≤ 0 := by
    have h := incidentFee_raw_le_poly (C := 1 / 24) (T := 3)
      (by norm_num : (0 : ℝ) ≤ 7 / 16) (by norm_num : (0 : ℝ) ≤ 5 / 16)
      (by norm_num) (by norm_num : (0 : ℝ) < 3) le_rfl
    linarith only [h]
  have hShape : (0 : ℝ) < 3 / 2 := by norm_num
  let Q (s : ℝ) := 9 / 16 - s / 16 - s ^ 2 / 24
  have h := incidentFee_integral_le_poly (C := 1 / 24) (T := 3)
    (by norm_num : (0 : ℝ) ≤ 7 / 16) (by norm_num : (0 : ℝ) ≤ 5 / 16)
    (by norm_num) (incidentGammaWeight_integrable hShape)
    (fun s hs => (incidentGammaWeight_pos hShape hs).le) (by norm_num) hCut (by norm_num) (by
      intro s hs
      have hSq := pow_le_pow_left₀ hs.1.le hs.2 2
      linarith only [hs.2,hSq])
  have hI : (∫ s : ℝ in Ioi 0, incidentGammaWeight (3 / 2) s *
      highIncidentFeeTest (7 / 16) (5 / 16) s) ≤
      ∫ s in (0 : ℝ)..3, incidentGammaWeight (3 / 2) s * Q s := by
    convert h using 2
    funext s
    unfold Q
    ring
  let F (s : ℝ) := Real.exp (-s) * s ^ (3 / 2 : ℝ) * (1 / 6 + s / 24) / Real.Gamma (3 / 2)
  have hF (s : ℝ) (hs : 0 < s) :
      HasDerivAt F (incidentGammaWeight (3 / 2) s * (Q s - 5 / 16)) s := by
    have hi := hasDerivAt_id s
    have hp := Real.hasDerivAt_rpow_const (p := 3 / 2) (Or.inl hs.ne')
    convert ((hi.neg.exp.mul hp).mul ((hi.div_const 24).const_add (1 / 6))).div_const
      (Real.Gamma (3 / 2)) using 1
    simp only [Q,incidentGammaWeight,lineDensity,Pi.neg_apply,Pi.mul_apply,id_eq]
    norm_num only [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num]
    rw [show s ^ (3 / 2 : ℝ) = s ^ (1 / 2 : ℝ) * s by
      rw [← Real.rpow_add_one hs.ne']; norm_num]
    ring
  have hW : Continuous (incidentGammaWeight (3 / 2)) := by
    unfold incidentGammaWeight lineDensity
    exact ((Real.continuous_rpow_const (by norm_num)).div_const _).mul (by fun_prop)
  have hQ : Continuous Q := by unfold Q; fun_prop
  have hC : Continuous F := by
    unfold F
    exact (((by fun_prop : Continuous (fun s : ℝ => Real.exp (-s))).mul
      (Real.continuous_rpow_const hShape.le)).mul (by fun_prop)).div_const _
  have hD := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (by norm_num : (0 : ℝ) < 3) (fun s hs => hF s hs.1)
    ((hW.mul (hQ.sub continuous_const)).intervalIntegrable 0 3)
    (hC.continuousAt.continuousWithinAt.tendsto (s := Ioi 0) (x := 0))
    (hC.continuousAt.continuousWithinAt.tendsto (s := Iio 3) (x := 3))
  have h₀ : F 0 = 0 := by
    simp [F,Real.zero_rpow hShape.ne']
  have hE :
      (∫ s in (0 : ℝ)..3, incidentGammaWeight (3 / 2) s * (Q s - 5 / 16)) =
        (∫ s in (0 : ℝ)..3, incidentGammaWeight (3 / 2) s * Q s) -
          (5 / 16) * (∫ s in (0 : ℝ)..3, incidentGammaWeight (3 / 2) s) := by
    simp_rw [mul_sub,mul_comm _ (5 / 16 : ℝ)]
    rw [intervalIntegral.integral_sub
      (show IntervalIntegrable (fun s => incidentGammaWeight (3 / 2) s * Q s) volume 0 3 from
        (hW.mul hQ).intervalIntegrable _ _)
      ((hW.const_mul (5 / 16)).intervalIntegrable _ _),intervalIntegral.integral_const_mul]
  have hPi : Real.sqrt 3 ≤ Real.sqrt Real.pi := Real.sqrt_le_sqrt Real.pi_gt_three.le
  have hGamma : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
    ring
  let d := Real.sqrt 3 / Real.Gamma (3 / 2)
  have hL : (∫ s in (0 : ℝ)..3, incidentGammaWeight (3 / 2) s) + d * Real.exp (-3) ≤ 1 := by
    have hw := incidentGammaWeight_integrable hShape
    have hExp : IntegrableOn (fun s : ℝ => Real.exp (-s)) (Ioi 3) := by
      simpa only [one_mul,neg_mul] using (exp_neg_integrableOn_Ioi 3 (b := 1) zero_lt_one)
    have hTail := setIntegral_mono_on (hExp.const_mul d)
      (hw.mono_set (Ioi_subset_Ioi (by norm_num))) measurableSet_Ioi (fun s hs => by
        have hs₀ : 0 < s := (by norm_num : (0 : ℝ) < 3).trans hs
        have hR := Real.sqrt_le_sqrt (show 3 ≤ s from hs.le)
        rw [Real.sqrt_eq_rpow s] at hR
        change d * Real.exp (-s) ≤ incidentGammaWeight (3 / 2) s
        unfold d incidentGammaWeight lineDensity
        rw [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num]
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hR
          (Real.Gamma_pos_of_pos hShape).le) (Real.exp_pos _).le)
    rw [integral_const_mul,integral_exp_neg_Ioi] at hTail
    have hDisj : Disjoint (Ioc (0 : ℝ) 3) (Ioi 3) := Set.disjoint_left.mpr fun _ h₁ h₂ => h₂.not_ge h₁.2
    have hUnion : Ioc (0 : ℝ) 3 ∪ Ioi 3 = Ioi 0 := by
      ext s
      simp only [mem_union,mem_Ioc,mem_Ioi]
      constructor
      · rintro (h | h)
        · exact h.1
        · linarith only [h]
      · intro h
        rcases le_or_gt s 3 with hs | hs
        · exact Or.inl ⟨h,hs⟩
        · exact Or.inr hs
    have hSum := setIntegral_union hDisj measurableSet_Ioi
      (hw.mono_set (fun _ hs => hs.1)) (hw.mono_set (Ioi_subset_Ioi (by norm_num)))
    rw [hUnion,incidentGammaWeight_integral hShape] at hSum
    rw [intervalIntegral.integral_of_le (by norm_num)]
    linarith only [hSum,hTail]
  have hFT : F 3 - (5 / 16) * d * Real.exp (-3) ≤ (9 / 8) * Real.exp (-3) := by
    unfold F
    rw [show (3 : ℝ) ^ (3 / 2 : ℝ) = Real.sqrt 3 * 3 by
      rw [Real.sqrt_eq_rpow,← Real.rpow_add_one (by norm_num : (3 : ℝ) ≠ 0)]; norm_num]
    have hd : d ≤ 2 := by
      unfold d
      rw [hGamma]
      exact (div_le_iff₀ (by positivity)).mpr (by linarith only [hPi])
    have hF' : Real.exp (-3) * (Real.sqrt 3 * 3) * (1 / 6 + 3 / 24) / Real.Gamma (3 / 2) -
        (5 / 16) * d * Real.exp (-3) = (9 / 16) * d * Real.exp (-3) := by unfold d; ring
    rw [hF']
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by norm_num)) (Real.exp_pos _).le).trans_eq
      (by ring)
  have hExp : Real.exp (-3) < 1 / 18 := by
    rw [Real.exp_neg,one_div]
    exact inv_strictAnti₀ (by norm_num) exp_three_gt_eighteen
  rw [hE,h₀,sub_zero] at hD
  have hL' := mul_le_mul_of_nonneg_left hL (by norm_num : (0 : ℝ) ≤ 5 / 16)
  nlinarith only [hI,hD,hL',hFT,hExp]

end ACS12.GammaMeasure

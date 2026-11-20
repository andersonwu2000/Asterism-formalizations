import ACS12.PressureFeePade
import ACS12.JointGapK
import Mathlib.Analysis.SpecialFunctions.PolynomialExp

/-! The complete normalized incident fee and its two endpoint integrals. -/
namespace ACS12.GammaMeasure

open Set Filter MeasureTheory Polynomial CenteredCircle.AllN
open GammaDeficit (lineDensity)

noncomputable def highIncidentFeeRaw (u c s : ℝ) : ℝ :=
  1 + c - (u + c) * expHeadFactor s + c * s

noncomputable def highIncidentFeeTest (u c s : ℝ) : ℝ := max 0 (highIncidentFeeRaw u c s)

theorem highIncidentFee_measurable (u c : ℝ) : Measurable (highIncidentFeeTest u c) := by
  unfold highIncidentFeeTest highIncidentFeeRaw expHeadFactor
  fun_prop

theorem highIncidentFee_antitone {u c : ℝ} (hc : 0 ≤ c) (hcu : c ≤ u) :
    AntitoneOn (highIncidentFeeTest u c) (Ioi 0) := by
  have hD (s : ℝ) (hs : 0 < s) : HasDerivAt (highIncidentFeeRaw u c)
      (-(u + c) * (1 - BoseShape.C s) + c) s := by
    have hE : HasDerivAt expHeadFactor (1 - BoseShape.C s) s := by
      have h := (hasDerivAt_id s).add (BoseShape.expTail_derivative hs)
      apply (show HasDerivAt (fun x => x + expTailFactor x) (1 - BoseShape.C s) s by
        simpa only [sub_eq_add_neg] using h).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hs] with x hx
      exact expHeadFactor_eq_add_expTail hx
    exact (((hE.const_mul (u + c)).const_sub (1 + c)).add ((hasDerivAt_id s).const_mul c))
      |>.congr_deriv (by ring)
  have hRaw : AntitoneOn (highIncidentFeeRaw u c) (Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    · exact fun s hs => (hD s hs).continuousAt.continuousWithinAt
    · exact fun s hs => (hD s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      have hs₀ : 0 < s := interior_subset hs
      rw [(hD s hs₀).deriv]
      have h := mul_le_mul_of_nonneg_left (show (1 / 2 : ℝ) ≤ 1 - BoseShape.C s by
        linarith only [boseC_lt_half hs₀]) (show 0 ≤ u + c by linarith only [hc,hcu])
      linarith only [h,hcu]
  exact fun s hs t ht hst => max_le_max le_rfl (hRaw hs ht hst)

theorem highIncidentFee_mono_coeff {u c d s : ℝ} (hs : 0 < s) (hcd : c ≤ d) :
    highIncidentFeeTest u c s ≤ highIncidentFeeTest u d s := by
  have hB : expTailFactor s ≤ 1 := by
    unfold expTailFactor
    exact (div_le_one (expTail_den_pos hs)).mpr (by linarith only [Real.add_one_le_exp s])
  unfold highIncidentFeeTest highIncidentFeeRaw
  rw [expHeadFactor_eq_add_expTail hs]
  exact max_le_max le_rfl (by nlinarith only [mul_nonneg (sub_nonneg.mpr hcd) (sub_nonneg.mpr hB)])

theorem highIncidentFee_le {u c s : ℝ} (hs : 0 < s) (hu : 0 ≤ u) (hc : 0 ≤ c) :
    highIncidentFeeTest u c s ≤ 1 + c := by
  have hE : s ≤ expHeadFactor s := by
    rw [expHeadFactor_eq_add_expTail hs]
    exact le_add_of_nonneg_right (div_nonneg hs.le (expTail_den_pos hs).le)
  have h := mul_le_mul_of_nonneg_left hE (show 0 ≤ u + c by positivity)
  unfold highIncidentFeeTest highIncidentFeeRaw
  exact max_le (by positivity) (by nlinarith only [h,mul_nonneg hu hs.le])

noncomputable def highIncidentFeeWeight (s : ℝ) : ℝ := s * Real.exp (-s)

theorem highIncidentFeeWeight_integrable : IntegrableOn highIncidentFeeWeight (Ioi 0) := by
  simpa only [highIncidentFeeWeight,pow_one,mul_one] using expMoment_nat_integrable 1 (c := 1) zero_lt_one

theorem highIncidentFee_integrable {u c : ℝ} (hu : 0 ≤ u) (hc : 0 ≤ c) :
    IntegrableOn (fun s => highIncidentFeeWeight s * highIncidentFeeTest u c s) (Ioi 0) := by
  have hM : Measurable (fun s => highIncidentFeeWeight s * highIncidentFeeTest u c s) :=
    (by unfold highIncidentFeeWeight; fun_prop : Measurable highIncidentFeeWeight).mul (highIncidentFee_measurable u c)
  apply (highIncidentFeeWeight_integrable.const_mul (1 + c)).mono' hM.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hW : 0 ≤ highIncidentFeeWeight s := mul_nonneg (show 0 < s from hs).le (Real.exp_pos _).le
  have hT : 0 ≤ highIncidentFeeTest u c s := le_max_left _ _
  rw [Real.norm_of_nonneg (mul_nonneg hW hT),mul_comm (1 + c)]
  exact mul_le_mul_of_nonneg_left (highIncidentFee_le hs hu hc) hW

private theorem highIncident_head_lower {s D : ℝ} (hs : 0 < s)
    (h : D * (60 + s ^ 2) ≤ 5) : 1 + s / 2 + D * s ^ 2 ≤ expHeadFactor s := by
  have hB := mul_le_mul_of_nonneg_left (Pressure.bose_lower_pade hs).le hs.le
  have hC : D ≤ 5 / (60 + s ^ 2) := (le_div_iff₀ (by positivity)).mpr h
  have hC' := mul_le_mul_of_nonneg_right hC (sq_nonneg s)
  have hE : s * (1 / s) = 1 := by field_simp [hs.ne']
  rw [expHeadFactor_eq_add_expTail hs]
  unfold expTailFactor
  simp only [mul_add,mul_sub,hE,mul_one_div] at hB
  rw [show s * (5 * s / (60 + s ^ 2)) = 5 / (60 + s ^ 2) * s ^ 2 by ring] at hB
  linarith only [hB,hC']

private theorem exp_poly_fee_integral (A B C T : ℝ) :
    (∫ s in (0 : ℝ)..T, highIncidentFeeWeight s * (A - B * s - C * s ^ 2)) =
      A - 2 * B - 6 * C + Real.exp (-T) *
        (-A * (T + 1) + B * (T ^ 2 + 2 * T + 2) + C * (T ^ 3 + 3 * T ^ 2 + 6 * T + 6)) := by
  let P : ℝ[X] := -Polynomial.C A * (X + 1) + Polynomial.C B * (X ^ 2 + 2 * X + 2) +
    Polynomial.C C * (X ^ 3 + 3 * X ^ 2 + 6 * X + 6)
  let F (s : ℝ) := Real.exp (-s) * P.eval s
  have hD (s : ℝ) : HasDerivAt F (highIncidentFeeWeight s * (A - B * s - C * s ^ 2)) s := by
    convert (((hasDerivAt_id s).neg.exp).mul (P.hasDerivAt s)) using 1
    simp only [P,highIncidentFeeWeight,derivative_add,derivative_mul,derivative_neg,derivative_pow,
      derivative_C,derivative_X,derivative_ofNat,derivative_one,eval_zero,eval_one,zero_mul,zero_add,add_zero,eval_add,eval_mul,eval_neg,
      eval_pow,eval_C,eval_X,eval_ofNat,Pi.neg_apply,id_eq,Nat.cast_ofNat,mul_one]
    ring
  have hC : Continuous (fun s => highIncidentFeeWeight s * (A - B * s - C * s ^ 2)) := by
    unfold highIncidentFeeWeight
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hD s) (hC.intervalIntegrable _ _)]
  norm_num [F,P]
  ring

theorem incidentFee_raw_le_poly {u c C T s : ℝ} (hu : 0 ≤ u) (hc : 0 ≤ c)
    (hCoeff : C * (60 + T ^ 2) ≤ 5 * (u + c)) (hs : 0 < s) (hsT : s ≤ T) :
    highIncidentFeeRaw u c s ≤ 1 - u - (u - c) / 2 * s - C * s ^ 2 := by
  have hU : 0 ≤ u + c := add_nonneg hu hc
  have hD := highIncident_head_lower hs (D := 5 / (60 + T ^ 2)) (by
    have h := pow_le_pow_left₀ hs.le hsT 2
    calc
      _ ≤ (5 / (60 + T ^ 2)) * (60 + T ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith only [h]) (by positivity)
      _ = 5 := div_mul_cancel₀ _ (by positivity))
  have hK := mul_le_mul_of_nonneg_left hD hU
  have hC : C ≤ (u + c) * (5 / (60 + T ^ 2)) := by
    rw [← mul_div_assoc]
    exact (le_div_iff₀ (by positivity)).mpr (hCoeff.trans_eq (mul_comm _ _))
  have hW := mul_le_mul_of_nonneg_right hC (sq_nonneg s)
  unfold highIncidentFeeRaw
  nlinarith only [hK,hW]

theorem incidentFee_integral_le_poly {u c C T : ℝ} {w : ℝ → ℝ}
    (hu : 0 ≤ u) (hc : 0 ≤ c) (hcu : c ≤ u)
    (hw : IntegrableOn w (Ioi 0)) (hw₀ : ∀ s > 0, 0 ≤ w s)
    (hT : 0 < T) (hCut : highIncidentFeeRaw u c T ≤ 0)
    (hCoeff : C * (60 + T ^ 2) ≤ 5 * (u + c))
    (hPos : ∀ s ∈ Ioc 0 T, 0 ≤ 1 - u - (u - c) / 2 * s - C * s ^ 2) :
    (∫ s : ℝ in Ioi 0, w s * highIncidentFeeTest u c s) ≤
      ∫ s in (0 : ℝ)..T, w s * (1 - u - (u - c) / 2 * s - C * s ^ 2) := by
  let Q (s : ℝ) := 1 - u - (u - c) / 2 * s - C * s ^ 2
  have hRaw (s : ℝ) (hs : 0 < s) (hsT : s ≤ T) : highIncidentFeeRaw u c s ≤ Q s :=
    incidentFee_raw_le_poly hu hc hCoeff hs hsT
  have hI : IntegrableOn (fun s => w s * highIncidentFeeTest u c s) (Ioi 0) := by
    apply (hw.const_mul (1 + c)).mono'
      (hw.aestronglyMeasurable.mul (highIncidentFee_measurable u c).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    change ‖w s * highIncidentFeeTest u c s‖ ≤ (1 + c) * w s
    have hT₀ : 0 ≤ highIncidentFeeTest u c s := le_max_left _ _
    rw [Real.norm_of_nonneg (mul_nonneg (hw₀ s hs) hT₀),mul_comm (1 + c)]
    exact mul_le_mul_of_nonneg_left (highIncidentFee_le hs hu hc) (hw₀ s hs)
  have hSet : Ioc (0 : ℝ) T ⊆ Ioi 0 := fun _ hs => hs.1
  have hJ : IntegrableOn (fun s => w s * Q s) (Ioc 0 T) := by
    have hQ : Continuous Q := by unfold Q; fun_prop
    have hB : 0 ≤ (u - c) / 2 := by linarith only [hcu]
    have hBound : ∀ᵐ s ∂volume.restrict (Ioc 0 T), ‖Q s‖ ≤ 1 - u + |C| * T ^ 2 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      rw [Real.norm_of_nonneg (hPos s hs)]
      have hSq := pow_le_pow_left₀ hs.1.le hs.2 2
      have hAbs := (mul_le_mul_of_nonneg_right (neg_le_abs C) (sq_nonneg s)).trans
        (mul_le_mul_of_nonneg_left hSq (abs_nonneg C))
      nlinarith only [hAbs,mul_nonneg hB hs.1.le]
    simpa only [mul_comm] using (hw.mono_set hSet).bdd_mul hQ.measurable.aestronglyMeasurable hBound
  rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi hSet ?_,
    intervalIntegral.integral_of_le hT.le]
  · exact setIntegral_mono_on (hI.mono_set hSet) hJ measurableSet_Ioc (fun s hs =>
      mul_le_mul_of_nonneg_left (max_le (hPos s hs) (hRaw s hs.1 hs.2)) (hw₀ s hs.1))
  · intro s hs
    have h := highIncidentFee_antitone hc hcu (mem_Ioi.mpr hT) hs.1 (le_of_not_ge fun hh => hs.2 ⟨hs.1,hh⟩)
    have h0 : highIncidentFeeTest u c T = 0 := max_eq_left hCut
    rw [h0] at h
    rw [le_antisymm h (le_max_left _ _),mul_zero]

theorem highIncidentFee_one_third_lt :
    (∫ s : ℝ in Ioi 0, highIncidentFeeWeight s * highIncidentFeeTest (1 / 3) (5 / 24) s) < 9 / 20 := by
  have hCut : highIncidentFeeRaw (1 / 3) (5 / 24) 4 ≤ 0 := by
    have h := incidentFee_raw_le_poly (C := 5 / 192) (T := 4)
      (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (0 : ℝ) ≤ 5 / 24)
      (by norm_num) (by norm_num : (0 : ℝ) < 4) le_rfl
    linarith only [h]
  have h := incidentFee_integral_le_poly (C := 5 / 192) (T := 4)
    (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (0 : ℝ) ≤ 5 / 24)
    (by norm_num) highIncidentFeeWeight_integrable (fun s hs => mul_nonneg hs.le (Real.exp_pos _).le)
    (by norm_num) hCut (by norm_num) (by
      intro s hs
      have hSq := pow_le_pow_left₀ hs.1.le hs.2 2
      linarith only [hs.2,hSq])
  rw [exp_poly_fee_integral] at h
  have hE : Real.exp (-4) < 1 / 32 := by
    rw [Real.exp_neg,one_div]
    apply inv_strictAnti₀ (by norm_num)
    have h4 := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 4 by norm_num) 6
    norm_num [Finset.sum_range_succ,Nat.factorial] at h4
    linarith only [h4]
  linarith only [h,hE]

theorem highIncidentFee_one_fourth_lt :
    (∫ s : ℝ in Ioi 0, highIncidentFeeWeight s * highIncidentFeeTest (1 / 4) (1 / 8) s) < 17 / 32 := by
  have hCut : highIncidentFeeRaw (1 / 4) (1 / 8) (9 / 2) ≤ 0 := by
    have hH := highIncident_head_lower (s := 9 / 2) (D := 20 / 321) (by norm_num) (by norm_num)
    unfold highIncidentFeeRaw
    linarith only [hH]
  have h := incidentFee_integral_le_poly (C := 1 / 48) (T := 9 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (0 : ℝ) ≤ 1 / 8)
    (by norm_num) highIncidentFeeWeight_integrable (fun s hs => mul_nonneg hs.le (Real.exp_pos _).le)
    (by norm_num) hCut (by norm_num) (by
      intro s hs
      have hSq := pow_le_pow_left₀ hs.1.le hs.2 2
      linarith only [hs.2,hSq])
  rw [exp_poly_fee_integral] at h
  have hE : Real.exp (-(9 / 2)) < 1 / 64 := by
    rw [Real.exp_neg,one_div]
    apply inv_strictAnti₀ (by norm_num)
    have h3 := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 3 / 2 by norm_num) 4
    norm_num [Finset.sum_range_succ,Nat.factorial] at h3
    have h4 : (4 : ℝ) < Real.exp (3 / 2) := (by norm_num : (4 : ℝ) < _).trans_le h3
    rw [show (9 / 2 : ℝ) = (3 : ℕ) * (3 / 2 : ℝ) by norm_num,Real.exp_nat_mul]
    exact (by norm_num : (64 : ℝ) = 4 ^ 3).trans_lt (pow_lt_pow_left₀ h4 (by norm_num) (by decide))
  linarith only [h,hE]

end ACS12.GammaMeasure

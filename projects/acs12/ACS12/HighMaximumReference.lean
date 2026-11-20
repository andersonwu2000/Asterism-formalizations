import ACS12.HighMaximumLaw
import ACS12.PressureFeePade
import ACS12.PressureGeneralStress
import ACS12.PressureLikelihood

/-! The full maximum-ray fee under the exact and elementary reference laws. -/
namespace ACS12.GammaMeasure

open Set Filter MeasureTheory CenteredCircle.AllN

noncomputable def maximumFeeShape (s : ℝ) : ℝ := s * Real.exp s / (Real.exp s - 1) ^ 2

theorem maximumFeeShape_pos {s : ℝ} (hs : 0 < s) : 0 < maximumFeeShape s :=
  div_pos (mul_pos hs (Real.exp_pos _)) (sq_pos_of_pos (expTail_den_pos hs))

theorem maximumFeeShape_le {s : ℝ} (hs : 0 < s) : maximumFeeShape s ≤ s⁻¹ := by
  have h := mul_le_mul_of_nonneg_left (Pressure.bose_slope_le_inv_sq hs) hs.le
  convert h using 1
  · unfold maximumFeeShape
    ring
  · field_simp [hs.ne']

theorem maximumFeeShape_antitone : AntitoneOn maximumFeeShape (Ioi 0) := by
  have hD (s : ℝ) (hs : 0 < s) : HasDerivAt maximumFeeShape
      (Real.exp s * ((1 - s) * Real.exp s - (1 + s)) / (Real.exp s - 1) ^ 3) s := by
    have hE := Real.hasDerivAt_exp s
    convert ((hasDerivAt_id s).mul hE).div ((hE.sub_const 1).pow 2)
      (pow_ne_zero _ (expTail_den_pos hs).ne') using 1
    simp only [id_eq,Pi.pow_apply,Pi.mul_apply,one_mul,Nat.reduceSub,pow_one]
    field_simp [(expTail_den_pos hs).ne']
    ring
  apply antitoneOn_of_deriv_nonpos (convex_Ioi _)
  · exact fun s hs => (hD s hs).continuousAt.continuousWithinAt
  · exact fun s hs => (hD s (interior_subset hs)).differentiableAt.differentiableWithinAt
  · intro s hs
    have hs₀ : 0 < s := interior_subset hs
    rw [(hD s hs₀).deriv]
    have h := mul_lt_mul_of_pos_right (Real.add_one_lt_exp (neg_ne_zero.mpr hs₀.ne')) (Real.exp_pos s)
    rw [← Real.exp_add,neg_add_cancel,Real.exp_zero] at h
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith only [h,hs₀]))
      (pow_nonneg (expTail_den_pos hs₀).le _)

noncomputable def maximumRefWeight (θ c s : ℝ) : ℝ :=
  s * Real.exp (-s) * (s ^ 2 + c) ^ θ

theorem maximumRefWeight_pos {θ c s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    0 < maximumRefWeight θ c s := by unfold maximumRefWeight; positivity

theorem maximumRefWeight_integrable {θ c : ℝ} (hθ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (hc : 0 < c) :
    IntegrableOn (maximumRefWeight θ c) (Ioi 0) ∧
      IntegrableOn (fun s => maximumRefWeight θ c s * maximumFeeShape s) (Ioi 0) := by
  let F := maximumRefWeight θ c
  let P (s : ℝ) := s ^ 2 + c
  have hPow (s : ℝ) : P s ^ θ ≤ 1 + P s := by
    have hP : 0 < P s := add_pos_of_nonneg_of_pos (sq_nonneg s) hc
    rcases le_total (P s) 1 with h | h
    · have h' := Real.rpow_le_rpow_of_exponent_ge hP h hθ
      rw [Real.rpow_zero] at h'
      exact h'.trans (le_add_of_nonneg_right hP.le)
    · have h' := Real.rpow_le_rpow_of_exponent_le h hθ₁
      rw [Real.rpow_one] at h'
      exact h'.trans (le_add_of_nonneg_left zero_le_one)
  have hF : Measurable F := by unfold F maximumRefWeight; fun_prop
  have hJ : Measurable maximumFeeShape := by unfold maximumFeeShape; fun_prop
  have hI (n : ℕ) : IntegrableOn (fun s : ℝ => s ^ n * Real.exp (-s)) (Ioi 0) := by
    simpa only [mul_one] using expMoment_nat_integrable n zero_lt_one
  constructor
  · apply ((hI 3).add ((hI 1).const_mul (1 + c))).mono' hF.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0 < s := hs
    rw [Real.norm_of_nonneg (maximumRefWeight_pos (θ := θ) hc hs₀).le]
    have h := mul_le_mul_of_nonneg_left (hPow s) (mul_nonneg hs₀.le (Real.exp_pos (-s)).le)
    change _ ≤ s ^ 3 * Real.exp (-s) + (1 + c) * (s ^ (1 : ℕ) * Real.exp (-s))
    dsimp only [maximumRefWeight,P] at h ⊢
    simp only [pow_one]
    nlinarith only [h]
  · apply ((hI 2).add ((hI 0).const_mul (1 + c))).mono' (hF.mul hJ).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0 < s := hs
    rw [Real.norm_of_nonneg (mul_nonneg (maximumRefWeight_pos (θ := θ) hc hs₀).le (maximumFeeShape_pos hs₀).le)]
    have h := mul_le_mul_of_nonneg_left (maximumFeeShape_le hs₀) (maximumRefWeight_pos (θ := θ) hc hs₀).le
    have hE : F s * s⁻¹ = Real.exp (-s) * P s ^ θ := by unfold F maximumRefWeight P; field_simp [hs₀.ne']
    change _ ≤ s ^ 2 * Real.exp (-s) + (1 + c) * (s ^ (0 : ℕ) * Real.exp (-s))
    rw [show maximumRefWeight θ c s = F s by rfl,hE] at h
    exact h.trans ((mul_le_mul_of_nonneg_left (hPow s) (Real.exp_pos _).le).trans_eq
      (by simp only [P,pow_zero,one_mul]; ring))

noncomputable def maximumRefFee (θ c : ℝ) : ℝ :=
  (∫ s : ℝ in Ioi 0, maximumRefWeight θ c s * maximumFeeShape s) /
    (∫ s : ℝ in Ioi 0, maximumRefWeight θ c s)

theorem maximumRefWeight_integral_pos {θ c : ℝ} (hθ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (hc : 0 < c) :
    0 < ∫ s : ℝ in Ioi 0, maximumRefWeight θ c s := by
  letI : NeZero (volume.restrict (Ioi (0 : ℝ))) := ⟨positiveHalfLine_ne_zero⟩
  have h := integral_strict_of_ae_lt (volume.restrict (Ioi (0 : ℝ))) (integrable_zero ℝ ℝ _)
    (maximumRefWeight_integrable hθ hθ₁ hc).1 (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact maximumRefWeight_pos hc hs)
  simpa only [integral_zero] using h

theorem maximumRefFee_mono_scale {θ c d : ℝ} (hθ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (hc : 0 < c) (hcd : c ≤ d) :
    maximumRefFee θ c ≤ maximumRefFee θ d := by
  have hd := hc.trans_le hcd
  obtain ⟨hC,hCJ⟩ := maximumRefWeight_integrable hθ hθ₁ hc
  obtain ⟨hD,hDJ⟩ := maximumRefWeight_integrable hθ hθ₁ hd
  have hRat (s : ℝ) (hs : 0 < s) : maximumRefWeight θ c s / maximumRefWeight θ d s =
      ((s ^ 2 + c) / (s ^ 2 + d)) ^ θ := by
    rw [Real.div_rpow (by positivity : 0 ≤ s ^ 2 + c) (by positivity : 0 ≤ s ^ 2 + d)]
    unfold maximumRefWeight
    exact mul_div_mul_left _ _ (mul_pos hs (Real.exp_pos _)).ne'
  have hM : MonotoneOn (fun s => maximumRefWeight θ c s / maximumRefWeight θ d s) (Ioi 0) := by
    intro x hx y hy hxy
    change maximumRefWeight θ c x / maximumRefWeight θ d x ≤ maximumRefWeight θ c y / maximumRefWeight θ d y
    rw [hRat x hx,hRat y hy]
    apply Real.rpow_le_rpow (by positivity) _ hθ
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hSq := pow_le_pow_left₀ (show 0 < x from hx).le hxy 2
    nlinarith only [mul_nonneg (sub_nonneg.mpr hSq) (sub_nonneg.mpr hcd)]
  have h := Pressure.likelihood_test_anti hD hC hDJ hCJ (fun _ hs => maximumRefWeight_pos hd hs) hM maximumFeeShape_antitone
  exact (div_le_div_iff₀ (maximumRefWeight_integral_pos hθ hθ₁ hc)
    (maximumRefWeight_integral_pos hθ hθ₁ hd)).mpr h

noncomputable def maximumActualFee (p L : ℝ) : ℝ :=
  (∫ s : ℝ in Ioi 0, imageDensity p L s * Real.exp (-s) * maximumFeeShape s) / imagePotential p L 1

theorem maximumActualFee_integrable {p L : ℝ} (hp : 0 < p) (hL : 0 < L) :
    IntegrableOn (fun s => imageDensity p L s * Real.exp (-s) * maximumFeeShape s) (Ioi 0) := by
  obtain ⟨B,hB,hBound⟩ := Pressure.imageDensity_linear_exp_bound hp hL (ε := 1 / 2) (by norm_num)
  have hM : Measurable (fun s => imageDensity p L s * Real.exp (-s) * maximumFeeShape s) := by
    exact ((continuous_imageDensity hp hL).measurable.mul (by fun_prop)).mul (by unfold maximumFeeShape; fun_prop)
  have hI : IntegrableOn (fun s : ℝ => Real.exp (-s * (1 / 2))) (Ioi 0) := by
    simpa only [pow_zero,one_mul] using expMoment_nat_integrable 0 (c := 1 / 2) (by norm_num)
  apply (hI.const_mul B).mono' hM.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs₀ : 0 < s := hs
  have hN : 0 ≤ imageDensity p L s * Real.exp (-s) * maximumFeeShape s := by
    exact mul_nonneg (mul_nonneg (imageDensity_pos hp hL hs₀).le (Real.exp_pos _).le) (maximumFeeShape_pos hs₀).le
  rw [Real.norm_of_nonneg hN]
  have h := mul_le_mul (hBound s hs₀) (maximumFeeShape_le hs₀)
    (maximumFeeShape_pos hs₀).le (by positivity)
  have h' := mul_le_mul_of_nonneg_right h (Real.exp_pos (-s)).le
  have hE : (B * s * Real.exp ((1 / 2) * s)) * s⁻¹ * Real.exp (-s) = B * Real.exp (-s * (1 / 2)) := by
    have hExp : Real.exp ((1 / 2) * s) * Real.exp (-s) = Real.exp (-s * (1 / 2)) := by rw [← Real.exp_add]; congr 1; ring
    calc
      _ = B * (Real.exp ((1 / 2) * s) * Real.exp (-s)) := by field_simp [hs₀.ne'] <;> ring
      _ = _ := by rw [hExp]
  rw [hE] at h'
  simpa only [mul_right_comm (imageDensity p L s)] using h'

theorem maximumActualFee_le_reference {p L : ℝ} (hp : 2 ≤ p) (hP : p ≤ 4) (hL : 2 < L) :
    maximumActualFee p L ≤ maximumRefFee ((p - 2) / 2) (10) := by
  let θ := (p - 2) / 2
  let c := maximumLawScale L
  let W := maximumRefWeight θ c
  let V (s : ℝ) := imageDensity p L s * Real.exp (-s)
  have hp₀ : 0 < p := by linarith only [hp]
  have hL₀ : 0 < L := by linarith only [hL]
  have hc := maximumLawScale_pos hL₀
  have hθ : 0 ≤ θ := div_nonneg (sub_nonneg.mpr hp) (by norm_num)
  have hθ₁ : θ ≤ 1 := by unfold θ; linarith only [hP]
  have hC : c ≤ 10 := by
    have hPi := pow_lt_pow_left₀ Real.pi_lt_d6 Real.pi_pos.le (by decide : 2 ≠ 0)
    have hL₂ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hL.le 2
    unfold c maximumLawScale
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hL₀)).mpr
    nlinarith only [hPi,hL₂]
  obtain ⟨hW,hWJ⟩ := maximumRefWeight_integrable hθ hθ₁ hc
  have hV : IntegrableOn V (Ioi 0) := by simpa only [V,mul_one] using imagePotential_integrable hp₀ hL₀ zero_lt_one
  have hRatio : MonotoneOn (fun s => V s / W s) (Ioi 0) := by
    have hE (s : ℝ) : V s / W s = imageDensity p L s / (s * (s ^ 2 + c) ^ θ) := by
      unfold V W maximumRefWeight
      have he : s * Real.exp (-s) * (s ^ 2 + c) ^ θ = (s * (s ^ 2 + c) ^ θ) * Real.exp (-s) := by ring
      rw [he,mul_div_mul_right _ _ (Real.exp_ne_zero _)]
    intro x hx y hy hxy
    change V x / W x ≤ V y / W y
    rw [hE x,hE y]
    exact maximumLaw_imageRatio_mono hp hP hL₀ hx hy hxy
  have h := Pressure.likelihood_test_anti hW hV hWJ (maximumActualFee_integrable hp₀ hL₀)
    (fun _ hs => maximumRefWeight_pos hc hs) hRatio maximumFeeShape_antitone
  have hEq : (∫ s : ℝ in Ioi 0, V s) = imagePotential p L 1 := by simp only [V,imagePotential,mul_one]
  rw [hEq] at h
  have hC' : maximumActualFee p L ≤ maximumRefFee θ c :=
    (div_le_div_iff₀ (imagePotential_pos hp₀ hL₀ zero_lt_one)
      (maximumRefWeight_integral_pos hθ hθ₁ hc)).mpr h
  exact hC'.trans (maximumRefFee_mono_scale hθ hθ₁ hc hC)

end ACS12.GammaMeasure

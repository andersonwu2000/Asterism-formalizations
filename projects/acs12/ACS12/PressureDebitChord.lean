import ACS12.PressureCanonicalData
import ACS12.PressureHalfPath

/-! The complete canonical signed-debit envelope and its chord. -/
namespace ACS12.Pressure

open Set

noncomputable def pressureContrastCap : ℝ := Real.log 4

theorem pressureContrastCap_lt : pressureContrastCap < canonicalV := by
  have h := pressure_log16_lt_cap
  rw [show (16 : ℝ) = 4 * 4 by norm_num,Real.log_mul (by norm_num) (by norm_num)] at h
  unfold pressureContrastCap canonicalV
  linarith only [h]

private theorem pressureContrastCap_lower : (1386 / 1000 : ℝ) < pressureContrastCap := by
  unfold pressureContrastCap
  rw [show (4 : ℝ) = 2 * 2 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
  linarith only [Real.log_two_gt_d9]

private noncomputable def debitRatio (v : ℝ) : ℝ := (1 + v ^ 2 / 10) / (1 + (887 / 3920) * v ^ 2)
private noncomputable def debitTailSlope : ℝ := 487 / (27000 * pressureContrastCap)
private noncomputable def debitTail (v : ℝ) : ℝ := 1 / 27 - debitTailSlope * v

noncomputable def originalDebitEnvelope (v : ℝ) : ℝ :=
  (45 / 1568) * Real.exp ((171 / 70) * v) * debitRatio v * debitTail v

noncomputable def canonicalDebit (v : ℝ) : ℝ := (21 / 5) * originalDebitEnvelope v

private theorem debitTail_far : debitTail pressureContrastCap = 513 / 27000 := by
  have h : 0 < pressureContrastCap := (by norm_num : (0 : ℝ) < 1386 / 1000).trans pressureContrastCap_lower
  unfold debitTail debitTailSlope
  field_simp [h.ne']
  ring

private theorem debitTail_pos {v : ℝ} (hv : v ≤ pressureContrastCap) : 0 < debitTail v := by
  have hL : 0 < pressureContrastCap := (by norm_num : (0 : ℝ) < 1386 / 1000).trans pressureContrastCap_lower
  have hS : 0 ≤ debitTailSlope := by unfold debitTailSlope; positivity
  have h := mul_le_mul_of_nonneg_left hv hS
  have hE := debitTail_far
  unfold debitTail at hE ⊢
  linarith only [h,hE]

private noncomputable def debitSlopeH (v : ℝ) : ℝ :=
  2 * (99 / 784) * v / ((1 + v ^ 2 / 10) * (1 + (887 / 3920) * v ^ 2))
private noncomputable def debitSlopeS (v : ℝ) : ℝ := debitTailSlope / debitTail v
private noncomputable def debitLogSlope (v : ℝ) : ℝ := 171 / 70 - debitSlopeH v - debitSlopeS v

private theorem debitRatio_deriv (v : ℝ) :
    HasDerivAt debitRatio (-(debitRatio v * debitSlopeH v)) v := by
  have h := hasDerivAt_id v
  have h₁ := ((h.pow 2).div_const 10).const_add 1
  have h₂ := ((h.pow 2).const_mul (887 / 3920 : ℝ)).const_add 1
  have hD : 1 + (887 / 3920 : ℝ) * v ^ 2 ≠ 0 := by positivity
  convert h₁.div h₂ hD using 1
  norm_num [id_eq,debitRatio,debitSlopeH]
  field_simp [(show 1 + v ^ 2 / 10 ≠ 0 by positivity),(show 1 + (887 / 3920 : ℝ) * v ^ 2 ≠ 0 by positivity)]
  ring

private theorem debitTail_deriv (v : ℝ) : HasDerivAt debitTail (-debitTailSlope) v := by
  simpa only [id_eq,mul_one,zero_sub] using (hasDerivAt_const v (1 / 27 : ℝ)).sub
    ((hasDerivAt_id v).const_mul debitTailSlope)

private theorem canonicalDebit_deriv (v : ℝ) (hv : v ≤ pressureContrastCap) :
    HasDerivAt canonicalDebit (canonicalDebit v * debitLogSlope v) v := by
  have hE := (((hasDerivAt_id v).const_mul (171 / 70 : ℝ)).exp).const_mul (45 / 1568 : ℝ)
  convert ((hE.mul (debitRatio_deriv v)).mul (debitTail_deriv v)).const_mul (21 / 5 : ℝ) using 1
  simp only [id_eq,mul_one,canonicalDebit,originalDebitEnvelope,debitLogSlope,debitSlopeS,Pi.mul_apply]
  field_simp [(debitTail_pos hv).ne']
  ring

private theorem debitSlopeH_deriv_bound {v : ℝ} (hv : 0 ≤ v) :
    ∃ h, HasDerivAt debitSlopeH h v ∧ h ≤ 13 / 50 := by
  let D (x : ℝ) := (1 + x ^ 2 / 10) * (1 + (887 / 3920) * x ^ 2)
  let d := (v / 5) * (1 + (887 / 3920) * v ^ 2) + (1 + v ^ 2 / 10) * ((887 / 1960) * v)
  let c : ℝ := 2 * (99 / 784)
  have hD : 0 < D v := by unfold D; positivity
  have h := hasDerivAt_id v
  have hD' : HasDerivAt D d v := by
    convert (((h.pow 2).div_const 10).const_add 1).mul (((h.pow 2).const_mul (887 / 3920 : ℝ)).const_add 1) using 1
    norm_num [id_eq,d]
    ring
  have hNum : HasDerivAt (fun x => c * x) c v := by simpa only [id_eq,mul_one] using h.const_mul c
  refine ⟨(c * D v - c * v * d) / D v ^ 2,hNum.div hD' hD.ne',?_⟩
  have hNon : 0 ≤ c * v * d := by unfold c d; positivity
  have hD₁ : 1 ≤ D v := by
    have hA : 1 ≤ 1 + v ^ 2 / 10 := le_add_of_nonneg_right (by positivity)
    have hB : 1 ≤ 1 + (887 / 3920 : ℝ) * v ^ 2 := le_add_of_nonneg_right (by positivity)
    exact hB.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hA (zero_le_one.trans hB))
  have hLe : c * D v ≤ (13 / 50) * D v ^ 2 := by
    have h' := mul_le_mul_of_nonneg_right hD₁ hD.le
    have hC : c ≤ 13 / 50 := by norm_num [c]
    have h'' := mul_le_mul_of_nonneg_right hC hD.le
    nlinarith only [h',h'']
  apply (div_le_iff₀ (sq_pos_of_pos hD)).mpr
  exact (sub_le_self _ hNon).trans hLe

private theorem debitSlopeS_deriv {v : ℝ} (hv : v ≤ pressureContrastCap) :
    HasDerivAt debitSlopeS (debitSlopeS v ^ 2) v := by
  convert (hasDerivAt_const v debitTailSlope).div (debitTail_deriv v) (debitTail_pos hv).ne' using 1
  simp only [zero_mul,zero_sub]
  unfold debitSlopeS
  rw [div_pow]
  ring

private theorem debitLogSlope_bounds {v : ℝ} (hV : v ≤ pressureContrastCap) :
    27 / 20 < debitLogSlope v ∧ 0 ≤ debitSlopeS v ∧ debitSlopeS v ≤ 7 / 10 := by
  have hL : 0 < pressureContrastCap := (by norm_num : (0 : ℝ) < 1386 / 1000).trans pressureContrastCap_lower
  have hV' : v ≤ 7 / 5 := hV.trans (pressureContrastCap_lt.le.trans (by norm_num [canonicalV]))
  have hH : debitSlopeH v ≤ 99 / 280 := by
    unfold debitSlopeH
    apply (div_le_iff₀ (by positivity)).mpr
    have hV₂ := sq_nonneg v
    have hV₄ := sq_nonneg (v ^ 2)
    nlinarith only [hV',hV₂,hV₄]
  have hS₀ : 0 ≤ debitSlopeS v := by unfold debitSlopeS debitTailSlope; positivity [debitTail_pos hV]
  have hST : (513 / 27000 : ℝ) ≤ debitTail v := by
    rw [← debitTail_far]
    unfold debitTail
    have h := mul_le_mul_of_nonneg_left hV (show 0 ≤ debitTailSlope by unfold debitTailSlope; positivity)
    linarith only [h]
  have hS : debitSlopeS v ≤ 7 / 10 := by
    unfold debitSlopeS
    apply (div_le_iff₀ (debitTail_pos hV)).mpr
    have hB : debitTailSlope ≤ (7 / 10) * (513 / 27000) := by
      unfold debitTailSlope
      apply (div_le_iff₀ (by positivity)).mpr
      linarith only [pressureContrastCap_lower]
    linarith only [hB,hST]
  exact ⟨by unfold debitLogSlope; linarith only [hH,hS],hS₀,hS⟩

theorem originalDebitEnvelope_pos {v : ℝ} (hv : v ≤ pressureContrastCap) :
    0 < originalDebitEnvelope v := by
  have h := debitTail_pos hv
  unfold originalDebitEnvelope debitRatio
  positivity

theorem originalDebitEnvelope_mono : MonotoneOn originalDebitEnvelope (Icc 0 pressureContrastCap) := by
  have hM : MonotoneOn canonicalDebit (Icc 0 pressureContrastCap) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun x hx => (canonicalDebit_deriv x hx.2).continuousAt.continuousWithinAt
    · exact fun x hx => (canonicalDebit_deriv x (interior_subset hx).2).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' := interior_subset hx
      rw [(canonicalDebit_deriv x hx'.2).deriv]
      have hE := originalDebitEnvelope_pos hx'.2
      have hL := (debitLogSlope_bounds hx'.2).1
      unfold canonicalDebit
      exact mul_nonneg (mul_nonneg (by norm_num) hE.le) (by linarith only [hL])
  intro x hx y hy hxy
  exact (mul_le_mul_iff_right₀ (by norm_num : (0 : ℝ) < 21 / 5)).mp (hM hx hy hxy)

theorem canonicalDebit_convex : ConvexOn ℝ (Icc 0 pressureContrastCap) canonicalDebit := by
  let F (x : ℝ) := canonicalDebit x * debitLogSlope x
  have hF (x : ℝ) (hx : x ∈ Icc 0 pressureContrastCap) :
      ∃ d, HasDerivAt F d x ∧ 0 ≤ d := by
    obtain ⟨h,hD,hL⟩ := debitSlopeH_deriv_bound hx.1
    have hD' : HasDerivAt debitLogSlope (-h - debitSlopeS x ^ 2) x := by
      convert ((hasDerivAt_const x (171 / 70 : ℝ)).sub hD).sub (debitSlopeS_deriv hx.2) using 1
      simp only [zero_sub]
    have hF' := (canonicalDebit_deriv x hx.2).mul hD'
    refine ⟨_,hF',?_⟩
    have hP : 0 ≤ canonicalDebit x := by
      unfold canonicalDebit originalDebitEnvelope debitRatio
      positivity [debitTail_pos hx.2]
    obtain ⟨hA,hS,hSU⟩ := debitLogSlope_bounds hx.2
    have h₁ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27 / 20) hA.le 2
    have h₂ := pow_le_pow_left₀ hS hSU 2
    have h := mul_nonneg hP (show 0 ≤ debitLogSlope x ^ 2 - h - debitSlopeS x ^ 2 by linarith only [h₁,h₂,hL])
    linarith only [h]
  have hM : MonotoneOn F (Icc 0 pressureContrastCap) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro x hx
      obtain ⟨_,h,_⟩ := hF x hx
      exact h.continuousAt.continuousWithinAt
    · intro x hx
      obtain ⟨_,h,_⟩ := hF x (interior_subset hx)
      exact h.differentiableAt.differentiableWithinAt
    · intro x hx
      obtain ⟨_,h,hs⟩ := hF x (interior_subset hx)
      rwa [h.deriv]
  apply MonotoneOn.convexOn_of_deriv (convex_Icc _ _)
  · exact fun x hx => (canonicalDebit_deriv x hx.2).continuousAt.continuousWithinAt
  · exact fun x hx => (canonicalDebit_deriv x (interior_subset hx).2).differentiableAt.differentiableWithinAt
  · intro x hx y hy h
    rw [(canonicalDebit_deriv x (interior_subset hx).2).deriv,(canonicalDebit_deriv y (interior_subset hy).2).deriv]
    exact hM (interior_subset hx) (interior_subset hy) h

private theorem canonicalDebit_far_lt : canonicalDebit pressureContrastCap < debitChord pressureContrastCap := by
  have hL : 0 < pressureContrastCap := (by norm_num : (0 : ℝ) < 1386 / 1000).trans pressureContrastCap_lower
  have hE : Real.exp ((171 / 70) * pressureContrastCap) < 297 / 10 := by
    have h := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ (171 / 70) * (111 / 80) / 4)
      (by norm_num : ((171 / 70) * (111 / 80) / 4 : ℝ) ≤ 1) (n := 12) (by decide)
    have h' : Real.exp ((171 / 70) * (111 / 80) / 4) ≤ 2334 / 1000 := by
      norm_num [Finset.sum_range_succ,Nat.factorial] at h
      linarith only [h]
    have hA := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left pressureContrastCap_lt.le
      (by norm_num : (0 : ℝ) ≤ 171 / 70))
    unfold canonicalV at hA
    have hB := pow_le_pow_left₀ (Real.exp_pos _).le h' 4
    have hC : Real.exp ((171 / 70) * (111 / 80)) =
        Real.exp ((171 / 70) * (111 / 80) / 4) ^ (4 : ℕ) := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
    rw [hC] at hA
    exact hA.trans_lt (hB.trans_lt (by norm_num))
  have hR : debitRatio pressureContrastCap ≤ 832 / 1000 := by
    unfold debitRatio
    apply (div_le_iff₀ (by positivity)).mpr
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1386 / 1000) pressureContrastCap_lower.le 2
    nlinarith only [h]
  have hR₀ : 0 ≤ debitRatio pressureContrastCap := by unfold debitRatio; positivity
  have hP := mul_le_mul hE.le hR hR₀ (by norm_num : (0 : ℝ) ≤ 297 / 10)
  unfold canonicalDebit originalDebitEnvelope
  rw [debitTail_far]
  unfold debitChord
  linarith only [hP,pressureContrastCap_lower]

theorem canonicalDebit_le_chord {v : ℝ} (hv : 0 ≤ v) (hV : v ≤ pressureContrastCap) :
    canonicalDebit v ≤ debitChord v := by
  have hL : 0 < pressureContrastCap := (by norm_num : (0 : ℝ) < 1386 / 1000).trans pressureContrastCap_lower
  let b := v / pressureContrastCap
  have hb : 0 ≤ b := div_nonneg hv hL.le
  have hb₁ : b ≤ 1 := (div_le_one hL).mpr hV
  have hC := canonicalDebit_convex.2 ⟨le_rfl,hL.le⟩ ⟨hL.le,le_rfl⟩
    (sub_nonneg.mpr hb₁) hb (sub_add_cancel 1 b)
  have hE : (1 - b) * 0 + b * pressureContrastCap = v := by
    simp only [b,mul_zero,zero_add,div_mul_cancel₀ _ hL.ne']
  have hD : canonicalDebit 0 = 1 / 224 := by norm_num [canonicalDebit,originalDebitEnvelope,debitRatio,debitTail]
  simp only [smul_eq_mul,hE,hD] at hC
  have h := mul_le_mul_of_nonneg_left canonicalDebit_far_lt.le hb
  have hB : b * pressureContrastCap = v := div_mul_cancel₀ _ hL.ne'
  unfold debitChord at h ⊢
  nlinarith only [hC,h,hB]

end ACS12.Pressure

import ACS12.PressureLineDebit

/-! Compare the complete maximum debit with the decreasing test on the line law. -/
namespace ACS12.Pressure

open Set Filter MeasureTheory CenteredCircle.AllN
open GammaMeasure (imageDensity imageDensity_two imageDensity_pos imagePotential imagePotential_integrable
  imageDensity_div_lineDensity_strictMono lineDensity_pos)
open GammaDeficit (lineDensity lineDensity_exp_integral lineDensity_exp_integrable)

private noncomputable def expGap (x : ℝ) : ℝ := Real.exp x + Real.exp (-x) - 2

private theorem expGap_pos {x : ℝ} (hx : 0 < x) : 0 < expGap x := by
  have hE := Real.exp_pos x
  have hE' := Real.one_lt_exp_iff.mpr hx
  unfold expGap
  rw [Real.exp_neg]
  have hEq : Real.exp x + (Real.exp x)⁻¹ - 2 = (Real.exp x - 1) ^ 2 / Real.exp x := by
    field_simp [hE.ne']
    ring
  rw [hEq]
  exact div_pos (sq_pos_of_pos (sub_pos.mpr hE')) hE

private theorem expGap_slope_gt {x : ℝ} (hx : 0 < x) :
    expGap x < x * (Real.exp x - Real.exp (-x)) := by
  let f (x : ℝ) := x * (Real.exp x - Real.exp (-x)) - expGap x
  have hD (x : ℝ) : HasDerivAt f (x * (Real.exp x + Real.exp (-x))) x := by
    have h₁ := (Real.hasDerivAt_exp x).sub ((hasDerivAt_id x).neg.exp)
    have h₂ := ((Real.hasDerivAt_exp x).add ((hasDerivAt_id x).neg.exp)).sub_const 2
    convert ((hasDerivAt_id x).mul h₁).sub h₂ using 1
    simp only [id_eq,Pi.neg_apply,Pi.sub_apply,one_mul]
    ring
  have hM : StrictMonoOn f (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
    · exact fun x _ => (hD x).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hD x).deriv]
      exact mul_pos hx (add_pos (Real.exp_pos _) (Real.exp_pos _))
  have h := hM (mem_Ici.mpr (le_refl (0 : ℝ))) (mem_Ici.mpr hx.le) hx
  have h0 : f 0 = 0 := by norm_num [f,expGap]
  rw [h0] at h
  exact sub_pos.mp h

private noncomputable def pressureDebitTest (Q s : ℝ) : ℝ :=
  s * pressureBose Q s ^ 2 * Real.exp (s * Q)

private theorem pressureDebitTest_eq {Q s : ℝ} (hQ : 0 < Q) (hs : 0 < s) :
    pressureDebitTest Q s = Q ^ 2 / (expGap (Q * s) / s) := by
  have hX := mul_pos hs hQ
  have hA := Real.exp_pos (s * Q)
  have hB := expTail_den_pos hX
  have hG : expGap (s * Q) = (Real.exp (s * Q) - 1) ^ 2 / Real.exp (s * Q) := by
    unfold expGap
    rw [Real.exp_neg]
    field_simp [hA.ne']
    ring
  unfold pressureDebitTest
  rw [pressureBose_eq hQ hs,scaledExpTail,mul_comm Q s,hG]
  field_simp [hA.ne',hB.ne',pow_ne_zero 2 hB.ne',hs.ne']

private theorem pressureDebitTest_antitone {Q : ℝ} (hQ : 0 < Q) :
    AntitoneOn (pressureDebitTest Q) (Ioi 0) := by
  let f (s : ℝ) := expGap (Q * s) / s
  have hD (s : ℝ) (hs : 0 < s) :
      HasDerivAt f ((s * (Q * (Real.exp (Q * s) - Real.exp (-(Q * s)))) - expGap (Q * s)) / s ^ 2) s := by
    have hX := (hasDerivAt_id s).const_mul Q
    have h := ((hX.exp.add hX.neg.exp).sub_const 2).div (hasDerivAt_id s) hs.ne'
    convert h using 1
    simp only [id_eq,Pi.neg_apply,Pi.add_apply,mul_one,expGap]
    ring
  have hM : MonotoneOn f (Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi _)
    · exact fun s hs => (hD s hs).continuousAt.continuousWithinAt
    · exact fun s hs => (hD s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      have hs₀ : 0 < s := interior_subset hs
      rw [(hD s hs₀).deriv]
      have hE := expGap_slope_gt (mul_pos hQ hs₀)
      exact div_nonneg (by nlinarith only [hE]) (sq_nonneg _)
  intro s hs t ht hst
  rw [pressureDebitTest_eq hQ hs,pressureDebitTest_eq hQ ht]
  exact div_le_div_of_nonneg_left (sq_nonneg _) (div_pos (expGap_pos (mul_pos hQ hs)) hs) (hM hs ht hst)

theorem maximumDebit_le_boseDebit {p L Q : ℝ} (hp : 1 < p) (hp₂ : p ≤ 2) (hL : 0 < L) (hQ : 0 < Q) :
    maximumDebit p L Q ≤ Q * imagePotential p L Q * boseDebit p := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  let W := GammaMeasure.imageDensity p L
  let R := lineDensity p
  let E (s : ℝ) := Real.exp (-s * Q)
  let T := pressureDebitTest Q
  let f (s : ℝ) := R s * (s * pressureBose Q s ^ 2)
  let g (s : ℝ) := W s * E s
  let h (s : ℝ) := W s * (s * pressureBose Q s ^ 2)
  let k (s : ℝ) := R s * E s
  have hp₀ := zero_lt_one.trans hp
  have hf : Integrable f μ := lineMaximumDebit_integrable hp hQ
  have hg : Integrable g μ := imagePotential_integrable hp₀ hL hQ
  have hh : Integrable h μ := (maximumDebit_integrable hp₀ hL hQ).congr
    (Eventually.of_forall fun s => by dsimp only [h,W,pressureWeight]; ring)
  have hk : Integrable k μ := lineDensity_exp_integrable hp₀ hQ
  have hRat : MonotoneOn (fun s => W s / R s) (Ioi 0) := by
    rcases hp₂.eq_or_lt with rfl | h₂
    · intro s hs t ht hst
      have hR (u : ℝ) : lineDensity 2 u = u := by
        norm_num [lineDensity,Real.Gamma_two]
      simp only [W,R,imageDensity_two hL hs,imageDensity_two hL ht,hR,
        div_self (show s ≠ 0 from (show 0 < s from hs).ne'),div_self (show t ≠ 0 from (show 0 < t from ht).ne'),le_rfl]
    · exact (imageDensity_div_lineDensity_strictMono hp.le h₂ hL).monotoneOn
  have hOrdered (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (hST : s ≤ t) :
      0 ≤ f s * g t + f t * g s - h s * k t - h t * k s := by
    have hR₁ : 0 < R s := lineDensity_pos hp₀ hs
    have hR₂ : 0 < R t := lineDensity_pos hp₀ ht
    have hT := sub_nonneg.mpr (pressureDebitTest_antitone hQ hs ht hST)
    have hW := sub_nonneg.mpr (hRat hs ht hST)
    have hP : 0 ≤ R s * R t * E s * E t * (T s - T t) * (W t / R t - W s / R s) := by positivity
    have hE (x : ℝ) : E x * T x = x * pressureBose Q x ^ 2 := by
      have h : E x * Real.exp (x * Q) = 1 := by
        dsimp only [E]
        rw [← Real.exp_add,show -x * Q + x * Q = 0 by ring,Real.exp_zero]
      dsimp only [T,pressureDebitTest]
      linear_combination x * pressureBose Q x ^ 2 * h
    have hR : R s * R t * (W t / R t - W s / R s) = R s * W t - R t * W s := by
      field_simp [hR₁.ne',hR₂.ne']
    convert hP using 1
    calc
      _ = (R s * W t - R t * W s) *
          (E t * (s * pressureBose Q s ^ 2) - E s * (t * pressureBose Q t ^ 2)) := by
        dsimp only [f,g,h,k]
        ring
      _ = _ := by rw [← hR,← hE s,← hE t]; ring
  have hPair : ∀ᵐ s ∂μ, ∀ᵐ t ∂μ, 0 ≤ f s * g t + f t * g s - h s * k t - h t * k s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rcases le_total s t with hST | hTS
    · exact hOrdered s t hs ht hST
    · linarith only [hOrdered t s ht hs hTS]
  have hCmp := integral_product_comparison hf hg hh hk hPair
  have hH : (∫ s : ℝ, h s ∂μ) = maximumDebit p L Q := by
    unfold maximumDebit
    exact setIntegral_congr_fun measurableSet_Ioi (fun s _ => by dsimp only [h,W,pressureWeight]; ring)
  change _ * (∫ s : ℝ in Ioi 0, lineDensity p s * Real.exp (-s * Q)) ≤
    lineMaximumDebit p Q * imagePotential p L Q at hCmp
  have hPow : Q ^ (1 - p) = Q * Q ^ (-p) := by
    rw [show 1 - p = 1 + -p by ring,Real.rpow_add hQ,Real.rpow_one]
  rw [hH,lineDensity_exp_integral hp₀ hQ,lineMaximumDebit_eq hp hQ,hPow] at hCmp
  have hFinal : maximumDebit p L Q * Q ^ (-p) ≤
      (Q * imagePotential p L Q * boseDebit p) * Q ^ (-p) := hCmp.trans_eq (by ring)
  exact (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hQ (-p))).mp (by simpa only [mul_comm] using hFinal)

end ACS12.Pressure

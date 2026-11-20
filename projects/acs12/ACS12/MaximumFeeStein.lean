import ACS12.HighMaximumReference
import Mathlib.Analysis.SpecialFunctions.PolynomialExp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! A pointwise Stein certificate for the complete maximum-ray fee. -/
namespace ACS12.GammaMeasure

open Set Filter MeasureTheory Polynomial
open scoped Topology
open CenteredCircle.AllN

private noncomputable def feeSteinTrial (θ : ℝ) : ℝ[X] :=
  C (-1) - C (1/18+θ/10)*X + C (1/80+θ/30)*X^2

private noncomputable def feeSteinDerivative (θ s : ℝ) : ℝ :=
  let H := feeSteinTrial θ
  (((1-X)*H+X*H.derivative).eval s * Real.exp (-s)) * (s^2+10)^θ +
    ((C (2*θ)*X^2*H).eval s * Real.exp (-s)) * (s^2+10)^(θ-1)

private theorem feeStein_hasDerivAt (θ s : ℝ) :
    HasDerivAt (fun s => maximumRefWeight θ 10 s * (feeSteinTrial θ).eval s)
      (feeSteinDerivative θ s) s := by
  have hPos : 0 < s^2+(10:ℝ) := by positivity
  have h := hasDerivAt_id s
  have hP := ((h.pow 2).add_const 10).rpow_const (p := θ) (Or.inl hPos.ne')
  have hF := (((h.mul h.neg.exp).mul hP).mul ((feeSteinTrial θ).hasDerivAt s))
  convert hF using 1
  simp only [feeSteinDerivative, eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_X_pow,
    eval_one, id_eq, one_mul, Pi.neg_apply, Pi.pow_apply, Pi.mul_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  ring

private theorem feePolynomial_exp_integrable (P : ℝ[X]) :
    IntegrableOn (fun s : ℝ => P.eval s * Real.exp (-s)) (Ioi 0) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [eval_add, add_mul, Pi.add_apply] using hp.add hq
  | monomial n a =>
    simpa only [eval_monomial, mul_assoc, mul_one] using
      (expMoment_nat_integrable n (c := 1) zero_lt_one).const_mul a

private theorem feePolynomial_rpow_integrable (P : ℝ[X]) {r : ℝ} (hr : r ≤ 1) :
    IntegrableOn (fun s : ℝ => P.eval s * Real.exp (-s) * (s^2+10)^r) (Ioi 0) := by
  have hI := (feePolynomial_exp_integrable (P*(X^2+C 10))).norm
  have hM : Measurable fun s : ℝ => P.eval s * Real.exp (-s) * (s^2+10)^r := by fun_prop
  apply hI.mono' hM.aestronglyMeasurable
  filter_upwards with s
  have hPos : 0 < s^2+(10:ℝ) := by positivity
  have hPow := Real.rpow_le_rpow_of_exponent_le (show 1 ≤ s^2+(10:ℝ) by nlinarith [sq_nonneg s]) hr
  rw [Real.rpow_one] at hPow
  simp only [eval_mul,eval_add,eval_X_pow,eval_C]
  have hEq : P.eval s * (s^2+10) * Real.exp (-s) = P.eval s * Real.exp (-s) * (s^2+10) := by ring
  rw [hEq]
  simp only [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg hPos.le _), Real.norm_of_nonneg hPos.le]
  exact mul_le_mul_of_nonneg_left hPow (mul_nonneg (norm_nonneg _) (norm_nonneg _))

private theorem feeStein_integral_zero {θ : ℝ} (hθ : θ ≤ 1) :
    (∫ s in Ioi 0, feeSteinDerivative θ s) = 0 := by
  let H := feeSteinTrial θ
  let F (s : ℝ) := maximumRefWeight θ 10 s * H.eval s
  let P := X * H * (X^2+C 10)
  have hP : Tendsto (fun s : ℝ => ‖P.eval s / Real.exp s‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using P.tendsto_div_exp_atTop.norm
  have hTop : Tendsto F atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero' (Eventually.of_forall fun s => norm_nonneg _) ?_ hP
    filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs
    have hE := Real.exp_pos (-s)
    have hPos : 0 < s^2+(10:ℝ) := by positivity
    have hPow := Real.rpow_le_rpow_of_exponent_le (show 1 ≤ s^2+(10:ℝ) by nlinarith [sq_nonneg s]) hθ
    rw [Real.rpow_one] at hPow
    have hR := mul_le_mul_of_nonneg_left hPow (show 0 ≤ s*Real.exp (-s)*‖H.eval s‖ by positivity)
    unfold F maximumRefWeight P
    simp only [eval_mul, eval_add, eval_X, eval_X_pow, eval_C, div_eq_mul_inv, ← Real.exp_neg]
    rw [show s * H.eval s * (s^2+10) * Real.exp (-s) = s * Real.exp (-s) * (H.eval s*(s^2+10)) by ring,
      show s * Real.exp (-s) * (s^2+10)^θ * H.eval s = s * Real.exp (-s) * (H.eval s*(s^2+10)^θ) by ring]
    simp only [norm_mul, Real.norm_of_nonneg hs, Real.norm_of_nonneg hE.le,
      Real.norm_of_nonneg hPos.le, Real.norm_of_nonneg (Real.rpow_nonneg hPos.le _)]
    linarith only [hR]
  have hI : IntegrableOn (feeSteinDerivative θ) (Ioi 0) :=
    (feePolynomial_rpow_integrable ((1-X)*H+X*H.derivative) hθ).add
      (feePolynomial_rpow_integrable (C (2*θ)*X^2*H) (by linarith))
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (fun s _ => feeStein_hasDerivAt θ s) hI hTop
  simpa [F, maximumRefWeight] using h

private noncomputable def feeEnvelope (s : ℝ) : ℝ := 360/(s*(s^4+30*s^2+360))

private theorem feeShape_lt_envelope {s : ℝ} (hs : 0 < s) : maximumFeeShape s < feeEnvelope s := by
  let a (j : ℕ) := s ^ (2*(j+4)) / ((2*(j+4)).factorial : ℝ)
  have ha : HasSum a (Real.cosh s-(1+s^2/2+s^4/24+s^6/720)) := by
    simpa [a,Finset.sum_range_succ,Nat.factorial] using (hasSum_nat_add_iff' 4).mpr (Real.hasSum_cosh s)
  have hC : 0 < Real.cosh s-(1+s^2/2+s^4/24+s^6/720) :=
    ha.tsum_eq ▸ ha.summable.tsum_pos (fun j => by unfold a; positivity) 0 (by unfold a; positivity)
  have hC₀ : 0 < Real.cosh s-1 := by nlinarith only [hC, sq_nonneg s, pow_nonneg hs.le 4, pow_nonneg hs.le 6]
  have hD : 0 < s^4+30*s^2+360 := by positivity
  have hE : (Real.exp s-1)^2 = 2*Real.exp s*(Real.cosh s-1) := by
    rw [Real.cosh_eq,Real.exp_neg]
    field_simp [(Real.exp_pos s).ne']
    ring
  unfold maximumFeeShape feeEnvelope
  rw [hE, show s*Real.exp s/(2*Real.exp s*(Real.cosh s-1)) = s/(2*(Real.cosh s-1)) by
    field_simp [(Real.exp_pos s).ne',hC₀.ne']]
  apply (div_lt_div_iff₀ (by positivity) (mul_pos hs hD)).mpr
  linarith only [hC]

private theorem feeStein_residual_pos {θ s : ℝ} (hθ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (hs : 0 < s) :
    feeEnvelope s + ((feeSteinTrial θ).derivative.eval s + (feeSteinTrial θ).eval s *
      (1/s-1+2*θ*s/(s^2+10))) < (9/10)-θ/5 := by
  let D := s^4+30*s^2+360
  have hD : 0 < D := by unfold D; positivity
  have hP : 0 < s^2+(10:ℝ) := by positivity
  have hQuad₁ : 0 < 9*s^2-67*s+125 := by nlinarith only [sq_nonneg (18*s-67)]
  have hQuad₂ : 0 < 153*s^2-1290*s+2800 := by nlinarith only [sq_nonneg (306*s-1290)]
  have hQuad₃ : 0 < 680*s^2-2520*s+2880 := by nlinarith only [sq_nonneg (1360*s-2520)]
  have hQuad₄ : 0 < 12*s^2-81*s+160 := by nlinarith only [sq_nonneg (24*s-81)]
  have hQuad₅ : 0 < 12*s^2-105*s+232 := by nlinarith only [sq_nonneg (24*s-105)]
  have hθ' := sub_nonneg.mpr hθ₁
  have hEq : (9/10)-θ/5-(feeEnvelope s + ((feeSteinTrial θ).derivative.eval s +
      (feeSteinTrial θ).eval s * (1/s-1+2*θ*s/(s^2+10)))) =
      (s^4*(9*s^2-67*s+125)+s^2*(153*s^2-1290*s+2800)+(680*s^2-2520*s+2880))/(720*D) +
      θ*s^2*((1-θ)*(12*s^2-81*s+160)+θ*(12*s^2-105*s+232))/(360*(s^2+10)) := by
    simp only [feeEnvelope, feeSteinTrial, D, derivative_add, derivative_sub, derivative_mul,
      derivative_C, derivative_X, eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_X_pow, eval_zero, eval_one]
    norm_num
    field_simp [hs.ne',show s^4+30*s^2+360 ≠ 0 from hD.ne', hP.ne']
    <;> ring
  apply sub_pos.mp
  rw [hEq]
  positivity

private theorem feeSteinDerivative_factor {θ s : ℝ} (hs : 0 < s) :
    feeSteinDerivative θ s = maximumRefWeight θ 10 s *
      ((feeSteinTrial θ).derivative.eval s + (feeSteinTrial θ).eval s * (1/s-1+2*θ*s/(s^2+10))) := by
  have hP : 0 < s^2+(10:ℝ) := by positivity
  simp only [feeSteinDerivative,maximumRefWeight,eval_add,eval_sub,eval_mul,eval_one,eval_C,eval_X,eval_X_pow]
  rw [Real.rpow_sub_one hP.ne']
  field_simp [hs.ne',hP.ne']
  <;> ring

theorem maximumRefFee_lt_line {θ : ℝ} (hθ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    maximumRefFee θ 10 < (9/10)-θ/5 := by
  let W := maximumRefWeight θ 10
  let G := feeSteinDerivative θ
  let F (s : ℝ) := W s * maximumFeeShape s
  let c := (9/10 : ℝ)-θ/5
  let μ := volume.restrict (Ioi (0:ℝ))
  have hW := maximumRefWeight_integrable hθ hθ₁ (by norm_num : (0:ℝ) < 10)
  have hG : Integrable G μ :=
    (feePolynomial_rpow_integrable _ hθ₁).add (feePolynomial_rpow_integrable _ (by linarith : θ-1 ≤ 1))
  letI : NeZero μ := ⟨positiveHalfLine_ne_zero⟩
  have h := integral_strict_of_ae_lt μ (hW.2.add hG) (hW.1.const_mul c) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0 < s := hs
    have h := (add_lt_add_of_lt_of_le (feeShape_lt_envelope hs₀) le_rfl).trans (feeStein_residual_pos hθ hθ₁ hs₀)
    change F s + G s < c*W s
    unfold F G
    rw [feeSteinDerivative_factor hs₀,← mul_add,mul_comm c]
    exact mul_lt_mul_of_pos_left h (maximumRefWeight_pos (by norm_num) hs₀))
  change (∫ s, F s+G s ∂μ) < ∫ s, c*W s ∂μ at h
  rw [integral_add hW.2 hG, integral_const_mul, feeStein_integral_zero hθ₁, add_zero] at h
  exact (div_lt_iff₀ (maximumRefWeight_integral_pos hθ hθ₁ (by norm_num))).mpr h

end ACS12.GammaMeasure

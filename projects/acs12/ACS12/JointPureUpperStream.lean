import ACS12.JointPureUpperDensity
import ACS12.JointPureUpperK
import ACS12.JointPureBoseMoments

/-! The complete signed-stream bound for the pure upper diagonal. -/
namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaDeficit (lineDensity)

noncomputable def jointUnitValue (p mu : ℝ) : ℝ :=
  pureP p - (6 / 25) * pureQ p - jointPureLambda * (1 + pureP p) -
    mu * (2 * p + pureP p - pureQ p + (2 : ℝ) ^ (-p))

private noncomputable def jointUnitJ (p mu t : ℝ) : ℝ :=
  ∫ s : ℝ in Ioi 0, lineDensity p s * jointPureR mu 1 s * BoseShape.C (s * t)

theorem jointPureR_measurable (mu u : ℝ) : Measurable (jointPureR mu u) := by
  unfold jointPureR middleRightDensity middleA0 polyB
  fun_prop

theorem jointPureR_linear {mu u : ℝ} (hmu : 0 ≤ mu) (hmuU : mu ≤ 9 / 500)
    (hu : 0 < u) (hu₁ : u ≤ 1) (s : ℝ) (hs : 0 < s) :
    |jointPureR mu u s| ≤ 2 * s := by
  let X := Real.exp (-s)
  let Y := Real.exp (-s * u)
  let a := middleA u
  let g := middleRightDensity u s
  let b := polyB (u * s)
  have hX₀ : 0 < X := Real.exp_pos _
  have hX : 0 < 1 - X := expHead_den_pos hs
  have hX' : 1 - X ≤ s := by
    dsimp only [X]
    linarith only [Real.add_one_le_exp (-s)]
  have hY : 0 < Y := Real.exp_pos _
  have hY₁ : Y ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [mul_pos hs hu])
  have ha : 0 ≤ a := (middleA_pos hu hu₁).le
  have haU : a ≤ u := by unfold a middleA; nlinarith only [sq_nonneg u,hu]
  have hA := mul_le_mul_of_nonneg_left (show 1 - X ≤ 1 by linarith only [hX₀]) ha
  have hA₀ := mul_nonneg ha hX.le
  have hg : g = s * (u - a * (1 - X)) - (1 - X) := by
    dsimp only [g,a,X,middleRightDensity,middleA0,middleZ]
    ring
  have hG₁ := mul_nonneg hs.le (show 0 ≤ u - a * (1 - X) by linarith only [hA,haU])
  have hG₂ := mul_le_mul_of_nonneg_left (show u - a * (1 - X) ≤ 1 by linarith only [hA₀,hu₁]) hs.le
  have hB₀ : 0 ≤ b := (polyB_pos (mul_pos hu hs)).le
  have hBE : b = u * s - 1 + Y := by
    dsimp only [b, Y, polyB]
    rw [show -(u * s) = -s * u by ring]
  have hB : b ≤ s := by nlinarith only [hBE,hY₁,mul_le_mul_of_nonneg_right hu₁ hs.le]
  have hLam : 0 ≤ jointPureLambda := by norm_num [jointPureLambda]
  have h₁ := mul_le_mul_of_nonneg_left hB hLam
  have h₂ := mul_le_mul_of_nonneg_left
    ((mul_le_of_le_one_left hB₀ hY₁).trans hB) hmu
  have h₃ := mul_le_mul_of_nonneg_right hmuU hs.le
  have h₄ := mul_nonneg hLam hB₀
  have h₅ := mul_nonneg hmu (mul_nonneg hY.le hB₀)
  apply abs_le.mpr
  change -(2 * s) ≤ g - jointPureLambda * b - mu * Y * b ∧ g - jointPureLambda * b - mu * Y * b ≤ 2 * s
  dsimp only [jointPureLambda] at h₁ h₄ ⊢
  constructor <;> nlinarith only [hg,hX,hX',hG₁,hG₂,h₁,h₂,h₃,h₄,h₅,hs]

private theorem jointUnitJ_one_eq {p mu : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) :
    jointUnitJ p mu 1 = 1 + (6 / 25) * p + jointUnitValue p mu := by
  let F (s : ℝ) := lineDensity p s * outerR 1 s * BoseShape.C (s * 1)
  let B (s : ℝ) := lineDensity p s * polyB s * BoseShape.C s
  let E (s : ℝ) := lineDensity p s * polyB s * Real.exp (-s) * BoseShape.C s
  obtain ⟨B₀, hB₀, hB₁⟩ := outerR_linear_bound (show (0 : ℝ) < 1 from zero_lt_one)
  have hF : IntegrableOn F (Ioi 0) :=
    pureC_integrable_of_linear hp hp₂ zero_lt_one hB₀ (by
      unfold outerR middleRightDensity middleA0 polyB; fun_prop) hB₁
  have hBE : (∫ s : ℝ in Ioi 0, B s) = 1 + pureP p := by
    simpa only [B,pureP,Nat.cast_zero,mul_zero,neg_zero,Real.exp_zero,mul_one,zero_add,
      Nat.zero_add,Real.one_rpow,zero_mul,sub_zero] using pureBoseB_moment hp hp₂ 0
  have hB : IntegrableOn B (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [hBE]
    linarith only [pureP_nonneg hp]
  have hE : IntegrableOn E (Ioi 0) := shiftedBoseMoment_integrable hp hp₂
  have hEq (s : ℝ) : lineDensity p s * jointPureR mu 1 s * BoseShape.C (s * 1) =
      F s + (19 / 100 - jointPureLambda) * B s - mu * E s := by
    simp only [F,B,E,outerR,jointPureR,one_mul,mul_one]
    ring
  unfold jointUnitJ
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => hEq s)]
  change (∫ s : ℝ in Ioi 0, (F + (fun s => (19 / 100 - jointPureLambda) * B s)) s - mu * E s) = _
  rw [integral_sub (hF.add (hB.const_mul _)) (hE.const_mul mu)]
  change ((∫ s : ℝ in Ioi 0, F s + (19 / 100 - jointPureLambda) * B s) -
    ∫ s : ℝ in Ioi 0, mu * E s) = _
  rw [integral_add hF (hB.const_mul _), integral_const_mul, integral_const_mul, hBE]
  change outerJ p 1 + (19 / 100 - jointPureLambda) * (1 + pureP p) -
    mu * (∫ s : ℝ in Ioi 0, lineDensity p s * polyB s * Real.exp (-s) * BoseShape.C s) = _
  rw [outerJ_one_eq hp hp₂, pureBoseBX_moment hp hp₂, outerUnitValue, jointUnitValue, pureP, pureZ]
  ring

private theorem jointUnitJ_one_nonneg {p mu : ℝ} (hp : 1 ≤ p) (hmu : 0 ≤ mu) (hmuU : mu ≤ 9 / 500) :
    0 ≤ jointUnitJ p mu 1 := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs₀ : 0 < s := hs
  exact mul_nonneg (mul_nonneg (lineDensity_pos (zero_lt_one.trans_le hp) hs₀).le
    (jointPureR_one_bounds hmu hmuU hs₀).1.le) (BoseShape.C_pos (mul_pos hs₀ zero_lt_one)).le

private theorem jointUnitJ_scaled_le {p mu t : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hmu : 0 ≤ mu) (hmuU : mu ≤ 9 / 500) (ht : 0 < t) (ht₁ : t ≤ 1) :
    jointUnitJ p mu t ≤ t ^ (-(p + 2)) * jointUnitJ p mu 1 := by
  let R := jointPureR mu 1
  let f (s : ℝ) := R (s / t) * BoseShape.C s
  have hEq : jointUnitJ p mu t = t ^ (-p) * ∫ s : ℝ in Ioi 0, lineDensity p s * f s := by
    rw [← pureIntegral_scale ht f]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s _
    dsimp only [jointUnitJ, f, R]
    rw [mul_div_cancel_left₀ _ ht.ne', mul_comm t s, mul_assoc]
  have hB (s : ℝ) (hs : 0 < s) : |R s| ≤ s := by
    obtain ⟨hP,hS⟩ := jointPureR_one_bounds hmu hmuU hs
    rw [abs_of_nonneg hP.le]
    exact hS
  have hA : IntegrableOn (fun s => lineDensity p s * f s) (Ioi 0) := by
    have h := pureC_integrable_of_linear (f := fun s => R (s / t)) hp hp₂ zero_lt_one
      (inv_nonneg.mpr ht.le) ((jointPureR_measurable mu 1).comp (by fun_prop))
      (fun s hs => (hB _ (div_pos hs ht)).trans_eq (by ring))
    simpa only [f,mul_one,mul_assoc] using h
  have hI : IntegrableOn (fun s => lineDensity p s * R s * BoseShape.C (s * 1)) (Ioi 0) :=
    pureC_integrable_of_linear hp hp₂ zero_lt_one (B := 1) zero_le_one
      (jointPureR_measurable mu 1) (fun s hs => by simpa only [one_mul] using hB s hs)
  have hCmp := integral_mono_ae hA (hI.const_mul (t⁻¹ ^ 2)) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0 < s := hs
    have h := mul_le_mul_of_nonneg_left (jointPureR_one_scale_le hmu hmuU ht ht₁ hs₀)
      (mul_nonneg (lineDensity_pos (zero_lt_one.trans_le hp) hs₀).le (BoseShape.C_pos hs₀).le)
    simp only [f,R,mul_one]
    linear_combination h)
  rw [integral_const_mul] at hCmp
  change (∫ s : ℝ in Ioi 0, lineDensity p s * f s) ≤ t⁻¹ ^ 2 * jointUnitJ p mu 1 at hCmp
  rw [hEq]
  refine (mul_le_mul_of_nonneg_left hCmp (Real.rpow_nonneg ht.le _)).trans_eq ?_
  rw [← mul_assoc, inv_pow, ← Real.rpow_two, ← Real.rpow_neg ht.le, ← Real.rpow_add ht]
  congr 1
  ring

private theorem jointPureDirection_le {p mu u t : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hmu : 0 ≤ mu) (hmuU : mu ≤ 9 / 500) (huL : 7 / 8 ≤ u) (hut : u ≤ t) (ht₁ : t ≤ 1) :
    (∫ s : ℝ in Ioi 0, lineDensity p s * jointPureR mu u s * BoseShape.C (s * t)) ≤
      u ^ 2 * t ^ (-(p + 2)) * jointUnitJ p mu 1 - (1 - u) * (583 / 10000) := by
  have hp₂ := hP.trans (by norm_num : (9 / 5 : ℝ) ≤ 2)
  have hu := (by norm_num : (0 : ℝ) < 7 / 8).trans_le huL
  have ht := hu.trans_le hut
  have hu₁ := hut.trans ht₁
  let F (s : ℝ) := lineDensity p s * jointPureR mu u s * BoseShape.C (s * t)
  let J (s : ℝ) := lineDensity p s * jointPureR mu 1 s * BoseShape.C (s * t)
  let K (s : ℝ) := lineDensity p s * outerK u s * BoseShape.C (s * t)
  have hF : IntegrableOn F (Ioi 0) := pureC_integrable_of_linear hp hp₂ ht (by norm_num : (0 : ℝ) ≤ 2)
    (jointPureR_measurable mu u) (jointPureR_linear hmu hmuU hu hu₁)
  have hJ : IntegrableOn J (Ioi 0) := pureC_integrable_of_linear hp hp₂ ht (by norm_num : (0 : ℝ) ≤ 2)
    (jointPureR_measurable mu 1) (jointPureR_linear hmu hmuU zero_lt_one le_rfl)
  obtain ⟨B, hB, hB'⟩ := outerK_linear_bound hu
  have hK : IntegrableOn K (Ioi 0) :=
    pureC_integrable_of_linear hp hp₂ ht hB (by unfold outerK; fun_prop) hB'
  have h := integral_mono_ae hF ((hJ.const_mul (u ^ 2)).add (hK.const_mul (1 - u))) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0 < s := hs
    have h := mul_le_mul_of_nonneg_left (jointPureR_scale_bound hmu hu hu₁ hs₀)
      (mul_nonneg (lineDensity_pos (zero_lt_one.trans_le hp) hs₀).le (BoseShape.C_pos (mul_pos hs₀ ht)).le)
    simp only [F,J,K,Pi.add_apply]
    linear_combination h)
  change (∫ s : ℝ in Ioi 0, F s) ≤ ∫ s : ℝ in Ioi 0, u ^ 2 * J s + (1 - u) * K s at h
  rw [integral_add (hJ.const_mul _) (hK.const_mul _), integral_const_mul, integral_const_mul] at h
  have hJ' := mul_le_mul_of_nonneg_left (jointUnitJ_scaled_le hp hp₂ hmu hmuU ht ht₁) (sq_nonneg u)
  have hK' := mul_le_mul_of_nonneg_left (jointOuterK_integral_le hp hP huL hut ht₁) (sub_nonneg.mpr hu₁)
  change u ^ 2 * (∫ s : ℝ in Ioi 0, J s) ≤ _ at hJ'
  change (1 - u) * (∫ s : ℝ in Ioi 0, K s) ≤ _ at hK'
  exact h.trans ((add_le_add hJ' hK').trans_eq (by ring))

noncomputable def jointPureRStream (p mu u t : ℝ) : ℝ :=
  ∫ s : ℝ in Ioi 0, lineDensity p s * jointPureR mu u s * scaledExpTail s t

theorem jointPureRStream_gap_le {p mu u : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hmu : 0 ≤ mu) (hmuU : mu ≤ 9 / 500) (huL : 7 / 8 ≤ u) (hu₁ : u < 1) :
    jointPureRStream p mu u u - jointPureRStream p mu u 1 ≤
      (1 - u) * (1 + (6 / 25) * p + jointUnitValue p mu) - (583 / 10000) * (1 - u) ^ 2 := by
  have hu := (by norm_num : (0 : ℝ) < 7 / 8).trans_le huL
  have hp₂ := hP.trans (by norm_num : (9 / 5 : ℝ) ≤ 2)
  let J := jointUnitJ p mu 1
  let D (t : ℝ) := -(u ^ 2 * J) * (t ^ (-(p + 1)) / (p + 1)) - (1 - u) * (583 / 10000) * t
  let D' (t : ℝ) := u ^ 2 * t ^ (-(p + 2)) * J - (1 - u) * (583 / 10000)
  obtain ⟨_, _, hB⟩ := pureLinear_envelope hp hp₂ (by norm_num : (0 : ℝ) ≤ 2)
    (jointPureR_linear hmu hmuU hu hu₁.le)
  have hM : Measurable (fun s => lineDensity p s * jointPureR mu u s) :=
    (by unfold lineDensity; fun_prop : Measurable (lineDensity p)).mul (jointPureR_measurable mu u)
  have hF (t : ℝ) (ht : 0 < t) : HasDerivAt (jointPureRStream p mu u)
      (-(∫ s : ℝ in Ioi 0, lineDensity p s * jointPureR mu u s * BoseShape.C (s * t))) t :=
    (boseStream_derivative hM hB ht).2
  have hD (t : ℝ) (ht : 0 < t) : HasDerivAt D (D' t) t := by
    have hPow := (Real.hasDerivAt_rpow_const (p := -(p + 1)) (Or.inl ht.ne')).div_const (p + 1)
    convert (hPow.const_mul (-(u ^ 2 * J))).sub
      ((hasDerivAt_id t).const_mul ((1 - u) * (583 / 10000))) using 1
    simp only [D', mul_one, show -(p + 1) - 1 = -(p + 2) by ring]
    field_simp [(show p + 1 ≠ 0 by positivity)]
  have hE (t : ℝ) (ht : 0 < t) : HasDerivAt (fun t => jointPureRStream p mu u t + D t)
      (D' t - ∫ s : ℝ in Ioi 0, lineDensity p s * jointPureR mu u s * BoseShape.C (s * t)) t := by
    rw [sub_eq_add_neg, add_comm (D' t)]
    exact (hF t ht).add (hD t ht)
  have hMono : MonotoneOn (fun t => jointPureRStream p mu u t + D t) (Icc u 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun t ht => (hE t (hu.trans_le ht.1)).continuousAt.continuousWithinAt
    · exact fun t ht => (hE t (hu.trans_le (interior_subset ht).1)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Icc u 1 := interior_subset ht
      rw [(hE t (hu.trans_le ht'.1)).deriv]
      exact sub_nonneg.mpr (jointPureDirection_le hp hP hmu hmuU huL ht'.1 ht'.2)
  have h := hMono ⟨le_rfl, hu₁.le⟩ ⟨hu₁.le, le_rfl⟩ hu₁.le
  have hBound := mul_le_mul_of_nonneg_right (outer_finite_scaling hp hP huL hu₁) (jointUnitJ_one_nonneg hp hmu hmuU)
  have hEq : D 1 - D u = (u ^ 2 * ((u ^ (-(p + 1)) - 1) / (p + 1))) * J -
      (583 / 10000) * (1 - u) ^ 2 := by
    simp only [D, Real.one_rpow, mul_one]
    ring
  change jointPureRStream p mu u u + D u ≤ jointPureRStream p mu u 1 + D 1 at h
  rw [← jointUnitJ_one_eq hp hp₂]
  change _ ≤ (1 - u) * J - _
  nlinarith only [h,hEq,hBound]

end ACS12.GammaMeasure

import ACS12.OuterGap
import ACS12.PureBoseMomentBound

/-! Complete first and shifted source moments for the outer high-gap correction. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaDeficit (lineDensity)

theorem scaledExpTail_gap_ge {s u : ℝ} (hs : 0 < s) (hu : 0 < u) (hu₁ : u ≤ 1) :
    (1 - u) * BoseShape.C s ≤ scaledExpTail s u - scaledExpTail s 1 := by
  let f (r : ℝ) := scaledExpTail s r + r * BoseShape.C s
  have hd (r : ℝ) (hr : 0 < r) : HasDerivAt f (BoseShape.C s - BoseShape.C (s * r)) r := by
    convert (scaledExpTail_derivative hs hr).add ((hasDerivAt_id r).mul_const (BoseShape.C s)) using 1
    simp only [one_mul]
    ring
  have hm : AntitoneOn f (Icc u 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · intro r hr
      exact (hd r (hu.trans_le hr.1)).continuousAt.continuousWithinAt
    · intro r hr
      have hr' : r ∈ Icc u 1 := interior_subset hr
      exact (hd r (hu.trans_le hr'.1)).differentiableAt.differentiableWithinAt
    · intro r hr
      have hr' : r ∈ Icc u 1 := interior_subset hr
      have hr₀ := hu.trans_le hr'.1
      rw [(hd r hr₀).deriv]
      exact sub_nonpos.mpr (BoseShape.C_antitone (mul_pos hs hr₀) hs
        (mul_le_of_le_one_right hs.le hr'.2))
  have h := hm ⟨le_rfl, hu₁⟩ ⟨hu₁, le_rfl⟩ hu₁
  dsimp only [f] at h
  linarith

theorem polyB_elasticity {x : ℝ} (hx : 0 ≤ x) :
    x * (1 - Real.exp (-x)) ≤ 2 * polyB x := by
  let f (t : ℝ) := t - 2 + (t + 2) * Real.exp (-t)
  have hd (t : ℝ) : HasDerivAt f (1 - (t + 1) * Real.exp (-t)) t := by
    have h := ((hasDerivAt_id t).sub_const 2).add
      (((hasDerivAt_id t).add_const 2).mul (hasDerivAt_neg t).exp)
    convert h using 1
    simp only [id_eq]
    ring
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · exact fun t _ => (hd t).continuousAt.continuousWithinAt
    · exact fun t _ => (hd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hd t).deriv]
      apply sub_nonneg.mpr
      have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp t) (Real.exp_pos (-t)).le
      rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
  have h := hm (by simp : (0 : ℝ) ∈ Ici 0) hx hx
  simp only [f, zero_sub, zero_add, neg_zero, Real.exp_zero, mul_one] at h
  unfold polyB
  linarith only [h]

theorem polyB_scale_lower {u s : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) (hs : 0 < s) :
    u ^ 2 * polyB s ≤ polyB (u * s) := by
  let f (x : ℝ) := polyB x / x ^ 2
  have hd (x : ℝ) (hx : 0 < x) :
      HasDerivAt f ((x * (1 - Real.exp (-x)) - 2 * polyB x) / x ^ 3) x := by
    convert (hasDerivAt_polyB x).div ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 hx.ne') using 1
    simp only [id_eq, Nat.cast_ofNat, mul_one, Pi.pow_apply]
    norm_num
    field_simp [hx.ne']
  have hm : AntitoneOn f (Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi _)
    · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
    · exact fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx₀ : 0 < x := interior_subset hx
      rw [(hd x hx₀).deriv]
      exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (polyB_elasticity hx₀.le)) (by positivity)
  have h := hm (mul_pos hu hs) hs (mul_le_of_le_one_left hs.le hu₁)
  change polyB s / s ^ 2 ≤ polyB (u * s) / (u * s) ^ 2 at h
  rw [mul_pow] at h
  have h' := (div_le_div_iff₀ (by positivity : 0 < s ^ 2)
    (by positivity : 0 < u ^ 2 * s ^ 2)).mp h
  exact le_of_mul_le_mul_right (by nlinarith only [h'] : (u ^ 2 * polyB s) * s ^ 2 ≤
    polyB (u * s) * s ^ 2) (by positivity : 0 < s ^ 2)

theorem pureOuterDeficit_integral {p L u : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hu : 0 < u) :
    let f (s : ℝ) := lineDensity p s * polyB (u * s) * (scaledExpTail s u - scaledExpTail s 1)
    IntegrableOn f (Ioi 0) ∧ outerLawDeficit p L 0 u = ∫ s : ℝ in Ioi 0, f s := by
  simpa only [lawPeanoDensity, lawDensity, sub_zero, one_mul, zero_mul, add_zero, densityPolynomial] using
    outerLawDeficit_integral hp hp₂ hL (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩) hu

theorem pureOuterDeficit_lower {p L u : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hu : 0 < u) (hu₁ : u ≤ 1) :
    (1 - u) * u ^ 2 * (1 + p * (p - 1) * powerTail (p + 1) 1) ≤ outerLawDeficit p L 0 u := by
  let g (s : ℝ) := lineDensity p s * polyB s * BoseShape.C s
  have hEq : (∫ s : ℝ in Ioi 0, g s) = 1 + p * (p - 1) * powerTail (p + 1) 1 := by
    simpa only [g, Nat.cast_zero, mul_zero, Real.exp_zero, mul_one, zero_add, Nat.zero_add,
      Real.one_rpow, zero_mul, sub_zero] using pureBoseB_moment hp hp₂ 0
  have hg : IntegrableOn g (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [hEq]
    have hZ := powerTail_pos (by linarith : 1 < p + 1) (by decide : (0 : ℕ) < 1)
    exact (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg
      (mul_nonneg (zero_lt_one.trans_le hp).le (sub_nonneg.mpr hp)) hZ.le)).ne'
  obtain ⟨hf, hF⟩ := pureOuterDeficit_integral hp hp₂ hL hu
  rw [hF, ← hEq, ← integral_const_mul]
  apply integral_mono_ae (hg.const_mul _) hf
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs₀ : 0 < s := hs
  have hB := mul_le_mul (polyB_scale_lower hu hu₁ hs₀) (scaledExpTail_gap_ge hs₀ hu hu₁)
    (mul_nonneg (sub_nonneg.mpr hu₁) (BoseShape.C_pos hs₀).le) (polyB_pos (mul_pos hu hs₀)).le
  have h := mul_le_mul_of_nonneg_left hB (lineDensity_pos (zero_lt_one.trans_le hp) hs₀).le
  dsimp only [g]
  nlinarith only [h]

noncomputable def pureOuterShiftedDeficit (p u : ℝ) : ℝ :=
  ∫ s : ℝ in Ioi 0, lineDensity p s * polyB (u * s) * Real.exp (-s * u) *
    (scaledExpTail s u - scaledExpTail s 1)

private theorem scaledShiftedBoseMoment {p u : ℝ} (hu : 0 < u) :
    (∫ s : ℝ in Ioi 0, lineDensity p s * polyB (u * s) * Real.exp (-s * u) * BoseShape.C (u * s)) =
      u ^ (-p) * shiftedBoseMoment p := by
  let f (s : ℝ) := lineDensity p s * polyB s * Real.exp (-s) * BoseShape.C s
  have hEq (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      lineDensity p s * polyB (u * s) * Real.exp (-s * u) * BoseShape.C (u * s) =
        u ^ (-(p - 1)) * f (s * u) := by
    have hs₀ : 0 < s := hs
    have hρ : lineDensity p (s * u) = u ^ (p - 1) * lineDensity p s := by
      unfold lineDensity
      rw [Real.mul_rpow hs₀.le hu.le]
      ring
    have hPow : u ^ (-(p - 1)) * u ^ (p - 1) = 1 := by
      rw [Real.rpow_neg hu.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hu _).ne']
    simp only [f, hρ, show -(s * u) = -s * u by ring]
    rw [mul_comm s u]
    linear_combination -lineDensity p s * polyB (u * s) *
      Real.exp (-s * u) * BoseShape.C (u * s) * hPow
  rw [setIntegral_congr_fun measurableSet_Ioi hEq, integral_const_mul,
    integral_comp_mul_right_Ioi f 0 hu, zero_mul, smul_eq_mul, ← mul_assoc]
  have hPow : u ^ (-(p - 1)) * u⁻¹ = u ^ (-p) := by
    rw [← div_eq_mul_inv, ← Real.rpow_sub_one hu.ne', show -(p - 1) - 1 = -p by ring]
  rw [hPow]
  rfl

theorem pureOuterShiftedDeficit_le {p L u : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hu : 0 < u) (hu₁ : u ≤ 1) :
    pureOuterShiftedDeficit p u ≤ (1 - u) * (u ^ (-p) * shiftedBoseMoment p) := by
  let f (s : ℝ) := lineDensity p s * polyB (u * s) * (scaledExpTail s u - scaledExpTail s 1)
  let g (s : ℝ) := lineDensity p s * polyB (u * s) * Real.exp (-s * u) * BoseShape.C (u * s)
  have hp₀ := zero_lt_one.trans_le hp
  have hf : IntegrableOn f (Ioi 0) := (pureOuterDeficit_integral hp hp₂ hL hu).1
  have hG : (∫ s : ℝ in Ioi 0, g s) = u ^ (-p) * shiftedBoseMoment p := scaledShiftedBoseMoment hu
  have hS : 0 < shiftedBoseMoment p := by
    unfold shiftedBoseMoment
    letI : NeZero (volume.restrict (Ioi (0 : ℝ))) := ⟨positiveHalfLine_ne_zero⟩
    have h := integral_strict_of_ae_lt (volume.restrict (Ioi (0 : ℝ)))
      (integrable_zero ℝ ℝ _) (shiftedBoseMoment_integrable hp hp₂) ?_
    · simpa only [integral_zero] using h
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact mul_pos (mul_pos (mul_pos (lineDensity_pos hp₀ hs) (polyB_pos hs)) (Real.exp_pos _))
        (BoseShape.C_pos hs)
  have hg : IntegrableOn g (Ioi 0) := Integrable.of_integral_ne_zero
    (hG ▸ (mul_pos (Real.rpow_pos_of_pos hu _) hS).ne')
  have hM : IntegrableOn (fun s => Real.exp (-s * u) * f s) (Ioi 0) := by
    have hE : AEStronglyMeasurable (fun s : ℝ => Real.exp (-s * u)) (volume.restrict (Ioi 0)) :=
      (by fun_prop : Measurable (fun s : ℝ => Real.exp (-s * u))).aestronglyMeasurable
    apply Integrable.bdd_mul (c := 1) hf hE
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) hu.le)
  have hP (s : ℝ) : lineDensity p s * polyB (u * s) * Real.exp (-s * u) *
      (scaledExpTail s u - scaledExpTail s 1) = Real.exp (-s * u) * f s := by dsimp only [f]; ring
  rw [pureOuterShiftedDeficit, setIntegral_congr_fun measurableSet_Ioi (fun s _ => hP s), ← hG, ← integral_const_mul]
  apply integral_mono_ae hM (hg.const_mul _)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have h := mul_le_mul_of_nonneg_left (scaledExpTail_gap_le hs hu hu₁)
    (mul_nonneg (mul_nonneg (lineDensity_pos hp₀ hs).le (polyB_pos (mul_pos hu hs)).le)
      (Real.exp_pos (-s * u)).le)
  rw [show BoseShape.C (s * u) = BoseShape.C (u * s) by rw [mul_comm s u]] at h
  dsimp only [f, g]
  nlinarith only [h]

end ACS12.GammaMeasure

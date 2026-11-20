import ACS12.JointMomentsPrice

/-! Complete Bose spacing and retained A-stream bounds. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaDeficit (lineDensity)

theorem scaledExpTail_secant {s a b : ℝ} (hs : 0 < s) (ha : 0 < a) (hab : a ≤ b) :
    (b - a) * BoseShape.C (s * b) ≤ scaledExpTail s a - scaledExpTail s b ∧
      scaledExpTail s a - scaledExpTail s b ≤ (b - a) * BoseShape.C (s * a) := by
  let f (c t : ℝ) := scaledExpTail s t + c * t
  have hD (c t : ℝ) (ht : 0 < t) : HasDerivAt (f c) (c - BoseShape.C (s * t)) t := by
    convert (scaledExpTail_derivative hs ht).add ((hasDerivAt_id t).const_mul c) using 1
    simp only [mul_one]
    ring
  have hP (t : ℝ) (ht : t ∈ Icc a b) : 0 < t := ha.trans_le ht.1
  have hC (c : ℝ) : ContinuousOn (f c) (Icc a b) :=
    fun t ht => (hD c t (hP t ht)).continuousAt.continuousWithinAt
  have hDiff (c : ℝ) : DifferentiableOn ℝ (f c) (interior (Icc a b)) :=
    fun t ht => (hD c t (hP t (interior_subset ht))).differentiableAt.differentiableWithinAt
  have hLow : AntitoneOn (f (BoseShape.C (s * b))) (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) (hC _) (hDiff _)
    intro t ht
    have ht' : t ∈ Icc a b := interior_subset ht
    rw [(hD _ t (hP t ht')).deriv]
    exact sub_nonpos.mpr (BoseShape.C_antitone (mul_pos hs (hP t ht')) (mul_pos hs (ha.trans_le hab))
      (mul_le_mul_of_nonneg_left ht'.2 hs.le))
  have hHigh : MonotoneOn (f (BoseShape.C (s * a))) (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (hC _) (hDiff _)
    intro t ht
    have ht' : t ∈ Icc a b := interior_subset ht
    rw [(hD _ t (hP t ht')).deriv]
    exact sub_nonneg.mpr (BoseShape.C_antitone (mul_pos hs ha) (mul_pos hs (hP t ht'))
      (mul_le_mul_of_nonneg_left ht'.1 hs.le))
  have hA : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hB : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have h₁ := hLow hA hB hab
  have h₂ := hHigh hA hB hab
  dsimp only [f] at h₁ h₂
  exact ⟨by nlinarith only [h₁], by nlinarith only [h₂]⟩

theorem polyA_scale_upper {k x : ℝ} (hk : 1 ≤ k) (hx : 0 ≤ x) :
    polyA (k * x) ≤ k ^ 2 * polyA x := by
  let f (t : ℝ) := k ^ 2 * polyA t - polyA (k * t)
  have hD (t : ℝ) : HasDerivAt f (k ^ 2 * t * (Real.exp (-t) - Real.exp (-(k * t)))) t := by
    convert ((hasDerivAt_polyA t).const_mul (k ^ 2)).sub
      ((hasDerivAt_polyA (k * t)).comp t ((hasDerivAt_id t).const_mul k)) using 1
    simp only [mul_one]
    ring
  have hM : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · exact fun t _ => (hD t).continuousAt.continuousWithinAt
    · exact fun t _ => (hD t).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : 0 ≤ t := (show t ∈ Ici 0 from interior_subset ht)
      rw [(hD t).deriv]
      have h := Real.exp_le_exp.mpr (neg_le_neg (le_mul_of_one_le_left ht' hk))
      exact mul_nonneg (mul_nonneg (sq_nonneg k) ht') (sub_nonneg.mpr h)
  have h := hM (show (0 : ℝ) ∈ Ici 0 by simp) (show x ∈ Ici 0 from hx) hx
  have h0 : f 0 = 0 := by simp [f, polyA]
  rw [h0] at h
  exact sub_nonneg.mp h

theorem pureA_exp_moment {p : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) :
    IntegrableOn (fun s => lineDensity p s * polyA s * Real.exp (-s)) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, lineDensity p s * polyA s * Real.exp (-s)) =
        1 - (1 + p / 2) * (2 : ℝ) ^ (-p) := by
  let F (s : ℝ) := lineDensity p s * Real.exp (-s)
  let G (s : ℝ) := lineDensity p s * Real.exp (-s * 2)
  let H (s : ℝ) := lineDensity p s * s * Real.exp (-s * 2)
  let h0 : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have hF : IntegrableOn F (Ioi 0) := by
    simpa only [F, lawDensity, sub_zero, one_mul, zero_mul, add_zero, pow_zero, mul_one] using
      lawMoment_integrable hp hp₂ zero_lt_one h0 zero_lt_one 0
  have hG : IntegrableOn G (Ioi 0) := by
    simpa only [G, lawDensity, sub_zero, one_mul, zero_mul, add_zero, pow_zero, mul_one] using
      lawMoment_integrable hp hp₂ zero_lt_one h0 (by norm_num : (0 : ℝ) < 2) 0
  have hH : IntegrableOn H (Ioi 0) := by
    simpa only [H, lawDensity, sub_zero, one_mul, zero_mul, add_zero, pow_one] using
      lawMoment_integrable hp hp₂ zero_lt_one h0 (by norm_num : (0 : ℝ) < 2) 1
  have hEq (s : ℝ) : lineDensity p s * polyA s * Real.exp (-s) = F s - G s - H s := by
    dsimp only [F, G, H, polyA]
    rw [show -s * 2 = -s + -s by ring, Real.exp_add]
    ring
  refine ⟨((hF.sub hG).sub hH).congr (Eventually.of_forall fun s => (hEq s).symm), ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => hEq s)]
  change (∫ s : ℝ in Ioi 0, (F - G) s - H s) = _
  rw [integral_sub (hF.sub hG) hH]
  change ((∫ s : ℝ in Ioi 0, F s - G s) - ∫ s : ℝ in Ioi 0, H s) = _
  rw [integral_sub hF hG]
  have hp₀ := zero_lt_one.trans_le hp
  have hE (t : ℝ) :
      lawMoment p 1 0 0 t = ∫ s : ℝ in Ioi 0, lineDensity p s * Real.exp (-s * t) := by
    simp only [lawMoment, lawDensity, sub_zero, one_mul, zero_mul, add_zero, pow_zero, mul_one]
  have hT : lawMoment p 1 0 1 2 = ∫ s : ℝ in Ioi 0, H s := by
    simp only [H, lawMoment, lawDensity, sub_zero, one_mul, zero_mul, add_zero, pow_one]
  change (∫ s : ℝ in Ioi 0, F s) - (∫ s : ℝ in Ioi 0, G s) - (∫ s : ℝ in Ioi 0, H s) = _
  have hFE : (∫ s : ℝ in Ioi 0, F s) = 1 := by
    rw [← show lawMoment p 1 0 0 1 = (∫ s : ℝ in Ioi 0, F s) by simpa only [F, mul_one] using hE 1,
      lawMoment_zero_radial hp₀ zero_lt_one, Real.one_rpow]
  have hGE : (∫ s : ℝ in Ioi 0, G s) = (2 : ℝ) ^ (-p) := by
    rw [← show lawMoment p 1 0 0 2 = (∫ s : ℝ in Ioi 0, G s) from hE 2,
      lawMoment_zero_radial hp₀ (by norm_num)]
  rw [hFE, hGE, ← hT, lawMoment_zero_slope hp₀ (by norm_num),
    show -(p + 1) = -p - 1 by ring, Real.rpow_sub_one (by norm_num : (2 : ℝ) ≠ 0)]
  ring

theorem pureA_exp_moment_lt {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    (∫ s : ℝ in Ioi 0, lineDensity p s * polyA s * Real.exp (-s)) < 91 / 200 := by
  let f (x : ℝ) := (1 + x / 2) * (2 : ℝ) ^ (-x)
  let d (x : ℝ) := (2 : ℝ) ^ (-x) * (1 / 2 - (1 + x / 2) * Real.log 2)
  have hD (x : ℝ) : HasDerivAt f (d x) x := by
    have h := hasDerivAt_id x
    convert ((h.div_const 2).const_add 1).mul (h.neg.const_rpow (by norm_num : (0 : ℝ) < 2)) using 1
    simp only [d, id_eq, Pi.neg_apply]
    ring
  have hA : AntitoneOn f (Icc 1 (9 / 5)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · exact fun x _ => (hD x).continuousAt.continuousWithinAt
    · exact fun x _ => (hD x).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Icc (1 : ℝ) (9 / 5) := interior_subset hx
      rw [(hD x).deriv]
      have h := mul_le_mul (show (3 / 2 : ℝ) ≤ 1 + x / 2 by linarith only [hx'.1])
        (show (693 / 1000 : ℝ) ≤ Real.log 2 by linarith only [Real.log_two_gt_d9])
        (by norm_num) (by linarith only [hx'.1])
      exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (by norm_num) _) (by linarith only [h])
  have hF := hA (show p ∈ Icc 1 (9 / 5) from ⟨hp, hP⟩)
    (show (9 / 5 : ℝ) ∈ Icc 1 (9 / 5) by constructor <;> norm_num) hP
  have hP' : (28717 / 100000 : ℝ) < (2 : ℝ) ^ (-(9 / 5 : ℝ)) := by
    apply (Real.rpow_lt_rpow_iff (by norm_num) (Real.rpow_nonneg (by norm_num) _)
      (z := (5 : ℝ)) (by norm_num)).mp
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [(pureA_exp_moment hp (hP.trans (by norm_num))).2]
  dsimp only [f] at hF
  linarith only [hF, hP']

end ACS12.GammaMeasure

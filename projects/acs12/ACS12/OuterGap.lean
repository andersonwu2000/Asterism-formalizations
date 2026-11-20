import ACS12.OuterLaw
import ACS12.PureBose
import ACS12.MiddlePbar

/-! The all-u pure outer deficit bound and its transfer to the actual law. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaDeficit (lineDensity lineDensity_exp_integral)

theorem scaledExpTail_gap_le {s u : ℝ} (hs : 0 < s) (hu : 0 < u) (hu₁ : u ≤ 1) :
    scaledExpTail s u - scaledExpTail s 1 ≤ (1 - u) * BoseShape.C (s * u) := by
  let f (r : ℝ) := scaledExpTail s r + r * BoseShape.C (s * u)
  have hd (r : ℝ) (hr : 0 < r) : HasDerivAt f (BoseShape.C (s * u) - BoseShape.C (s * r)) r := by
    convert (scaledExpTail_derivative hs hr).add ((hasDerivAt_id r).mul_const (BoseShape.C (s * u))) using 1
    simp only [one_mul]
    ring
  have hm : MonotoneOn f (Icc u 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro r hr
      exact (hd r (hu.trans_le hr.1)).continuousAt.continuousWithinAt
    · intro r hr
      have hr' : r ∈ Icc u 1 := interior_subset hr
      exact (hd r (hu.trans_le hr'.1)).differentiableAt.differentiableWithinAt
    · intro r hr
      have hr' : r ∈ Icc u 1 := interior_subset hr
      have hr₀ := hu.trans_le hr'.1
      rw [(hd r hr₀).deriv]
      exact sub_nonneg.mpr (BoseShape.C_antitone (mul_pos hs hu) (mul_pos hs hr₀)
        (mul_le_mul_of_nonneg_left hr'.1 hs.le))
  have h := hm ⟨le_rfl, hu₁⟩ ⟨hu₁, le_rfl⟩ hu₁
  dsimp only [f] at h
  linarith

@[simp] theorem lawMoment_zero_radial {p L t : ℝ} (hp : 0 < p) (ht : 0 < t) :
    lawMoment p L 0 0 t = t ^ (-p) := by
  simpa only [lawMoment, lawDensity, sub_zero, one_mul, zero_mul, add_zero, pow_zero, mul_one] using
    lineDensity_exp_integral hp ht

@[simp] theorem lawMoment_zero_slope {p L t : ℝ} (hp : 0 < p) (ht : 0 < t) :
    lawMoment p L 0 1 t = p * t ^ (-(p + 1)) := by
  simp only [lawMoment, lawDensity, sub_zero, one_mul, zero_mul, add_zero, pow_one]
  have hP (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      lineDensity p s * s * Real.exp (-s * t) =
        p * (lineDensity (p + 1) s * Real.exp (-s * t)) := by
    have hs₀ : 0 < s := hs
    have hG := (Real.Gamma_pos_of_pos hp).ne'
    have hPow : s ^ (p - 1) * s = s ^ p := by
      rw [Real.rpow_sub_one hs₀.ne', div_mul_cancel₀ _ hs₀.ne']
    have hR : lineDensity p s * s = p * lineDensity (p + 1) s := by
      unfold lineDensity
      rw [show (s ^ (p - 1) / Real.Gamma p) * s = (s ^ (p - 1) * s) / Real.Gamma p by ring,
        hPow, add_sub_cancel_right, Real.Gamma_add_one hp.ne']
      field_simp [hp.ne', hG]
    rw [hR]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hP, integral_const_mul,
    lineDensity_exp_integral (by positivity : 0 < p + 1) ht]

theorem outerLawDenom_zero {p L u : ℝ} (hp : 0 < p) (hu : 0 < u) :
    outerLawDenom p L 0 u = (p + 1) * u ^ (-p) := by
  rw [outerLawDenom, lawMoment_zero_radial hp hu, lawMoment_zero_slope hp hu,
    lawSelf, zero_mul, add_zero,
    show -(p + 1) = -p - 1 by ring, Real.rpow_sub_one hu.ne']
  field_simp [hu.ne']

theorem pureBoseB_moment_scaled {p u : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hu : 0 < u) :
    (∫ s : ℝ in Ioi 0, lineDensity p s * polyB (u * s) * BoseShape.C (u * s)) =
      u ^ (-p) * (1 + p * (p - 1) * powerTail (p + 1) 1) := by
  let f (s : ℝ) := lineDensity p s * polyB s * BoseShape.C s
  have hF : (∫ s : ℝ in Ioi 0, f s) = 1 + p * (p - 1) * powerTail (p + 1) 1 := by
    simpa only [f, Nat.cast_zero, mul_zero, Real.exp_zero, mul_one, zero_add, Nat.zero_add, Real.one_rpow,
      zero_mul, sub_zero] using pureBoseB_moment hp hp₂ 0
  have hEq (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      lineDensity p s * polyB (u * s) * BoseShape.C (u * s) =
        u ^ (-(p - 1)) * f (s * u) := by
    have hs₀ : 0 < s := hs
    have hρ : lineDensity p (s * u) = u ^ (p - 1) * lineDensity p s := by
      unfold lineDensity
      rw [Real.mul_rpow hs₀.le hu.le]
      ring
    have hPow : u ^ (-(p - 1)) * u ^ (p - 1) = 1 := by
      rw [Real.rpow_neg hu.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hu _).ne']
    dsimp only [f]
    rw [hρ, mul_comm s u]
    calc
      _ = (u ^ (-(p - 1)) * u ^ (p - 1)) *
          (lineDensity p s * polyB (u * s) * BoseShape.C (u * s)) := by rw [hPow, one_mul]
      _ = _ := by ring
  rw [setIntegral_congr_fun measurableSet_Ioi hEq, integral_const_mul,
    integral_comp_mul_right_Ioi f 0 hu, zero_mul, smul_eq_mul, hF, ← mul_assoc]
  have hPow : u ^ (-(p - 1)) * u⁻¹ = u ^ (-p) := by
    rw [← div_eq_mul_inv, ← Real.rpow_sub_one hu.ne', show -(p - 1) - 1 = -p by ring]
  rw [hPow]

theorem outerLawGap_pure_lt {p L u : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hL : 0 < L) (hu : 0 < u) (hu₁ : u < 1) :
    u - outerLawMass p L 0 u < 1 - u := by
  have hp₂ : p ≤ 2 := hP.trans (by norm_num)
  have hθ : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have hp₀ := zero_lt_one.trans_le hp
  let δ := 1 - u
  let K (s : ℝ) := lineDensity p s * polyB (u * s) * BoseShape.C (u * s)
  let F (s : ℝ) := lineDensity p s * polyB (u * s) * (scaledExpTail s u - scaledExpTail s 1)
  have hδ : 0 < δ := sub_pos.mpr hu₁
  have hI : (∫ s : ℝ in Ioi 0, K s) = u ^ (-p) * (1 + p * (p - 1) * powerTail (p + 1) 1) :=
    pureBoseB_moment_scaled hp hp₂ hu
  have hK : IntegrableOn K (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [hI]
    have hZ := powerTail_pos (by linarith : 1 < p + 1) (show (0 : ℕ) < 1 by decide)
    exact (mul_pos (Real.rpow_pos_of_pos hu (-p)) (add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg (mul_nonneg hp₀.le (sub_nonneg.mpr hp)) hZ.le))).ne'
  obtain ⟨hF, hFE⟩ := outerLawDeficit_integral hp hp₂ hL hθ hu
  have hF' : IntegrableOn F (Ioi 0) := by
    simpa only [F, lawPeanoDensity, lawDensity, sub_zero, one_mul, zero_mul, add_zero,
      densityPolynomial] using hF
  have hFE' : outerLawDeficit p L 0 u = ∫ s : ℝ in Ioi 0, F s := by
    simpa only [F, lawPeanoDensity, lawDensity, sub_zero, one_mul, zero_mul, add_zero,
      densityPolynomial] using hFE
  have hBound : outerLawDeficit p L 0 u ≤ δ * (∫ s : ℝ in Ioi 0, K s) := by
    rw [hFE', ← integral_const_mul]
    apply integral_mono_ae hF' (hK.const_mul δ)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0 < s := hs
    have hB := mul_le_mul_of_nonneg_left (scaledExpTail_gap_le hs₀ hu hu₁.le)
      (mul_pos (lineDensity_pos hp₀ hs₀) (polyB_pos (mul_pos hu hs₀))).le
    rw [mul_comm s u] at hB
    dsimp only [F, K, δ]
    linarith only [hB]
  have hP' := middle_powerMoment_lt hp hP
  have hLt : outerLawDeficit p L 0 u < δ * outerLawDenom p L 0 u := by
    rw [hI] at hBound
    rw [outerLawDenom_zero hp₀ hu]
    have h := hBound.trans_lt (mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left
      (by linarith only [hP'] : 1 + p * (p - 1) * powerTail (p + 1) 1 < p + 1)
      (Real.rpow_pos_of_pos hu (-p))) hδ)
    simpa only [mul_comm (u ^ (-p)) (p + 1)] using h
  unfold outerLawMass
  have hD := outerLawDenom_pos hp hp₂ hL hθ hu
  have h := (div_lt_iff₀ hD).mpr hLt
  linarith only [h]

theorem outerLawGap_lt {p L θ u : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hu : 0 < u) (hu₁ : u < 1) :
    u - outerLawMass p L θ u < 1 - u := by
  have hp₂ : p < 2 := hP.trans_lt (by norm_num)
  have hMono := (outerLawMass_strictMono hp hp₂ hL hu hu₁).monotoneOn
    (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩) hθ hθ.1
  exact (sub_le_sub_left hMono u).trans_lt (outerLawGap_pure_lt hp hP hL hu hu₁)

end ACS12.GammaMeasure


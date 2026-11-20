import ACS12.PureAdjacentArc
import ACS12.BosePath

/-! Finite mixed source differences along the decreasing affine mass cap. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaDeficit (lineDensity lineDensity_exp_integral lineDensity_exp_integrable)

private theorem exp_mul_C_eq {x : ℝ} (hx : 0 < x) :
    Real.exp x * BoseShape.C x = polyB x / (1 - Real.exp (-x)) ^ 2 := by
  have hD := (expHead_den_pos hx).ne'
  rw [Real.exp_neg] at hD ⊢
  unfold BoseShape.C polyB
  rw [Real.exp_neg]
  field_simp [hD, (expTail_den_pos hx).ne', (Real.exp_pos x).ne']

private theorem exp_mul_C_monotone :
    MonotoneOn (fun x => Real.exp x * BoseShape.C x) (Ioi 0) := by
  let f (x : ℝ) := polyB x / (1 - Real.exp (-x)) ^ 2
  have hD (x : ℝ) (hx : 0 < x) : HasDerivAt f
      ((1 - 2 * x * Real.exp (-x) - Real.exp (-x) ^ 2) / (1 - Real.exp (-x)) ^ 3) x := by
    have hX := (hasDerivAt_neg x).exp.const_sub 1
    have hB := hasDerivAt_polyB x
    have hDen := (expHead_den_pos hx).ne'
    convert hB.div (hX.pow 2) (pow_ne_zero 2 hDen) using 1
    simp only [polyB, Nat.cast_ofNat, neg_neg, mul_neg, mul_one, pow_one, Pi.pow_apply]
    field_simp [hDen]
    ring
  have hm : MonotoneOn f (Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi _)
    · exact fun x hx => (hD x hx).continuousAt.continuousWithinAt
    · exact fun x hx => (hD x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx₀ : 0 < x := interior_subset hx
      rw [(hD x hx₀).deriv]
      apply div_nonneg _ (pow_nonneg (expHead_den_pos hx₀).le _)
      have hS := Real.self_lt_sinh_iff.mpr hx₀
      rw [Real.sinh_eq] at hS
      have hE : Real.exp x * Real.exp (-x) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      have h := mul_le_mul_of_nonneg_right
        (show 2 * x ≤ Real.exp x - Real.exp (-x) by linarith only [hS]) (Real.exp_pos (-x)).le
      nlinarith only [h, hE]
  intro x hx y hy hxy
  change Real.exp x * BoseShape.C x ≤ Real.exp y * BoseShape.C y
  rw [exp_mul_C_eq hx, exp_mul_C_eq hy]
  exact hm hx hy hxy

private theorem weightedPeanoSlope_mono {τ : ℝ} (hτ : 0 < τ) (hτ₁ : τ ≤ 1) :
    MonotoneOn (fun s => polyA s * Real.exp s * BoseShape.C (s * τ)) (Ioi 0) := by
  intro x hx y hy hxy
  have hx₀ : 0 < x := hx
  have hy₀ : 0 < y := hy
  have hEq (s : ℝ) : polyA s * Real.exp s * BoseShape.C (s * τ) =
      (polyA s * Real.exp ((1 - τ) * s)) * (Real.exp (s * τ) * BoseShape.C (s * τ)) := by
    have hE : Real.exp ((1 - τ) * s) * Real.exp (s * τ) = Real.exp s := by
      rw [← Real.exp_add, show (1 - τ) * s + s * τ = s by ring]
    rw [← hE]
    ring
  change polyA x * Real.exp x * BoseShape.C (x * τ) ≤ polyA y * Real.exp y * BoseShape.C (y * τ)
  rw [hEq, hEq]
  have hX := mul_pos hx₀ hτ
  have hY := mul_pos hy₀ hτ
  apply mul_le_mul
  · exact mul_le_mul (polyA_monotone_nonneg (show x∈Ici (0:ℝ) from (show 0<x from hx).le) (show y∈Ici (0:ℝ) from (show 0<y from hy).le) hxy)
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hxy (sub_nonneg.mpr hτ₁))) (Real.exp_pos _).le
      (polyA_pos hy₀).le
  · exact exp_mul_C_monotone hX hY (mul_le_mul_of_nonneg_right hxy hτ.le)
  · exact mul_nonneg (Real.exp_pos _).le (BoseShape.C_pos hX).le
  · exact mul_nonneg (polyA_pos hy₀).le (Real.exp_pos _).le

private theorem pureAStack_derivative {p τ : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hτ : 0 < τ) :
    let f (s : ℝ) := lineDensity p s * polyA s * BoseShape.C (s * τ)
    IntegrableOn f (Ioi 0) ∧
      HasDerivAt (pureAStack p) (-(∫ s : ℝ in Ioi 0, f s)) τ := by
  let g (s : ℝ) := lineDensity p s * polyA s
  have hθ : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  obtain ⟨B, _, hB⟩ := lawPeanoDensity_quadratic_bound hp hp₂ zero_lt_one hθ zero_lt_one .a
  have hg : Measurable g := by
    unfold g lineDensity polyA
    fun_prop
  have hB' (s : ℝ) (hs : 0 < s) : |g s| ≤ B * s ^ 2 := by
    simpa only [g, lawPeanoDensity, lawDensity, sub_zero, one_mul, zero_mul, add_zero, densityPolynomial] using
      hB s hs
  have hB₀ : 0 ≤ B := by
    have h := (abs_nonneg _).trans (hB' 1 zero_lt_one)
    simpa only [one_pow, mul_one] using h
  have hC (s : ℝ) (hs : 0 < s) : |g s| ≤ B * (s + s ^ 2) :=
    (hB' s hs).trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hs.le) hB₀)
  obtain ⟨hInt, hD⟩ := boseStream_derivative hg hC hτ
  refine ⟨hInt, hD.congr_of_eventuallyEq ?_⟩
  filter_upwards [Ioi_mem_nhds hτ] with t ht
  exact (pureAStack_integral hp hp₂ ht).2

private theorem peanoSlope_le_of_exponent_le {p q τ : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q) (hq : q ≤ 2)
    (hτ : 0 < τ) (hτ₁ : τ ≤ 1) :
    (∫ s : ℝ in Ioi 0, lineDensity p s * polyA s * BoseShape.C (s * τ)) ≤
      ∫ s : ℝ in Ioi 0, lineDensity q s * polyA s * BoseShape.C (s * τ) := by
  let W (s : ℝ) := lineDensity p s * Real.exp (-s)
  let V (s : ℝ) := lineDensity q s * Real.exp (-s)
  let Q (s : ℝ) := polyA s * Real.exp s * BoseShape.C (s * τ)
  let R (s : ℝ) := (Real.Gamma p / Real.Gamma q) * s ^ (q - p)
  let f (r s : ℝ) := lineDensity r s * polyA s * BoseShape.C (s * τ)
  have hp₀ := zero_lt_one.trans_le hp
  have hq₀ := hp₀.trans_le hpq
  have hγ : 0 ≤ Real.Gamma p / Real.Gamma q :=
    div_nonneg (Real.Gamma_pos_of_pos hp₀).le (Real.Gamma_pos_of_pos hq₀).le
  have hWp : ∀ s > 0, 0 < W s := fun s hs => mul_pos (lineDensity_pos hp₀ hs) (Real.exp_pos _)
  have hW : IntegrableOn W (Ioi 0) := by
    simpa only [W, neg_mul, one_mul, mul_one] using lineDensity_exp_integrable hp₀ zero_lt_one
  have hV : IntegrableOn V (Ioi 0) := by
    simpa only [V, neg_mul, one_mul, mul_one] using lineDensity_exp_integrable hq₀ zero_lt_one
  have hf : IntegrableOn (f p) (Ioi 0) := (pureAStack_derivative hp (hpq.trans hq) hτ).1
  have hg : IntegrableOn (f q) (Ioi 0) := (pureAStack_derivative (hp.trans hpq) hq hτ).1
  have hE (r s : ℝ) : (lineDensity r s * Real.exp (-s)) * Q s = f r s := by
    have h := Real.exp_add (-s) s
    rw [neg_add_cancel, Real.exp_zero] at h
    dsimp only [Q, f]
    linear_combination -lineDensity r s * polyA s * BoseShape.C (s * τ) * h
  have hR (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) : W s * R s = V s := by
    have hs₀ : 0 < s := hs
    dsimp only [W, R, V, lineDensity]
    have hP := Real.rpow_add hs₀ (p - 1) (q - p)
    rw [show p - 1 + (q - p) = q - 1 by ring] at hP
    rw [hP]
    field_simp [(Real.Gamma_pos_of_pos hp₀).ne', (Real.Gamma_pos_of_pos hq₀).ne']
  have hP (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) : W s * Q s * R s = f q s := by
    rw [mul_right_comm, hR s hs]
    exact hE q s
  have hI : IntegrableOn (fun s => W s * Q s) (Ioi 0) := hf.congr (Eventually.of_forall (fun s => (hE p s).symm))
  have hJ : IntegrableOn (fun s => W s * R s) (Ioi 0) := hV.congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hR s hs).symm)
  have hK : IntegrableOn (fun s => W s * Q s * R s) (Ioi 0) := hg.congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hP s hs).symm)
  have hQ := weightedPeanoSlope_mono hτ hτ₁
  have hRm : MonotoneOn R (Ioi 0) := fun x hx y _ hxy =>
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (show 0 < x from hx).le hxy (sub_nonneg.mpr hpq)) hγ
  have h := integral_product_comparison hK hW hI hJ (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hE : (W x * Q x * R x) * W y + (W y * Q y * R y) * W x -
        (W x * Q x) * (W y * R y) - (W y * Q y) * (W x * R x) =
        (W x * W y) * ((Q x - Q y) * (R x - R y)) := by ring
    rw [hE]
    apply mul_nonneg (mul_nonneg (hWp x hx).le (hWp y hy).le)
    rcases le_total x y with hxy | hyx
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hQ hx hy hxy))
        (sub_nonpos.mpr (hRm hx hy hxy))
    · exact mul_nonneg (sub_nonneg.mpr (hQ hy hx hyx)) (sub_nonneg.mpr (hRm hy hx hyx)))
  have hW1 : (∫ s : ℝ in Ioi 0, W s) = 1 := by
    simpa only [W, neg_mul, one_mul, mul_one, Real.one_rpow] using lineDensity_exp_integral hp₀ zero_lt_one
  have hV1 : (∫ s : ℝ in Ioi 0, V s) = 1 := by
    simpa only [V, neg_mul, one_mul, mul_one, Real.one_rpow] using lineDensity_exp_integral hq₀ zero_lt_one
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => hE p s),
    setIntegral_congr_fun measurableSet_Ioi hR, setIntegral_congr_fun measurableSet_Ioi hP, hW1, hV1] at h
  simpa only [mul_one] using h

theorem pureAStack_submodular {p q τ₁ τ₂ : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q) (hq : q ≤ 2)
    (hτ₁ : 0 < τ₁) (hτ : τ₁ ≤ τ₂) (hτ₂ : τ₂ ≤ 1) :
    pureAStack p τ₁ + pureAStack q τ₂ ≤ pureAStack p τ₂ + pureAStack q τ₁ := by
  let F (t : ℝ) := pureAStack q t - pureAStack p t
  have hD (t : ℝ) (ht : 0 < t) : HasDerivAt F
      ((∫ s : ℝ in Ioi 0, lineDensity p s * polyA s * BoseShape.C (s * t)) -
       (∫ s : ℝ in Ioi 0, lineDensity q s * polyA s * BoseShape.C (s * t))) t := by
    convert ((pureAStack_derivative (hp.trans hpq) hq ht).2).sub
      ((pureAStack_derivative hp (hpq.trans hq) ht).2) using 1
    ring
  have hMono : AntitoneOn F (Icc τ₁ τ₂) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · exact fun t ht => (hD t (hτ₁.trans_le ht.1)).continuousAt.continuousWithinAt
    · exact fun t ht => (hD t (hτ₁.trans_le (interior_subset ht).1)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Icc τ₁ τ₂ := interior_subset ht
      have ht₀ := hτ₁.trans_le ht'.1
      rw [(hD t ht₀).deriv]
      exact sub_nonpos.mpr (peanoSlope_le_of_exponent_le hp hpq hq ht₀ (ht'.2.trans hτ₂))
  have h := hMono ⟨le_rfl, hτ⟩ ⟨hτ, le_rfl⟩ hτ
  dsimp only [F] at h
  linarith only [h]

end ACS12.GammaMeasure

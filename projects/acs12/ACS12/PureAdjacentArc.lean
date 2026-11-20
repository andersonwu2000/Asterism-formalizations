import ACS12.PurePeanoIntegral
import ACS12.PureZetaEnvelope

/-! Convexity of the complete pure A mesh and the upper-endpoint B scaling. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaDeficit (lineDensity)

noncomputable def pureAStack (p τ : ℝ) : ℝ := samplingHead (purePeanoA p 1) τ τ

noncomputable def pureBStack (p u : ℝ) : ℝ :=
  u ^ (p - 1) * samplingTail (purePeanoB p u) 0 1

theorem pureAStack_integral {p τ : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hτ : 0 < τ) :
    let f (s : ℝ) := lineDensity p s * polyA s * scaledExpTail s τ
    IntegrableOn f (Ioi 0) ∧ pureAStack p τ = ∫ s : ℝ in Ioi 0, f s := by
  have hθ : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  obtain ⟨hI, hEq⟩ := lawPeanoTail_sampling hp hp₂ zero_lt_one hθ zero_lt_one
    (t := 0) le_rfl hτ .a
  simp only [lawPeanoDensity, lawDensity, sub_zero, one_mul, zero_mul, add_zero,
    densityPolynomial, mul_zero, Real.exp_zero, mul_one] at hI hEq
  refine ⟨hI, ?_⟩
  rw [← hEq, samplingTail_eq_shift, zero_add, pureAStack]
  unfold samplingHead
  apply congrArg (τ * ·)
  apply tsum_congr
  intro j
  exact (lawPeanoKernel_zero hp hp₂ zero_lt_one zero_lt_one (by positivity)).1.symm

theorem pureAStack_convex {p : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) :
    ConvexOn ℝ (Ioi 0) (pureAStack p) := by
  refine ⟨convex_Ioi _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx₀ : 0 < x := hx
  have hy₀ : 0 < y := hy
  have hz : 0 < a * x + b * y := convex_Ioi (0 : ℝ) hx hy ha hb hab
  obtain ⟨hI, hE⟩ := pureAStack_integral hp hp₂ hz
  obtain ⟨hX, hEX⟩ := pureAStack_integral hp hp₂ hx₀
  obtain ⟨hY, hEY⟩ := pureAStack_integral hp hp₂ hy₀
  simp only [smul_eq_mul]
  rw [hE, hEX, hEY, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hX.const_mul a) (hY.const_mul b)]
  apply integral_mono_ae hI ((hX.const_mul a).add (hY.const_mul b))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs₀ : 0 < s := hs
  have hD (t : ℝ) (ht : 0 < t) := scaledExpTail_derivative hs₀ ht
  have hMono : MonotoneOn (deriv (scaledExpTail s)) (interior (Ioi 0)) := by
    intro t ht r hr htr
    have ht₀ : 0 < t := interior_subset ht
    have hr₀ : 0 < r := interior_subset hr
    rw [(hD t ht₀).deriv, (hD r hr₀).deriv]
    exact neg_le_neg (BoseShape.C_antitone (mul_pos hs₀ ht₀) (mul_pos hs₀ hr₀)
      (mul_le_mul_of_nonneg_left htr hs₀.le))
  have hConv := hMono.convexOn_of_deriv (convex_Ioi _)
    (fun t ht => (hD t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hD t (interior_subset ht)).differentiableAt.differentiableWithinAt)
  have h := hConv.2 hx hy ha hb hab
  simp only [smul_eq_mul] at h
  have hM := mul_le_mul_of_nonneg_left h
    (mul_pos (lineDensity_pos (zero_lt_one.trans_le hp) hs₀) (polyA_pos hs₀)).le
  simp only [Pi.add_apply]
  nlinarith only [hM]

theorem pureBStack_samples_summable {p u : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hu : 0 < u) :
    Summable (fun j : ℕ => purePeanoB p u ((j : ℝ) + 1)) := by
  have hθ : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  obtain ⟨B, _, hB⟩ := lawPeanoDensity_quadratic_bound hp hp₂ zero_lt_one hθ hu .b
  have hM := lawPeanoDensity_measurable (θ := 0) (h := u) (zero_lt_one.trans_le hp) zero_lt_one .b
  have hS := (hasSum_signedTail (t := 0) hM hB le_rfl zero_lt_one).summable
  apply hS.congr
  intro j
  change lawPeanoKernel p 1 0 u .b (0 + 1 + (j : ℝ) * 1) = _
  simp only [mul_one, zero_add, add_comm (1 : ℝ) (j : ℝ)]
  exact (lawPeanoKernel_zero hp hp₂ zero_lt_one hu (by positivity)).2

private noncomputable def bShape (x : ℝ) : ℝ :=
  -(9 / 25) * x + 6 / 5 - (6 / 5) * (1 + x) ^ (-(9 / 5 : ℝ)) -
    (9 / 5) * x * (1 + x) ^ (-(14 / 5 : ℝ))

private theorem bShape_nonneg {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 7 / 8) :
    0 ≤ bShape x := by
  let D (x : ℝ) := -(9 / 25) + (9 / 25) * (1 + x) ^ (-(14 / 5 : ℝ)) +
    (126 / 25) * x * (1 + x) ^ (-(19 / 5 : ℝ))
  let E (x : ℝ) := (1 + x) ^ (-(24 / 5 : ℝ)) * ((504 / 125) - (378 / 25) * x)
  have hd (t : ℝ) (ht : 0 ≤ t) : HasDerivAt bShape (D t) t := by
    have ht₀ : 0 < 1 + t := by positivity
    have h := (hasDerivAt_id t).const_add 1
    have h₁ := h.rpow_const (p := -(9 / 5 : ℝ)) (Or.inl ht₀.ne')
    have h₂ := h.rpow_const (p := -(14 / 5 : ℝ)) (Or.inl ht₀.ne')
    have h₀ := (((hasDerivAt_id t).const_mul (-(9 / 25))).add_const (6 / 5)).sub
      (h₁.const_mul (6 / 5))
    convert h₀.sub (((hasDerivAt_id t).mul h₂).const_mul (9 / 5)) using 1
    · funext z
      simp only [bShape, id_eq, Pi.sub_apply, Pi.mul_apply]
      ring
    · norm_num [D, id_eq] <;> ring
  have hD (t : ℝ) (ht : 0 ≤ t) : HasDerivAt D (E t) t := by
    have ht₀ : 0 < 1 + t := by positivity
    have h := (hasDerivAt_id t).const_add 1
    have h₁ := h.rpow_const (p := -(14 / 5 : ℝ)) (Or.inl ht₀.ne')
    have h₂ := h.rpow_const (p := -(19 / 5 : ℝ)) (Or.inl ht₀.ne')
    convert ((h₁.const_mul (9 / 25)).const_add (-(9 / 25))).add
      (((hasDerivAt_id t).mul h₂).const_mul (126 / 25)) using 1
    · funext z
      simp only [D, id_eq, Pi.add_apply, Pi.mul_apply]
      ring
    · norm_num [E, id_eq]
      have hR : (1 + t) ^ (-(19 / 5 : ℝ)) = (1 + t) ^ (-(24 / 5 : ℝ)) * (1 + t) := by
        rw [show -(24 / 5 : ℝ) = -(19 / 5 : ℝ) - 1 by norm_num,
          Real.rpow_sub_one ht₀.ne', div_mul_cancel₀ _ ht₀.ne']
      rw [hR]
      ring
  have hMonoD : MonotoneOn D (Icc 0 (4 / 15)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun t ht => (hD t ht.1).continuousAt.continuousWithinAt
    · exact fun t ht => (hD t (interior_subset ht).1).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Icc (0 : ℝ) (4 / 15) := interior_subset ht
      rw [(hD t ht'.1).deriv]
      exact mul_nonneg (Real.rpow_nonneg (by linarith [ht'.1]) _) (by linarith [ht'.2])
  have hMono : MonotoneOn bShape (Icc 0 (4 / 15)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun t ht => (hd t ht.1).continuousAt.continuousWithinAt
    · exact fun t ht => (hd t (interior_subset ht).1).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Icc (0 : ℝ) (4 / 15) := interior_subset ht
      rw [(hd t ht'.1).deriv]
      have h := hMonoD (by constructor <;> norm_num : (0 : ℝ) ∈ Icc 0 (4 / 15)) ht' ht'.1
      simpa only [D, zero_add, Real.one_rpow, mul_one, mul_zero, add_zero, neg_add_cancel] using h
  have hZero : bShape 0 = 0 := by norm_num [bShape]
  have hA : 0 ≤ bShape (4 / 15) := by
    rw [← hZero]
    exact hMono (by constructor <;> norm_num) (by constructor <;> norm_num) (by norm_num)
  rcases le_total x (4 / 15) with h | h
  · rw [← hZero]
    exact hMono (by constructor <;> norm_num) ⟨hx, h⟩ hx
  · have hConv : ConcaveOn ℝ (Icc (4 / 15) (7 / 8)) bShape := by
      apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
        (fun t ht => (hd t ((by norm_num : (0 : ℝ) ≤ 4 / 15).trans ht.1)).continuousAt.continuousWithinAt)
        (fun t ht => (hd t ((by norm_num : (0 : ℝ) ≤ 4 / 15).trans (interior_subset ht).1)).hasDerivWithinAt)
        (fun t ht => (hD t ((by norm_num : (0 : ℝ) ≤ 4 / 15).trans (interior_subset ht).1)).hasDerivWithinAt)
      intro t ht
      have ht' : t ∈ Icc (4 / 15 : ℝ) (7 / 8) := interior_subset ht
      exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (by linarith [ht'.1]) _)
        (by linarith [ht'.1])
    have hB : 0 ≤ bShape (7 / 8) := by
      have hR : (15 / 8 : ℝ) ^ (-(9 / 5 : ℝ)) < 2 / 5 := by
        convert fifth_rpow_upper (k := 9) (b := 15 / 8) (x := 2 / 5)
          (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
      unfold bShape
      rw [show (1 : ℝ) + 7 / 8 = 15 / 8 by norm_num,
        show -(14 / 5 : ℝ) = -(9 / 5 : ℝ) - 1 by norm_num,
        Real.rpow_sub_one (by norm_num : (15 / 8 : ℝ) ≠ 0)]
      linarith only [hR]
    let a := ((7 / 8 : ℝ) - x) / (7 / 8 - 4 / 15)
    let b := (x - (4 / 15 : ℝ)) / (7 / 8 - 4 / 15)
    have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr hx') (by norm_num)
    have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr h) (by norm_num)
    have hab : a + b = 1 := by dsimp only [a, b]; ring
    have hxE : a * (4 / 15) + b * (7 / 8) = x := by dsimp only [a, b]; ring
    have hT := hConv.2 (show (4 / 15 : ℝ) ∈ Icc (4 / 15) (7 / 8) by constructor <;> norm_num)
      (show (7 / 8 : ℝ) ∈ Icc (4 / 15) (7 / 8) by constructor <;> norm_num) ha hb hab
    simp only [smul_eq_mul, hxE] at hT
    exact (add_nonneg (mul_nonneg ha hA) (mul_nonneg hb hB)).trans hT

theorem upperBscaled_mono :
    MonotoneOn (fun x : ℝ => x ^ (-(6 / 5 : ℝ)) * purePeanoB (9 / 5) x 1) (Ioc 0 (7 / 8)) := by
  let g (x : ℝ) := (9 / 5) * x - 1 + (1 + x) ^ (-(9 / 5 : ℝ))
  have hG : (fun x : ℝ => purePeanoB (9 / 5) x 1) = g := by
    funext x
    simp only [purePeanoB, g, Real.one_rpow, mul_one]
    ring
  have hD (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun x : ℝ => x ^ (-(6 / 5 : ℝ)) * purePeanoB (9 / 5) x 1)
        (x ^ (-(11 / 5 : ℝ)) * bShape x) x := by
    have hx₁ : 0 < 1 + x := by positivity
    have h := (hasDerivAt_id x).const_add 1
    have hG' := (((hasDerivAt_id x).const_mul (9 / 5)).sub_const 1).add
      (h.rpow_const (p := -(9 / 5 : ℝ)) (Or.inl hx₁.ne'))
    simp_rw [congrFun hG]
    convert (Real.hasDerivAt_rpow_const (p := -(6 / 5 : ℝ)) (Or.inl hx.ne')).mul hG' using 1
    norm_num [bShape, g, id_eq]
    have hR : x ^ (-(6 / 5 : ℝ)) = x ^ (-(11 / 5 : ℝ)) * x := by
      rw [show -(11 / 5 : ℝ) = -(6 / 5 : ℝ) - 1 by norm_num,
        Real.rpow_sub_one hx.ne', div_mul_cancel₀ _ hx.ne']
    rw [hR]
    ring
  apply monotoneOn_of_deriv_nonneg (convex_Ioc _ _)
  · exact fun x hx => (hD x hx.1).continuousAt.continuousWithinAt
  · exact fun x hx => (hD x (interior_subset hx).1).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : x ∈ Ioc (0 : ℝ) (7 / 8) := interior_subset hx
    rw [(hD x hx'.1).deriv]
    exact mul_nonneg (Real.rpow_nonneg hx'.1.le _) (bShape_nonneg hx'.1.le hx'.2)

end ACS12.GammaMeasure

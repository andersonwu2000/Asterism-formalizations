import ACS12.LowLineConvex
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Elementary Bose shapes for signed sampling of the original rows. -/

namespace ACS12.BoseShape

open CenteredCircle.AllN Set Filter
open scoped Topology

noncomputable def C (x : ℝ) : ℝ := ((x - 1) * Real.exp x + 1) / (Real.exp x - 1) ^ 2

noncomputable def E (x : ℝ) : ℝ := 1 - C x

theorem expTail_derivative {x : ℝ} (hx : 0 < x) : HasDerivAt expTailFactor (-C x) x := by
  convert hasDerivAt_expTailFactor hx using 1
  unfold C
  rw [← neg_div]
  congr 1
  ring

theorem C_pos {x : ℝ} (hx : 0 < x) : 0 < C x := by
  have h := expTail_numerator_neg hx
  exact div_pos (by linarith only [h]) (sq_pos_of_pos (expTail_den_pos hx))

theorem C_lt_one {x : ℝ} (hx : 0 < x) : C x < 1 := by
  unfold C
  apply (div_lt_one (sq_pos_of_pos (expTail_den_pos hx))).mpr
  have h := mul_lt_mul_of_pos_right (Real.add_one_lt_exp hx.ne') (Real.exp_pos x)
  nlinarith only [h]

theorem expTail_eq_decay {x : ℝ} (hx : 0 < x) :
    expTailFactor x = x * Real.exp (-x) / (1 - Real.exp (-x)) := by
  have hd := (expTail_den_pos hx).ne'
  have he := (expHead_den_pos hx).ne'
  have h : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  unfold expTailFactor
  apply (div_eq_div_iff hd he).mpr
  calc
    x * (1 - Real.exp (-x)) = x * (Real.exp x * Real.exp (-x) - Real.exp (-x)) := by rw [h]
    _ = _ := by ring

theorem expTail_bounds {x : ℝ} (hx : 0 < x) :
    0 ≤ expTailFactor x ∧ expTailFactor x ≤ 1 := by
  refine ⟨(div_pos hx (expTail_den_pos hx)).le, ?_⟩
  exact (div_le_one (expTail_den_pos hx)).mpr (by linarith [Real.add_one_le_exp x])

noncomputable def decayConstant : ℝ := Real.exp 1 + (1 - Real.exp (-1))⁻¹ ^ 2

theorem decayConstant_pos : 0 < decayConstant := by
  exact add_pos_of_pos_of_nonneg (Real.exp_pos _) (sq_nonneg _)

theorem C_le_decay {x : ℝ} (hx : 0 < x) : C x ≤ decayConstant * (x + 1) * Real.exp (-x) := by
  have h1 : 0 < 1 - Real.exp (-1) := expHead_den_pos zero_lt_one
  have he : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  by_cases hx₁ : x ≤ 1
  · have hc : 1 ≤ Real.exp 1 * Real.exp (-x) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp_iff.mpr (by linarith)
    have hd : Real.exp 1 ≤ decayConstant := le_add_of_nonneg_right (sq_nonneg _)
    have hb : 1 ≤ x + 1 := by linarith
    calc
      C x ≤ 1 := (C_lt_one hx).le
      _ ≤ Real.exp 1 * Real.exp (-x) := hc
      _ ≤ decayConstant * (x + 1) * Real.exp (-x) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact hd.trans (le_mul_of_one_le_right decayConstant_pos.le hb)
  · have hx₁' : 1 ≤ x := le_of_not_ge hx₁
    have hb : 1 - Real.exp (-1) ≤ 1 - Real.exp (-x) :=
      sub_le_sub_left (Real.exp_le_exp.mpr (neg_le_neg hx₁')) _
    have hEq : C x = ((x - 1) * Real.exp (-x) + Real.exp (-x) ^ 2) /
        (1 - Real.exp (-x)) ^ 2 := by
      unfold C
      apply (div_eq_div_iff (pow_ne_zero _ (expTail_den_pos hx).ne')
        (pow_ne_zero _ (expHead_den_pos hx).ne')).mpr
      have hA : (x - 1) * Real.exp (-x) + Real.exp (-x) ^ 2 =
          ((x - 1) * Real.exp x + 1) * Real.exp (-x) ^ 2 := by
        linear_combination -(x - 1) * Real.exp (-x) * he
      rw [hA, mul_assoc, ← mul_pow, mul_sub, mul_comm (Real.exp (-x)) (Real.exp x), he, mul_one]
    rw [hEq]
    have h₀ := (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx.le))
    have hN : (x - 1) * Real.exp (-x) + Real.exp (-x) ^ 2 ≤ (x + 1) * Real.exp (-x) := by
      have h := mul_le_mul_of_nonneg_right h₀ (Real.exp_pos (-x)).le
      nlinarith only [h, Real.exp_pos (-x)]
    have hP : 0 ≤ (x + 1) * Real.exp (-x) := by positivity
    have hD : (1 - Real.exp (-1)) ^ 2 ≤ (1 - Real.exp (-x)) ^ 2 := by gcongr
    calc
      _ ≤ (x + 1) * Real.exp (-x) / (1 - Real.exp (-1)) ^ 2 :=
        div_le_div_of_nonneg_right hN (sq_nonneg _) |>.trans (div_le_div_of_nonneg_left hP
          (sq_pos_of_pos h1) hD)
      _ = (1 - Real.exp (-1))⁻¹ ^ 2 * (x + 1) * Real.exp (-x) := by
        rw [div_eq_mul_inv, inv_pow]
        ring
      _ ≤ decayConstant * (x + 1) * Real.exp (-x) := by
        unfold decayConstant
        gcongr
        linarith [Real.exp_pos (1 : ℝ)]

theorem positive_of_derivative {f d : ℝ → ℝ} (h0 : f 0 = 0)
    (hD : ∀ x, HasDerivAt f (d x) x) (hP : ∀ x > 0, 0 < d x) {x : ℝ} (hx : 0 < x) :
    0 < f x := by
  have h : StrictMonoOn f (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact fun t _ => (hD t).continuousAt.continuousWithinAt
    · intro t ht
      rw [(hD t).deriv]
      exact hP t (by simpa only [interior_Ici, mem_Ioi] using ht)
  rw [← h0]
  exact h (by simp) hx.le hx

noncomputable def expQuad (k a b c x : ℝ) : ℝ :=
  (a * x ^ 2 + b * x + c) * Real.exp (k * x)

theorem expQuad_deriv (k a b c x : ℝ) :
    HasDerivAt (expQuad k a b c) (expQuad k (k * a) (k * b + 2 * a) (k * c + b) x) x := by
  have hP := ((((hasDerivAt_id x).pow 2).const_mul a).add
    ((hasDerivAt_id x).const_mul b)).add_const c
  have hE := ((hasDerivAt_id x).const_mul k).exp
  convert hP.mul hE using 1
  simp only [expQuad, Pi.add_apply, Pi.pow_apply, id_eq, show (2 - 1 : ℕ) = 1 by decide, pow_one]
  ring

private noncomputable def curvature (x : ℝ) : ℝ := (x - 2) * Real.exp x + x + 2

private theorem curvature_pos {x : ℝ} (hx : 0 < x) : 0 < curvature x := by
  apply positive_of_derivative (d := fun t => (t - 1) * Real.exp t + 1) (by norm_num [curvature]) _ _ hx
  · intro t
    convert ((((hasDerivAt_id t).sub_const 2).mul (Real.hasDerivAt_exp t)).add
      (hasDerivAt_id t)).add_const 2 using 1
    simp only [id_eq, one_mul]
    ring
  · intro t ht
    apply positive_of_derivative (d := fun u => u * Real.exp u) (by norm_num) _ (fun u hu =>
      mul_pos hu (Real.exp_pos _)) ht
    intro u
    convert (((hasDerivAt_id u).sub_const 1).mul (Real.hasDerivAt_exp u)).add_const 1 using 1
    simp only [id_eq, one_mul]
    ring

theorem expHeadFactor_gt_one_add_half {x : ℝ} (hx : 0 < x) :
    1 + x / 2 < expHeadFactor x := by
  unfold expHeadFactor
  apply (lt_div_iff₀ (expHead_den_pos hx)).mpr
  have hE : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have h := mul_pos (curvature_pos hx) (Real.exp_pos (-x))
  unfold curvature at h
  rw [add_mul, add_mul, mul_assoc, hE, mul_one] at h
  nlinarith only [h]

noncomputable def C₁ (x : ℝ) : ℝ :=
  -Real.exp x * curvature x / (Real.exp x - 1) ^ 3

theorem C₁_measurable : Measurable C₁ := by
  unfold C₁ curvature
  fun_prop

theorem C_deriv {x : ℝ} (hx : 0 < x) : HasDerivAt C (C₁ x) x := by
  have he := Real.hasDerivAt_exp x
  have h := ((((hasDerivAt_id x).sub_const 1).mul he).add_const 1).div
    ((he.sub_const 1).pow 2) (pow_ne_zero _ (expTail_den_pos hx).ne')
  convert h using 1
  simp only [C₁, curvature, Pi.mul_apply, Pi.pow_apply, id_eq, one_mul,
    show (2 - 1 : ℕ) = 1 by decide, pow_one]
  field_simp [(expTail_den_pos hx).ne']
  ring

theorem C₁_neg {x : ℝ} (hx : 0 < x) : C₁ x < 0 := by
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos (Real.exp_pos _))
    (curvature_pos hx)) (pow_pos (expTail_den_pos hx) _)

theorem C_antitone : AntitoneOn C (Ioi 0) := by
  apply StrictAntiOn.antitoneOn
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · exact fun x hx => (C_deriv hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx₀ : 0 < x := by simpa only [interior_Ioi, mem_Ioi] using hx
    rw [(C_deriv hx₀).deriv]
    exact C₁_neg hx₀


theorem neg_C₁_eq {x : ℝ} (hx : 0 < x) :
    -C₁ x = Real.exp (-x) * ((x - 2) + (x + 2) * Real.exp (-x)) / (1 - Real.exp (-x)) ^ 3 := by
  unfold C₁ curvature
  rw [Real.exp_neg]
  have hE := Real.exp_ne_zero x
  have h := (expTail_den_pos hx).ne'
  have h' := (expHead_den_pos hx).ne'
  rw [Real.exp_neg] at h'
  field_simp [h,h',hE]
  ring

private noncomputable def convexNumerator (x : ℝ) : ℝ :=
  expQuad 2 0 1 (-3) x + expQuad 1 0 4 0 x + x + 3

private theorem convexNumerator_pos {x : ℝ} (hx : 0 < x) : 0 < convexNumerator x := by
  let f₁ (t : ℝ) := expQuad 2 0 2 (-5) t + expQuad 1 0 4 4 t + 1
  let f₂ (t : ℝ) := expQuad 2 0 4 (-8) t + expQuad 1 0 4 8 t
  let f₃ (t : ℝ) := expQuad 2 0 8 (-12) t + expQuad 1 0 4 12 t
  let f₄ (t : ℝ) := expQuad 2 0 16 (-16) t + expQuad 1 0 4 16 t
  apply positive_of_derivative (d := f₁) (by norm_num [convexNumerator, expQuad]) _ _ hx
  · intro t
    convert ((((expQuad_deriv 2 0 1 (-3) t).add (expQuad_deriv 1 0 4 0 t)).add
      (hasDerivAt_id t)).add_const 3) using 1
    norm_num [f₁]
  intro t ht
  apply positive_of_derivative (d := f₂) (by norm_num [f₁, expQuad]) _ _ ht
  · intro u
    convert (((expQuad_deriv 2 0 2 (-5) u).add (expQuad_deriv 1 0 4 4 u)).add_const 1) using 1
    norm_num [f₂]
  intro u hu
  apply positive_of_derivative (d := f₃) (by norm_num [f₂, expQuad]) _ _ hu
  · intro v
    convert ((expQuad_deriv 2 0 4 (-8) v).add (expQuad_deriv 1 0 4 8 v)) using 1
    norm_num [f₃]
  intro v hv
  apply positive_of_derivative (d := f₄) (by norm_num [f₃, expQuad]) _ _ hv
  · intro t
    convert ((expQuad_deriv 2 0 8 (-12) t).add (expQuad_deriv 1 0 4 12 t)) using 1
    norm_num [f₄]
  intro t ht
  have h0 : (1 - t) * Real.exp t < 1 := by
    have h := mul_lt_mul_of_pos_right (Real.add_one_lt_exp (neg_ne_zero.mpr ht.ne'))
      (Real.exp_pos t)
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
    simpa only [sub_eq_add_neg, add_comm] using h
  have hE : Real.exp (2 * t) = Real.exp t * Real.exp t := by
    rw [two_mul, Real.exp_add]
  dsimp only [f₄, expQuad]
  rw [hE, one_mul]
  have h1 : 0 < t + 4 - 4 * ((1 - t) * Real.exp t) := by linarith
  have h2 := mul_pos (Real.exp_pos t) h1
  nlinarith only [h2]

noncomputable def C₂ (x : ℝ) : ℝ :=
  Real.exp x * convexNumerator x / (Real.exp x - 1) ^ 4

theorem C₁_deriv {x : ℝ} (hx : 0 < x) : HasDerivAt C₁ (C₂ x) x := by
  have he := Real.hasDerivAt_exp x
  have hc := ((((hasDerivAt_id x).sub_const 2).mul he).add (hasDerivAt_id x)).add_const 2
  have h := (he.neg.mul hc).div ((he.sub_const 1).pow 3) (pow_ne_zero _ (expTail_den_pos hx).ne')
  convert h using 1
  simp only [C₂, convexNumerator, expQuad, Pi.mul_apply, Pi.add_apply, Pi.neg_apply,
    Pi.pow_apply, one_mul, id_eq, two_mul, Real.exp_add,
    show (3 - 1 : ℕ) = 2 by decide]
  field_simp [(expTail_den_pos hx).ne']
  ring

theorem C₂_pos {x : ℝ} (hx : 0 < x) : 0 < C₂ x :=
  div_pos (mul_pos (Real.exp_pos _) (convexNumerator_pos hx)) (pow_pos (expTail_den_pos hx) _)

theorem C₁_mono : MonotoneOn C₁ (Ioi 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioi _)
  · exact fun x hx => (C₁_deriv hx).continuousAt.continuousWithinAt
  · exact fun x hx => (C₁_deriv (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    have h := show x ∈ Ioi (0 : ℝ) from interior_subset hx
    rw [(C₁_deriv h).deriv]
    exact (C₂_pos h).le

theorem C_convex : ConvexOn ℝ (Ioi 0) C := by
  apply StrictConvexOn.convexOn
  apply strictConvexOn_of_deriv2_pos' (convex_Ioi 0)
  · exact fun x hx => (C_deriv hx).continuousAt.continuousWithinAt
  · intro x hx
    have he : deriv C =ᶠ[𝓝 x] C₁ := by
      filter_upwards [Ioi_mem_nhds hx] with t ht
      exact (C_deriv ht).deriv
    change 0 < deriv (deriv C) x
    rw [((C₁_deriv hx).congr_of_eventuallyEq he).deriv]
    exact div_pos (mul_pos (Real.exp_pos _) (convexNumerator_pos hx)) (pow_pos (expTail_den_pos hx) _)

private noncomputable def logNumerator (x : ℝ) : ℝ :=
  expQuad 3 0 0 1 x + expQuad 2 (-2) 3 (-5) x + expQuad 1 0 (-2) 7 x - x - 3

private theorem logNumerator_pos {x : ℝ} (hx : 0 < x) : 0 < logNumerator x := by
  let f₁ (t : ℝ) := expQuad 3 0 0 3 t + expQuad 2 (-4) 2 (-7) t + expQuad 1 0 (-2) 5 t - 1
  let f₂ (t : ℝ) := expQuad 3 0 0 9 t + expQuad 2 (-8) (-4) (-12) t + expQuad 1 0 (-2) 3 t
  let f₃ (t : ℝ) := expQuad 3 0 0 27 t + expQuad 2 (-16) (-24) (-28) t + expQuad 1 0 (-2) 1 t
  let f₄ (t : ℝ) := expQuad 3 0 0 81 t + expQuad 2 (-32) (-80) (-80) t + expQuad 1 0 (-2) (-1) t
  let f₅ (t : ℝ) := expQuad 3 0 0 243 t + expQuad 2 (-64) (-224) (-240) t + expQuad 1 0 (-2) (-3) t
  apply positive_of_derivative (d := f₁) (by norm_num [logNumerator, expQuad]) _ _ hx
  · intro t
    convert (((((expQuad_deriv 3 0 0 1 t).add (expQuad_deriv 2 (-2) 3 (-5) t)).add
      (expQuad_deriv 1 0 (-2) 7 t)).sub (hasDerivAt_id t)).sub_const 3) using 1
    norm_num [f₁]
  intro t ht
  apply positive_of_derivative (d := f₂) (by norm_num [f₁, expQuad]) _ _ ht
  · intro u
    convert ((((expQuad_deriv 3 0 0 3 u).add (expQuad_deriv 2 (-4) 2 (-7) u)).add
      (expQuad_deriv 1 0 (-2) 5 u)).sub_const 1) using 1
    norm_num [f₂]
  intro u hu
  apply positive_of_derivative (d := f₃) (by norm_num [f₂, expQuad]) _ _ hu
  · intro v
    convert (((expQuad_deriv 3 0 0 9 v).add (expQuad_deriv 2 (-8) (-4) (-12) v)).add
      (expQuad_deriv 1 0 (-2) 3 v)) using 1
    norm_num [f₃]
  intro v hv
  apply positive_of_derivative (d := f₄) (by norm_num [f₃, expQuad]) _ _ hv
  · intro t
    convert (((expQuad_deriv 3 0 0 27 t).add (expQuad_deriv 2 (-16) (-24) (-28) t)).add
      (expQuad_deriv 1 0 (-2) 1 t)) using 1
    norm_num [f₄]
  intro t ht
  apply positive_of_derivative (d := f₅) (by norm_num [f₄, expQuad]) _ _ ht
  · intro u
    convert (((expQuad_deriv 3 0 0 81 u).add (expQuad_deriv 2 (-32) (-80) (-80) u)).add
      (expQuad_deriv 1 0 (-2) (-1) u)) using 1
    norm_num [f₅]
  intro u hu
  have he := Real.quadratic_le_exp_of_nonneg hu.le
  have he₂ : Real.exp (2 * u) = Real.exp u ^ 2 := by rw [two_mul, Real.exp_add, sq]
  have he₃ : Real.exp (3 * u) = Real.exp u ^ 3 := by
    rw [show 3 * u = 2 * u + u by ring, Real.exp_add, he₂]
    ring
  have hq : 0 < 243 * Real.exp u - (64 * u ^ 2 + 224 * u + 240) - (2 * u + 3) := by
    nlinarith only [he, hu, sq_nonneg u]
  have hy := Real.exp_pos u
  have hY : 1 ≤ Real.exp u := Real.one_le_exp_iff.mpr hu.le
  have h := mul_pos hq (sq_pos_of_pos hy)
  have h' := mul_nonneg (show 0 ≤ (2 * u + 3) * Real.exp u by positivity) (sub_nonneg.mpr hY)
  dsimp only [f₅, expQuad]
  rw [he₃, he₂, one_mul]
  nlinarith only [h, h']

theorem E_pos {x : ℝ} (hx : 0 < x) : 0 < E x := sub_pos.mpr (C_lt_one hx)

private theorem E_deriv {x : ℝ} (hx : 0 < x) : HasDerivAt E (-C₁ x) x :=
  (C_deriv hx).const_sub 1

theorem E_div_antitone : AntitoneOn (fun x => E x / x) (Ioi 0) := by
  have hD (x : ℝ) (hx : 0 < x) := (E_deriv hx).div (hasDerivAt_id x) hx.ne'
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · exact fun x hx => (hD x hx).continuousAt.continuousWithinAt
  · exact fun x hx => (hD x (by simpa only [interior_Ioi, mem_Ioi] using hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx₀ : 0 < x := by simpa only [interior_Ioi, mem_Ioi] using hx
    change deriv (E / id) x ≤ 0
    rw [(hD x hx₀).deriv]
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg x)
    simp only [id_eq, mul_one]
    have hEc : ConcaveOn ℝ (Ioi 0) E := by
      simpa only [E, sub_eq_add_neg, add_comm, Pi.neg_apply] using C_convex.neg.add_const 1
    have hsec (y : ℝ) (hy : y ∈ Ioo 0 x) : (x - y) * -C₁ x ≤ E x := by
      have h := hEc.deriv_le_slope hy.1 hx₀ hy.2 (E_deriv hx₀).differentiableAt
      rw [(E_deriv hx₀).deriv, slope_def_field] at h
      rw [mul_comm]
      exact ((le_div_iff₀ (sub_pos.mpr hy.2)).mp h).trans (sub_le_self _ (E_pos hy.1).le)
    have ht : Tendsto (fun y : ℝ => (x - y) * -C₁ x) (𝓝[>] 0) (𝓝 (-C₁ x * x)) := by
      have hc : Continuous (fun y : ℝ => (x - y) * -C₁ x) := by fun_prop
      have h := (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
      simpa only [sub_zero, mul_comm x] using h
    have hI : ∀ᶠ y : ℝ in 𝓝[>] 0, y ∈ Ioo 0 x :=
      inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds hx₀))
    exact sub_nonpos.mpr (le_of_tendsto ht (hI.mono hsec))

private noncomputable def logSlope (x : ℝ) : ℝ := C₁ x / C x

private theorem logSlope_neg {x : ℝ} (hx : 0 < x) : logSlope x < 0 :=
  div_neg_of_neg_of_pos (C₁_neg hx) (C_pos hx)

private theorem logSlope_antitone : AntitoneOn logSlope (Ioi 0) := by
  have hD (x : ℝ) (hx : 0 < x) := (C₁_deriv hx).div (C_deriv hx) (C_pos hx).ne'
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · exact fun x hx => (hD x hx).continuousAt.continuousWithinAt
  · exact fun x hx => (hD x (by simpa only [interior_Ioi, mem_Ioi] using hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx₀ : 0 < x := by simpa only [interior_Ioi, mem_Ioi] using hx
    change deriv (C₁ / C) x ≤ 0
    rw [(hD x hx₀).deriv]
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    have he : C₂ x * C x - C₁ x * C₁ x =
        -Real.exp x * logNumerator x / (Real.exp x - 1) ^ 6 := by
      simp only [C₂, C₁, C, curvature, convexNumerator, logNumerator, expQuad, one_mul,
        two_mul, show (3 : ℝ) * x = x + x + x by ring, Real.exp_add]
      field_simp [(expTail_den_pos hx₀).ne']
      ring
    rw [he]
    exact (div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos (Real.exp_pos _))
      (logNumerator_pos hx₀)) (pow_pos (expTail_den_pos hx₀) _)).le

theorem C_ratio_antitone {q : ℝ} (hq : 1 ≤ q) :
    AntitoneOn (fun x => C (q * x) / C x) (Ioi 0) := by
  have hq₀ : 0 < q := zero_lt_one.trans_le hq
  have hD (x : ℝ) (hx : 0 < x) :=
    (((C_deriv (mul_pos hq₀ hx)).comp x ((hasDerivAt_id x).const_mul q)).div
      (C_deriv hx) (C_pos hx).ne')
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · exact fun x hx => (hD x hx).continuousAt.continuousWithinAt
  · exact fun x hx => (hD x (by simpa only [interior_Ioi, mem_Ioi] using hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx₀ : 0 < x := by simpa only [interior_Ioi, mem_Ioi] using hx
    have hqx := mul_pos hq₀ hx₀
    change deriv (C ∘ (fun x => q * x) / C) x ≤ 0
    rw [(hD x hx₀).deriv]
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    simp only [Function.comp_apply]
    have hOrder := logSlope_antitone hx₀ hqx (le_mul_of_one_le_left hx₀.le hq)
    have hScale : q * logSlope (q * x) ≤ logSlope (q * x) :=
      mul_le_of_one_le_left (logSlope_neg hqx).le hq
    have hProd := mul_le_mul_of_nonneg_right (hScale.trans hOrder) (mul_pos (C_pos hqx) (C_pos hx₀)).le
    unfold logSlope at hProd
    have hL : q * (C₁ (q * x) / C (q * x)) * (C (q * x) * C x) =
        q * C₁ (q * x) * C x := by
      field_simp [(C_pos hqx).ne']
    have hR : C₁ x / C x * (C (q * x) * C x) = C (q * x) * C₁ x := by
      field_simp [(C_pos hx₀).ne']
    rw [hL, hR] at hProd
    nlinarith only [hProd]

end ACS12.BoseShape


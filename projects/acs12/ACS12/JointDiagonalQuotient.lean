import ACS12.JointLowerSourceThird

/-! The normalized moving diagonal extends at zero by its genuine derivative. -/
namespace ACS12.GammaMeasure

open MeasureTheory Set

theorem quotient_convex_of_third_nonneg {f d₁ d₂ d₃ : ℝ → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hf : f 0 = 0)
    (h₁ : ∀ x ∈ Icc 0 R, HasDerivAt f (d₁ x) x)
    (h₂ : ∀ x ∈ Icc 0 R, HasDerivAt d₁ (d₂ x) x)
    (h₃ : ∀ x ∈ Icc 0 R, HasDerivAt d₂ (d₃ x) x)
    (hP : ∀ x ∈ Icc 0 R, 0 ≤ d₃ x) :
    ConvexOn ℝ (Icc 0 R) (fun x => if x = 0 then d₁ 0 else f x / x) := by
  have hConv : ConvexOn ℝ (Icc 0 R) d₁ :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (fun x hx => (h₂ x hx).continuousAt.continuousWithinAt)
      (fun x hx => (h₂ x (interior_subset hx)).hasDerivWithinAt)
      (fun x hx => (h₃ x (interior_subset hx)).hasDerivWithinAt)
      (fun x hx => hP x (interior_subset hx))
  have hMem {x t : ℝ} (hx : x ∈ Icc 0 R) (ht : t ∈ Icc (0 : ℝ) 1) : t * x ∈ Icc 0 R :=
    ⟨mul_nonneg ht.1 hx.1,(mul_le_of_le_one_left hx.1 ht.2).trans hx.2⟩
  let F (x t : ℝ) := d₁ (t * x)
  have hC : ContinuousOn d₁ (Icc 0 R) := fun x hx => (h₂ x hx).continuousAt.continuousWithinAt
  have hI (x : ℝ) (hx : x ∈ Icc 0 R) : IntervalIntegrable (F x) volume 0 1 := by
    have h : ContinuousOn (fun t : ℝ => t * x) (Icc 0 1) := by fun_prop
    exact (hC.comp h (fun t ht => hMem hx ht)).intervalIntegrable_of_Icc zero_le_one
  have hValue (x : ℝ) (hx : x ∈ Icc 0 R) :
      (if x = 0 then d₁ 0 else f x / x) = ∫ t in (0 : ℝ)..1, F x t := by
    by_cases hx₀ : x = 0
    · subst x
      simp [F]
    · rw [if_neg hx₀]
      have hI' : IntervalIntegrable d₁ volume 0 x :=
        (hC.mono (Icc_subset_Icc_right hx.2)).intervalIntegrable_of_Icc hx.1
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := x)
        (fun y hy => h₁ y (Icc_subset_Icc_right hx.2 (by rwa [uIcc_of_le hx.1] at hy))) hI'
      have hScale := intervalIntegral.smul_integral_comp_mul_right (a := 0) (b := 1) d₁ x
      simp only [smul_eq_mul,zero_mul,one_mul,h,hf,sub_zero] at hScale
      exact (div_eq_iff hx₀).mpr (by unfold F; rw [mul_comm]; exact hScale.symm)
  refine ⟨convex_Icc _ _,?_⟩
  intro x hx y hy a b ha hb hab
  have hxy : a * x + b * y ∈ Icc 0 R := by
    simpa only [smul_eq_mul] using (convex_Icc (0 : ℝ) R) hx hy ha hb hab
  simp only [smul_eq_mul]
  rw [hValue _ hxy,hValue _ hx,hValue _ hy,← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul,← intervalIntegral.integral_add ((hI x hx).const_mul a) ((hI y hy).const_mul b)]
  apply intervalIntegral.integral_mono_on zero_le_one (hI _ hxy)
    (((hI x hx).const_mul a).add ((hI y hy).const_mul b))
  intro t ht
  have h := hConv.2 (hMem hx ht) (hMem hy ht) ha hb hab
  simp only [smul_eq_mul] at h
  unfold F
  rw [show t * (a * x + b * y) = a * (t * x) + b * (t * y) by ring]
  exact h

end ACS12.GammaMeasure

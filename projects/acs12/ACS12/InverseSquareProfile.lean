import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-! Direct inverse convexity of a positive increasing concave power profile. -/
namespace ACS12
open Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

noncomputable def inverseSquareProfile (c : ℝ) (f : ℝ → ℝ) (N : ℝ) :=
  1/(c*N^2*f (N^2))
noncomputable def inverseSquareProfileFirst (c : ℝ) (f f₁ : ℝ → ℝ) (N : ℝ) :=
  -(2*f (N^2)+2*N^2*f₁ (N^2))/(c*N^3*(f (N^2))^2)
noncomputable def inverseSquareProfileSecond (c : ℝ) (f f₁ f₂ : ℝ → ℝ) (N : ℝ) :=
  (6*(f (N^2))^2+6*N^2*f (N^2)*f₁ (N^2)+8*N^4*(f₁ (N^2))^2-
    4*N^4*f (N^2)*f₂ (N^2))/(c*N^4*(f (N^2))^3)

theorem inverseSquareProfile_deriv {c N : ℝ} {f f₁ : ℝ → ℝ}
    (hc : c ≠ 0) (hN : N ≠ 0) (hf : f (N^2) ≠ 0)
    (hF : HasDerivAt f (f₁ (N^2)) (N^2)) :
    HasDerivAt (inverseSquareProfile c f) (inverseSquareProfileFirst c f f₁ N) N := by
  have hSq : HasDerivAt (fun x : ℝ => x^2) (2*N) N := by
    convert (hasDerivAt_id N).pow 2 using 1 <;> simp
  have hFN := hF.comp_of_eq N hSq rfl
  have h := (hasDerivAt_const N (1:ℝ)).div
    ((hSq.const_mul c).mul hFN) (show c*N^2*f (N^2)≠0 by positivity)
  convert h using 1
  simp only [inverseSquareProfileFirst,mul_one,zero_mul,zero_sub,one_mul,
    Function.comp_apply,Pi.mul_apply,Pi.pow_apply,id_eq]
  field_simp [hc,hN,hf]
  <;> ring

theorem inverseSquareProfileFirst_deriv {c N : ℝ} {f f₁ f₂ : ℝ → ℝ}
    (hc : c ≠ 0) (hN : N ≠ 0) (hf : f (N^2) ≠ 0)
    (hF : HasDerivAt f (f₁ (N^2)) (N^2))
    (hF₁ : HasDerivAt f₁ (f₂ (N^2)) (N^2)) :
    HasDerivAt (inverseSquareProfileFirst c f f₁)
      (inverseSquareProfileSecond c f f₁ f₂ N) N := by
  have hSq : HasDerivAt (fun x : ℝ => x^2) (2*N) N := by
    convert (hasDerivAt_id N).pow 2 using 1 <;> simp
  have hFN := hF.comp_of_eq N hSq rfl
  have hF₁N := hF₁.comp_of_eq N hSq rfl
  have hNum := ((hFN.const_mul 2).add ((hSq.const_mul 2).mul hF₁N)).neg
  have hDen := (((hasDerivAt_id N).pow 3).const_mul c).mul (hFN.pow 2)
  have h := hNum.div hDen (show c*N^3*(f (N^2))^2≠0 by positivity)
  convert h using 1
  simp only [inverseSquareProfileSecond,id_eq,mul_one,Nat.cast_ofNat,
    Nat.reduceSub,pow_one,Function.comp_apply,Pi.mul_apply,Pi.pow_apply,
    Pi.add_apply,Pi.neg_apply]
  generalize hFv : f (N^2)=F at hf ⊢
  field_simp [hc,hN,hf]
  ring

theorem inverseSquareProfile_convex {c : ℝ} {f f₁ f₂ : ℝ → ℝ}
    (hc : 0 < c)
    (hF : ∀ z>0, HasDerivAt f (f₁ z) z)
    (hF₁ : ∀ z>0, HasDerivAt f₁ (f₂ z) z)
    (hf : ∀ z>0, 0 < f z) (hf₁ : ∀ z>0, 0 ≤ f₁ z) (hf₂ : ∀ z>0, f₂ z ≤ 0) :
    ConvexOn ℝ (Ioi 0) (inverseSquareProfile c f) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi _)
    (f':=inverseSquareProfileFirst c f f₁) (f'':=inverseSquareProfileSecond c f f₁ f₂)
  · intro N hN
    exact (inverseSquareProfile_deriv hc.ne' hN.ne' (hf _ (sq_pos_of_pos hN)).ne'
      (hF _ (sq_pos_of_pos hN))).continuousAt.continuousWithinAt
  · intro N hN
    have hN' : 0<N := interior_subset hN
    exact (inverseSquareProfile_deriv hc.ne' hN'.ne' (hf _ (sq_pos_of_pos hN')).ne'
      (hF _ (sq_pos_of_pos hN'))).hasDerivWithinAt
  · intro N hN
    have hN' : 0<N := interior_subset hN
    exact (inverseSquareProfileFirst_deriv hc.ne' hN'.ne' (hf _ (sq_pos_of_pos hN')).ne'
      (hF _ (sq_pos_of_pos hN')) (hF₁ _ (sq_pos_of_pos hN'))).hasDerivWithinAt
  · intro N hN
    have hN' : 0<N := interior_subset hN
    have hPos := hf _ (sq_pos_of_pos hN')
    have hFirst := hf₁ _ (sq_pos_of_pos hN')
    have hSecond := hf₂ _ (sq_pos_of_pos hN')
    unfold inverseSquareProfileSecond
    apply div_nonneg _ (by positivity)
    have hNeg : 0 ≤ -(4*N^4*f (N^2)*f₂ (N^2)) := neg_nonneg.mpr
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) hSecond)
    have hPos₁ : 0 ≤ 6*N^2*f (N^2)*f₁ (N^2) := by positivity
    nlinarith only [hNeg,hPos₁,sq_nonneg (f (N^2)),
      mul_nonneg (pow_nonneg hN'.le 4) (sq_nonneg (f₁ (N^2)))]

/-- The positive constant term makes reciprocal convexity strict even when
the underlying increasing concave profile is constant. -/
theorem inverseSquareProfile_strictConvex {c : ℝ} {f f₁ f₂ : ℝ → ℝ}
    (hc : 0 < c)
    (hF : ∀ z>0, HasDerivAt f (f₁ z) z)
    (hF₁ : ∀ z>0, HasDerivAt f₁ (f₂ z) z)
    (hf : ∀ z>0, 0 < f z) (hf₁ : ∀ z>0, 0 ≤ f₁ z) (hf₂ : ∀ z>0, f₂ z ≤ 0) :
    StrictConvexOn ℝ (Ioi 0) (inverseSquareProfile c f) := by
  apply strictConvexOn_of_deriv2_pos' (convex_Ioi _)
  · intro N hN
    exact (inverseSquareProfile_deriv hc.ne' hN.ne' (hf _ (sq_pos_of_pos hN)).ne'
      (hF _ (sq_pos_of_pos hN))).continuousAt.continuousWithinAt
  · intro N hN
    have hD : deriv (inverseSquareProfile c f) =ᶠ[𝓝 N]
        inverseSquareProfileFirst c f f₁ := by
      filter_upwards [Ioi_mem_nhds hN] with x hx
      exact (inverseSquareProfile_deriv hc.ne' hx.ne' (hf _ (sq_pos_of_pos hx)).ne'
        (hF _ (sq_pos_of_pos hx))).deriv
    have h := (inverseSquareProfileFirst_deriv hc.ne' hN.ne' (hf _ (sq_pos_of_pos hN)).ne'
      (hF _ (sq_pos_of_pos hN)) (hF₁ _ (sq_pos_of_pos hN))).congr_of_eventuallyEq hD
    change 0 < deriv (deriv (inverseSquareProfile c f)) N
    rw [h.deriv]
    have hPos := hf _ (sq_pos_of_pos hN)
    have hFirst := hf₁ _ (sq_pos_of_pos hN)
    have hSecond := hf₂ _ (sq_pos_of_pos hN)
    unfold inverseSquareProfileSecond
    apply div_pos _ (mul_pos (mul_pos hc (pow_pos hN 4)) (pow_pos hPos 3))
    have hNeg : 0 ≤ -(4*N^4*f (N^2)*f₂ (N^2)) := neg_nonneg.mpr
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) hSecond)
    have hPos₁ : 0 ≤ 6*N^2*f (N^2)*f₁ (N^2) := by positivity
    nlinarith only [hNeg,hPos₁,sq_pos_of_pos hPos,
      mul_nonneg (pow_nonneg hN.le 4) (sq_nonneg (f₁ (N^2)))]

end ACS12

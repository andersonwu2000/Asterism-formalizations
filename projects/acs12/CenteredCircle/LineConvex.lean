import CenteredCircle.LineRational

/-! Convexity of the exact line scalar, proved term by term for its rational series. -/

namespace CenteredCircle.AllN

open Set Filter
open scoped Topology

noncomputable def scaledRightProfile (t : ℝ) : ℝ := (3 * t + 4) / (4 * t * (t + 1) ^ 2)
noncomputable def scaledRightSlope (t : ℝ) : ℝ := -(3 * t ^ 2 + 6 * t + 2) / (2 * t ^ 2 * (t + 1) ^ 3)

theorem scaledRightProfile_eq {t : ℝ} (ht : 0 < t) : scaledRightProfile t = t * comparisonG t := by
  have ht1 : 0 < t + 1 := by linarith
  dsimp [scaledRightProfile, comparisonG]
  field_simp
  <;> ring

theorem hasDerivAt_scaledRightProfile {t : ℝ} (ht : 0 < t) :
    HasDerivAt scaledRightProfile (scaledRightSlope t) t := by
  have ht1 : 0 < t + 1 := by linarith
  have hn := ((hasDerivAt_id t).const_mul 3).add_const 4
  have hd := ((hasDerivAt_id t).const_mul 4).mul (((hasDerivAt_id t).add_const 1).pow 2)
  convert hn.div hd (by positivity : 4 * t * (t + 1) ^ 2 ≠ 0) using 1
  dsimp [scaledRightSlope]
  field_simp
  <;> ring

theorem hasDerivAt_scaledRightSlope {t : ℝ} (ht : 0 < t) :
    HasDerivAt scaledRightSlope
      ((9 * t ^ 3 + 24 * t ^ 2 + 16 * t + 4) / (2 * t ^ 3 * (t + 1) ^ 4)) t := by
  have ht1 : 0 < t + 1 := by linarith
  have hn := (((((hasDerivAt_id t).pow 2).const_mul 3).add
    ((hasDerivAt_id t).const_mul 6)).add_const 2).neg
  have hd := (((hasDerivAt_id t).pow 2).const_mul 2).mul
    (((hasDerivAt_id t).add_const 1).pow 3)
  convert hn.div hd (by positivity : 2 * t ^ 2 * (t + 1) ^ 3 ≠ 0) using 1
  dsimp
  field_simp
  <;> ring

theorem strictConvexOn_scaledRightProfile : StrictConvexOn ℝ (Ioi 0) scaledRightProfile := by
  apply strictConvexOn_of_deriv2_pos' (convex_Ioi 0)
  · intro t ht
    exact (hasDerivAt_scaledRightProfile ht).continuousAt.continuousWithinAt
  · intro t ht
    have he : deriv scaledRightProfile =ᶠ[𝓝 t] scaledRightSlope := by
      filter_upwards [Ioi_mem_nhds ht] with x hx
      exact (hasDerivAt_scaledRightProfile hx).deriv
    have hd := (hasDerivAt_scaledRightSlope ht).congr_of_eventuallyEq he
    change 0 < deriv (deriv scaledRightProfile) t
    rw [hd.deriv]
    change 0 < t at ht
    positivity

theorem convexOn_scaled_comparisonG {n : ℝ} (hn : 0 < n) :
    ConvexOn ℝ (Ioi 0) (fun b => b * comparisonG (n * b)) := by
  have hprofile := strictConvexOn_scaledRightProfile.convexOn
  have he (b : ℝ) (hb : 0 < b) : b * comparisonG (n * b) = scaledRightProfile (n * b) / n := by
    rw [scaledRightProfile_eq (mul_pos hn hb)]
    field_simp
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have hc : 0 < a * x + b * y := by
    simpa only [smul_eq_mul] using (convex_Ioi (0 : ℝ)) hx hy ha hb hab
  have h := hprofile.2 (mul_pos hn hx) (mul_pos hn hy) ha hb hab
  simp only [smul_eq_mul] at h ⊢
  rw [he _ hc, he x hx, he y hy]
  have hd := div_le_div_of_nonneg_right h hn.le
  convert hd using 1 <;> congr 1 <;> ring

theorem rationalPair_convex (j : ℕ) : ConvexOn ℝ (Ioi 0) (fun b => rationalPair b j) := by
  have h := convexOn_scaled_comparisonG (n := (j : ℝ) + 1) (by positivity)
  exact (convexOn_const (comparisonF ((j : ℝ) + 1)) (convex_Ioi (0 : ℝ))).add h

theorem convexOn_tsum_of_summable {f : ℕ → ℝ → ℝ} {S : Set ℝ}
    (hc : Convex ℝ S) (hf : ∀ j, ConvexOn ℝ S (f j))
    (hs : ∀ x ∈ S, Summable (fun j => f j x)) :
    ConvexOn ℝ S (fun x => ∑' j : ℕ, f j x) := by
  refine ⟨hc, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxy := hc hx hy ha hb hab
  have h := (hs _ hxy).tsum_le_tsum (fun j => (hf j).2 hx hy ha hb hab)
    (((hs x hx).mul_left a).add ((hs y hy).mul_left b))
  simp only [smul_eq_mul] at h ⊢
  rw [((hs x hx).mul_left a).tsum_add ((hs y hy).mul_left b), tsum_mul_left, tsum_mul_left] at h
  exact h

theorem lineScalar_convex : ConvexOn ℝ (Ioi 0) lineScalar := by
  have hsum : ConvexOn ℝ (Ioi 0) (fun b => ∑' j : ℕ, rationalPair b j) :=
    convexOn_tsum_of_summable (convex_Ioi 0) rationalPair_convex
      (fun b hb => rationalPair_summable hb)
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxy : 0 < a * x + b * y := by
    simpa only [smul_eq_mul] using (convex_Ioi (0 : ℝ)) hx hy ha hb hab
  have h := hsum.2 hx hy ha hb hab
  simp only [smul_eq_mul] at h ⊢
  rw [lineScalar_eq_rational hxy, lineScalar_eq_rational hx, lineScalar_eq_rational hy]
  nlinarith

end CenteredCircle.AllN

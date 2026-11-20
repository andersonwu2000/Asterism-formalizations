import ACS12.JointLowerSourceIdentity
import ACS12.PowerConvex

/-! Convexity of the fourth row after restoring its exact zero-gap debit. -/
namespace ACS12.GammaMeasure

open Set MeasureTheory Filter CenteredCircle.AllN
open GammaDeficit (lineDensity)

private noncomputable def fourthDiagonalFirst (p L u m : ℝ) : ℝ :=
  u * lawPeanoKernel p L 0 m .b u + samplingTail (lawPeanoKernel p L 0 m .b) u 1

private theorem fourthDiagonalFirst_integral {p L u m : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hL : 0 < L)
    (hu : 0 < u) (hm : 0 < m) :
    IntegrableOn (fun s => lineDensity p s * polyB (m * s) * fourthFirstStream u s) (Ioi 0) ∧
      fourthDiagonalFirst p L u m = ∫ s : ℝ in Ioi 0, lineDensity p s * polyB (m * s) * fourthFirstStream u s := by
  have h0 : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  let f (s : ℝ) := lawPeanoDensity p L 0 m .b s * Real.exp (-s * u)
  have hf : IntegrableOn f (Ioi 0) := lawPeanoKernel_integrable hp hp₂ hL h0 hm hu .b
  obtain ⟨hg,hgE⟩ := lawPeanoTail_sampling hp hp₂ hL h0 hm hu.le zero_lt_one .b
  have he (s : ℝ) : lineDensity p s * polyB (m * s) * fourthFirstStream u s = u * f s + f s * scaledExpTail s 1 := by
    simp only [f,lawPeanoDensity,lawDensity,densityPolynomial,sub_zero,one_mul,zero_mul,add_zero,fourthFirstStream]
    ring
  refine ⟨((hf.const_mul u).add hg).congr (Eventually.of_forall (fun s => (he s).symm)),?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => he s),integral_add (hf.const_mul u) hg,
    integral_const_mul,← hgE]
  rfl

private theorem fourthDiagonalFirst_convex {p L u : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hL : 0 < L) (hu : 0 < u) :
    ConvexOn ℝ (Ioi 0) (fourthDiagonalFirst p L u) := by
  refine ⟨convex_Ioi _,?_⟩
  intro x hx y hy a b ha hb hab
  let m := a * x + b * y
  let F (r s : ℝ) := lineDensity p s * polyB (r * s) * fourthFirstStream u s
  have hm : 0 < m := convex_Ioi (0 : ℝ) hx hy ha hb hab
  have hI (r : ℝ) (hr : 0 < r) := fourthDiagonalFirst_integral hp hp₂ hL hu hr
  have h : (∫ s : ℝ in Ioi 0, F m s) ≤ ∫ s : ℝ in Ioi 0, (a * F x s + b * F y s) := by
    apply integral_mono_ae (hI m hm).1 (((hI x hx).1.const_mul a).add ((hI y hy).1.const_mul b))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0 < s := hs
    have hB : ConvexOn ℝ (Ioi 0) polyB := by
      apply convexOn_of_hasDerivWithinAt2_nonneg (f' := fun x => 1 - Real.exp (-x))
        (f'' := fun x => Real.exp (-x)) (convex_Ioi _)
      · exact fun r _ => (hasDerivAt_polyB r).continuousAt.continuousWithinAt
      · exact fun r _ => (hasDerivAt_polyB r).hasDerivWithinAt
      · intro r hr
        simpa only [id_eq,Pi.neg_apply,mul_neg,mul_one,neg_neg] using
          (((hasDerivAt_id r).neg.exp).const_sub (1 : ℝ)).hasDerivWithinAt (s := interior (Ioi 0))
      · exact fun r _ => (Real.exp_pos (-r)).le
    have hC := hB.2 (mem_Ioi.mpr (mul_pos (show 0 < x from hx) hs₀))
      (mem_Ioi.mpr (mul_pos (show 0 < y from hy) hs₀)) ha hb hab
    simp only [smul_eq_mul] at hC
    rw [show a * (x * s) + b * (y * s) = m * s by unfold m; ring] at hC
    have hT : 0 ≤ fourthFirstStream u s := by
      have hβ : 0 < scaledExpTail s 1 := div_pos zero_lt_one (expTail_den_pos (by simpa only [mul_one] using hs₀))
      unfold fourthFirstStream
      positivity
    have hD := mul_le_mul_of_nonneg_left hC (mul_nonneg (lineDensity_pos (zero_lt_one.trans_le hp) hs₀).le hT)
    change F m s ≤ a * F x s + b * F y s
    unfold F
    nlinarith only [hD]
  rw [integral_add ((hI x hx).1.const_mul a) ((hI y hy).1.const_mul b),integral_const_mul,integral_const_mul,
    ← (hI x hx).2,← (hI y hy).2,← (hI m hm).2] at h
  exact h

private theorem jointFourth_diagonal_eq {p L u m : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hL : 0 < L)
    (hm : 0 < m) :
    fourthSourceRow p L 0 u m m m = fourthDiagonalFirst p L u m - (pureZ p - 1) * m ^ (1 - p) := by
  have hA : samplingTail (lawPeanoKernel p L 0 m .a) 0 m = samplingTail (purePeanoA p m) 0 m := by
    unfold samplingTail
    apply congrArg (fun x : ℝ => m * x)
    exact tsum_congr (fun j => (lawPeanoKernel_zero hp hp₂ hL hm
      (show 0 < 0 + ((j + 1 : ℕ) : ℝ) * m by positivity)).1)
  unfold fourthSourceRow fourthDiagonalFirst
  dsimp only
  rw [hA,purePeanoA_tail_self hm,rightSourceSum_zero_one hp hp₂,lawMoment_zero_slope (zero_lt_one.trans_le hp) hm]
  simp only [sub_self,zero_mul,add_zero]
  rw [show -(p + 1) = -p - 1 by ring,Real.rpow_sub_one hm.ne',
    show 1 - p = -p + 1 by ring,Real.rpow_add_one hm.ne']
  field_simp [hm.ne'] <;> ring

theorem fourthDiagonal_convex_restored {p L u : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (huL : 7 / 8 ≤ u) :
    ConvexOn ℝ (Icc (2 * u - 1) u) (fun m =>
      fourthSourceRow p L 0 u m m m + (pureZ p - 1) * m ^ (1 - p)) := by
  have hu : 0 < u := by linarith only [huL]
  have hI (m : ℝ) (hm : m ∈ Icc (2 * u - 1) u) : 0 < m := by linarith only [hm.1,huL]
  apply ((fourthDiagonalFirst_convex hp hp₂ hL hu).subset (fun m hm => hI m hm) (convex_Icc _ _)).congr
  intro m hm
  dsimp only
  rw [jointFourth_diagonal_eq hp hp₂ hL (hI m hm)]
  ring

end ACS12.GammaMeasure

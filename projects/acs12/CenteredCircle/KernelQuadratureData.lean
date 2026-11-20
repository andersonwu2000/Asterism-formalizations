import CenteredCircle.ConvexTailSampling

/-! Verified sampling data on the domain actually occupied by a source. -/

namespace CenteredCircle.AllN

open Set

structure QuadratureData (K : ℝ → ℝ) (d : ℝ) : Prop where
  nonneg : ∀ x, d ≤ x → 0 ≤ K x
  summable : ∀ x s, d ≤ x → 0 < s → Summable (fun j : ℕ => K (x + j * s))
  head_mono : ∀ x, d ≤ x → MonotoneOn (samplingHead K x) (Ioi 0)
  tail_anti : ∀ x, d ≤ x → AntitoneOn (samplingTail K x) (Ioi 0)
  boundary_anti : AntitoneOn (samplingTail K 0) (Ici d)

theorem summable_tail_shift {K : ℝ → ℝ} {t s : ℝ}
    (h : Summable (fun j : ℕ => K ((t + s) + j * s))) :
    Summable (fun j : ℕ => K (t + (j + 1 : ℕ) * s)) := by
  convert h using 1
  funext j
  congr 1
  push_cast
  ring

theorem convex_cubic_quadratureData {K : ℝ → ℝ} {d C : ℝ}
    (hd : 0 < d) (hC : 0 ≤ C)
    (hc : ConvexOn ℝ (Ici d) K) (hp : ∀ x, d ≤ x → 0 ≤ K x)
    (hdiff : ∀ x, d ≤ x → DifferentiableAt ℝ K x)
    (hbound : ∀ x, d ≤ x → K x ≤ C / x ^ 3)
    (hsum : ∀ x s, d ≤ x → 0 < s → Summable (fun j : ℕ => K (x + j * s))) :
    QuadratureData K d := by
  refine ⟨hp, hsum, ?_, ?_, ?_⟩
  · intro x hx
    exact samplingHead_monotone_of_convex hc hp hdiff hx (hsum x · hx ·)
  · intro x hx
    apply samplingTail_antitone_of_convex hc hdiff hC (fun x hx _ => hbound x hx)
      (le_trans hd.le hx) hx
    intro s hs
    exact summable_tail_shift (hsum (x + s) s (by linarith) hs)
  · apply samplingTail_boundary_antitone_of_convex hc hdiff hC
      (fun x hx _ => hbound x hx) hd
    intro s hs
    have hh := summable_tail_shift (t := 0)
      (by simpa only [zero_add] using hsum s s hs (lt_of_lt_of_le hd hs))
    simpa only [zero_add] using hh

theorem mixedLeftKernel_quadratureData {L : ℝ} (hL : 0 < L) :
    QuadratureData (mixedLeftKernel L) 1 := by
  apply convex_cubic_quadratureData (C := 1) (by norm_num) (by norm_num)
    (strictConvexOn_mixedLeftKernel hL).convexOn
  · intro x hx
    exact (mixedLeftKernel_pos hL hx).le
  · intro x hx
    exact (hasDerivAt_leftMixedMoment hL (by linarith : 0 < x) 0).differentiableAt
  · intro x hx
    exact mixedLeftKernel_le_cubic hL (by linarith)
  · intro x s hx hs
    exact mixedLeftKernel_summable hL (by linarith) hs

theorem mixedRightKernel_quadratureData {L d : ℝ} (hL : 0 < L) (hd : 0 < d) :
    QuadratureData (mixedRightKernel L) d := by
  apply convex_cubic_quadratureData (C := 1) hd (by norm_num)
    ((strictConvexOn_mixedRightKernel hL).convexOn.subset
      (fun x hx => lt_of_lt_of_le hd hx) (convex_Ici d))
  · intro x hx
    exact (mixedRightKernel_pos hL (lt_of_lt_of_le hd hx)).le
  · intro x hx
    exact (hasDerivAt_rightMixedMoment hL (lt_of_lt_of_le hd hx) 0).differentiableAt
  · intro x hx
    exact mixedRightKernel_le_cubic hL (lt_of_lt_of_le hd hx)
  · intro x s hx hs
    exact mixedRightKernel_summable hL (lt_of_lt_of_le hd hx) hs

end CenteredCircle.AllN

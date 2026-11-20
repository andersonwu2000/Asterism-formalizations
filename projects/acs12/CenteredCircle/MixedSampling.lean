import CenteredCircle.DensitySampling

/-! The mixed lattice sums are integrals of their actual signed densities. -/

namespace CenteredCircle.AllN

open MeasureTheory Set Filter

theorem samplingTail_sub_div_integral (K H f g : ℝ → ℝ) (s : ℝ)
    (hK : Summable (fun j : ℕ => K (s + j * s)))
    (hH : Summable (fun j : ℕ => H (s + j * s)))
    (hf : IntegrableOn f (Ioi 0)) (hg : IntegrableOn g (Ioi 0))
    (heK : samplingTail K 0 s = ∫ u : ℝ in Ioi 0, f u)
    (heH : samplingTail H 0 s = ∫ u : ℝ in Ioi 0, g u) :
    IntegrableOn (fun u : ℝ => f u - g u / 4) (Ioi 0) ∧
      samplingTail (fun t => K t - H t / 4) 0 s =
        ∫ u : ℝ in Ioi 0, f u - g u / 4 := by
  constructor
  · exact hf.sub (hg.div_const 4)
  · rw [samplingTail_sub_div K H s 4 hK hH, heK, heH,
      integral_sub hf (hg.div_const 4), integral_div]

theorem mixedLeftKernel_sampling {L s : ℝ} (hL : 0 < L) (hs : 0 < s) :
    IntegrableOn (fun u : ℝ => circleWeight L u * leftMixPolynomial u * scaledExpTail u s) (Ioi 0) ∧
      samplingTail (mixedLeftKernel L) 0 s =
        ∫ u : ℝ in Ioi 0, circleWeight L u * leftMixPolynomial u * scaledExpTail u s := by
  have hA := circle_density_sampling hL hs .a
  have hB := circle_density_sampling hL hs .b
  have h := samplingTail_sub_div_integral (circleKernel L .a) (circleKernel L .b)
    _ _ s (circleKernel_summable hL .a s s hs hs) (circleKernel_summable hL .b s s hs hs)
    hA.1 hB.1 hA.2 hB.2
  have he : (fun u : ℝ => circleDensity L .a u * scaledExpTail u s -
      (circleDensity L .b u * scaledExpTail u s) / 4) =
      fun u => circleWeight L u * leftMixPolynomial u * scaledExpTail u s := by
    funext u
    dsimp [circleDensity, densityPolynomial, leftMixPolynomial]
    ring
  rw [he] at h
  have hfun : mixedLeftKernel L = fun t => circleKernel L .a t - circleKernel L .b t / 4 := by
    funext t
    exact mixedLeftKernel_formula hL t
  rw [hfun]
  exact h

theorem mixedRightKernel_sampling {L s : ℝ} (hL : 0 < L) (hs : 0 < s) :
    IntegrableOn (fun u : ℝ => circleWeight L u * rightMixPolynomial u * scaledExpTail u s) (Ioi 0) ∧
      samplingTail (mixedRightKernel L) 0 s =
        ∫ u : ℝ in Ioi 0, circleWeight L u * rightMixPolynomial u * scaledExpTail u s := by
  have hA := circle_density_sampling hL hs .a
  have hB := circle_density_sampling hL hs .b
  have h := samplingTail_sub_div_integral (circleKernel L .b) (circleKernel L .a)
    _ _ s (circleKernel_summable hL .b s s hs hs) (circleKernel_summable hL .a s s hs hs)
    hB.1 hA.1 hB.2 hA.2
  have he : (fun u : ℝ => circleDensity L .b u * scaledExpTail u s -
      (circleDensity L .a u * scaledExpTail u s) / 4) =
      fun u => circleWeight L u * rightMixPolynomial u * scaledExpTail u s := by
    funext u
    dsimp [circleDensity, densityPolynomial, rightMixPolynomial]
    ring
  rw [he] at h
  have hfun : mixedRightKernel L = fun t => circleKernel L .b t - circleKernel L .a t / 4 := by
    funext t
    exact mixedRightKernel_formula hL t
  rw [hfun]
  exact h

noncomputable def lineLeftKernel (t : ℝ) : ℝ := lineKernel .a t - lineKernel .b t / 4
noncomputable def lineRightKernel (t : ℝ) : ℝ := lineKernel .b t - lineKernel .a t / 4

theorem lineLeftKernel_sampling {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun u : ℝ => leftMixPolynomial u * scaledExpTail u s) (Ioi 0) ∧
      samplingTail lineLeftKernel 0 s =
        ∫ u : ℝ in Ioi 0, leftMixPolynomial u * scaledExpTail u s := by
  have hA := line_density_sampling hs .a
  have hB := line_density_sampling hs .b
  have h := samplingTail_sub_div_integral (lineKernel .a) (lineKernel .b)
    _ _ s (lineKernel_summable .a hs hs) (lineKernel_summable .b hs hs)
    hA.1 hB.1 hA.2 hB.2
  have he : (fun u : ℝ => densityPolynomial .a u * scaledExpTail u s -
      (densityPolynomial .b u * scaledExpTail u s) / 4) =
      fun u => leftMixPolynomial u * scaledExpTail u s := by
    funext u
    dsimp [densityPolynomial, leftMixPolynomial]
    ring
  rw [he] at h
  exact h

theorem lineRightKernel_sampling {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun u : ℝ => rightMixPolynomial u * scaledExpTail u s) (Ioi 0) ∧
      samplingTail lineRightKernel 0 s =
        ∫ u : ℝ in Ioi 0, rightMixPolynomial u * scaledExpTail u s := by
  have hA := line_density_sampling hs .a
  have hB := line_density_sampling hs .b
  have h := samplingTail_sub_div_integral (lineKernel .b) (lineKernel .a)
    _ _ s (lineKernel_summable .b hs hs) (lineKernel_summable .a hs hs)
    hB.1 hA.1 hB.2 hA.2
  have he : (fun u : ℝ => densityPolynomial .b u * scaledExpTail u s -
      (densityPolynomial .a u * scaledExpTail u s) / 4) =
      fun u => rightMixPolynomial u * scaledExpTail u s := by
    funext u
    dsimp [densityPolynomial, rightMixPolynomial]
    ring
  rw [he] at h
  exact h

end CenteredCircle.AllN

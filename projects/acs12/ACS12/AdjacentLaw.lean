import ACS12.LawPeanoContinuity
import ACS12.FourthComparisonRoot
import ACS12.JointFloor

/-! The exact adjacent law used at the original fourth-source cap. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open scoped Topology

noncomputable def adjacentSourceLaw (p L θ u v m r : ℝ) : ℝ :=
  let D := lawMoment p L θ 0 u + lawSelf p L θ
  samplingTail (lawPeanoKernel p L θ u .b) 0 1 + u * D -
    m * (u * lawMoment p L θ 1 u + D) + samplingHead (lawPeanoKernel p L θ u .a) v r

theorem _root_.ACS12.Configuration.adjacentSourceLaw_nonneg {n : ℕ} {p : ℝ} (F : Configuration n p)
    (hn : 2 ≤ n) (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi)) {j k : Fin n}
    (hj : C.source.IsNext C.source.neighbor j) (hk : C.source.IsNext j k) :
    let S := C.source
    0 ≤ adjacentSourceLaw p S.period 1 (S.forwardDistance S.neighbor j) (S.forwardDistance j k)
      (S.mass j) (S.mass k) := by
  let S := C.source
  let L := S.period
  let u := S.forwardDistance S.neighbor j
  let v := S.forwardDistance j k
  let b := S.mass S.neighbor
  let m := S.mass j
  let r := S.mass k
  let A := peanoKernel p L u .a
  let B := peanoKernel p L u .b
  let D := imagePotential p L u + imageSelf p L
  have hp₀ := zero_lt_one.trans_le hp
  have hL : 0 < L := S.period_pos
  have hu : 0 < u := S.forwardDistance_pos _ _
  have hD : 0 < D := add_pos (imagePotential_pos hp₀ hL hu) (imageSelf_pos hp₀ hL)
  have hb : b ≤ u := (S.forwardDistance_caps C.circular_caps (fun he => (lt_irrefl _) (he ▸ hj.1))).1
  have h := F.adjacent_source_necessary hn hp₀ hp₂ C hj hk
  change 0 ≤ samplingTail B 0 1 + b * D - m * (u * imageSlope p L u + D) + samplingHead A v r at h
  change 0 ≤ adjacentSourceLaw p L 1 u v m r
  simp only [adjacentSourceLaw, lawPeanoKernel_one, lawMoment_one_radial, lawMoment_one_slope,
    lawSelf, one_mul]
  change 0 ≤ samplingTail B 0 1 + u * D - m * (u * imageSlope p L u + D) + samplingHead A v r
  linarith only [h, mul_le_mul_of_nonneg_right hb hD.le]

theorem adjacentSourceLaw_mono_r {p L θ u v m r q : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hu : 0 < u) (hv : 0 < v)
    (hr : 0 < r) (hq : 0 < q) (hrq : r ≤ q) :
    adjacentSourceLaw p L θ u v m r ≤ adjacentSourceLaw p L θ u v m q := by
  unfold adjacentSourceLaw
  exact add_le_add le_rfl (lawPeanoHead_mono_step hp hp₂ hL hθ hu hv hr hq hrq .a)

theorem peanoBose_total {u s : ℝ} (hu : 0 < u) (hs : 0 < s) :
    (polyA (u * s) + polyB (u * s)) * scaledExpTail s u =
      u * u * s * Real.exp (-s * u) := by
  have hPoly : polyA (u * s) + polyB (u * s) = u * s * (1 - Real.exp (-s * u)) := by
    simp only [polyA, polyB, show -(u * s) = -s * u by ring]
    ring
  rw [hPoly]
  linear_combination -(u * s) * scaledExpTail_bridge hs hu

theorem adjacentSourceLaw_at_u_neg {p L θ u r : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hu : 0 < u) (hu₁ : u < 1)
    (hr : 0 < r) (hru : r ≤ u) :
    adjacentSourceLaw p L θ u u u r < 0 := by
  refine (adjacentSourceLaw_mono_r hp hp₂ hL hθ hu hu hr hu hru).trans_lt ?_
  let A := lawPeanoKernel p L θ u .a
  let B := lawPeanoKernel p L θ u .b
  let w := lawDensity p L θ
  let f (s : ℝ) := lawPeanoDensity p L θ u .b s * scaledExpTail s 1
  let g (s : ℝ) := lawPeanoDensity p L θ u .a s * scaledExpTail s u
  let h (s : ℝ) := w s * s * Real.exp (-s * u)
  let μ := volume.restrict (Ioi (0 : ℝ))
  obtain ⟨hf, hfE⟩ := lawPeanoTail_sampling hp hp₂ hL hθ hu (t := 0) le_rfl zero_lt_one .b
  obtain ⟨hg, hgE⟩ := lawPeanoTail_sampling hp hp₂ hL hθ hu (t := 0) le_rfl hu .a
  simp only [mul_zero, Real.exp_zero, mul_one] at hf hfE hg hgE
  have hh : Integrable h μ := by simpa only [pow_one] using lawMoment_integrable hp hp₂ hL hθ hu 1
  have hf' : Integrable f μ := hf
  have hg' : Integrable g μ := hg
  have hInt : Integrable (fun s => f s + g s - (u * u) * h s) μ :=
    (hf'.add hg').sub (hh.const_mul (u * u))
  have hEq : adjacentSourceLaw p L θ u u u u =
      ∫ s : ℝ in Ioi 0, f s + g s - (u * u) * h s := by
    have hShift : samplingHead A u u = samplingTail A 0 u := by
      rw [samplingTail_eq_shift, zero_add]
    change samplingTail B 0 1 + u * (lawMoment p L θ 0 u + lawSelf p L θ) -
      u * (u * lawMoment p L θ 1 u + (lawMoment p L θ 0 u + lawSelf p L θ)) +
      samplingHead A u u = _
    have hFG : Integrable (fun s => f s + g s) μ := hf'.add hg'
    rw [hShift, integral_sub hFG (hh.const_mul (u * u)),
      integral_add hf' hg', integral_const_mul]
    change samplingTail (lawPeanoKernel p L θ u .b) 0 1 + _ -
      _ + samplingTail (lawPeanoKernel p L θ u .a) 0 u = _
    rw [hfE, hgE]
    simp only [f, g, h, μ, w, lawMoment, pow_one]
    ring
  rw [hEq]
  letI : NeZero μ := ⟨positiveHalfLine_ne_zero⟩
  have hNeg := integral_strict_of_ae_lt μ hInt (integrable_zero ℝ ℝ μ) ?_
  · simpa only [integral_zero] using hNeg
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0 < s := hs
    have hT := peanoBose_total hu hs₀
    have hPoint : f s + g s - (u * u) * h s =
        w s * polyB (u * s) * (scaledExpTail s 1 - scaledExpTail s u) := by
      simp only [f, g, h, lawPeanoDensity, densityPolynomial]
      linear_combination w s * hT
    rw [hPoint]
    exact mul_neg_of_pos_of_neg (mul_pos (lawDensity_pos (zero_lt_one.trans_le hp) hL hθ hs₀)
      (polyB_pos (mul_pos hu hs₀))) (sub_neg.mpr
        (scaledExpTail_strictAnti hs₀ hu (mem_Ioi.mpr zero_lt_one) hu₁))

theorem adjacentSourceLaw_advance_lt {p L θ u x y m r q : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hu : 0 < u) (hx : 0 < x)
    (hxy : x < y) (hr : 0 < r) (hq : 0 < q) (hqr : q - r ≤ 2 * (y - x)) :
    adjacentSourceLaw p L θ u y m q < adjacentSourceLaw p L θ u x m r := by
  let d := y - x
  have hd : 0 < d := sub_pos.mpr hxy
  have hqd : q ≤ r + 2 * d := by linarith
  have hy := hx.trans hxy
  have hR : 0 < r + 2 * d := add_pos hr (mul_pos two_pos hd)
  have hW := lawPeanoHead_advance_lt hp hp₂ hL hθ hu hx hr hd .a
  have he : x + d = y := by dsimp only [d]; ring
  rw [he] at hW
  unfold adjacentSourceLaw
  exact add_lt_add_right ((lawPeanoHead_mono_step hp hp₂ hL hθ hu hy hq hR hqd .a).trans_lt hW) _

end ACS12.GammaMeasure


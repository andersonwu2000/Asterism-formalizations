import ACS12.GammaMoments
import ACS12.LowScalar

/-! The actual source satisfies the mixed quadrature bound. -/

namespace ACS12.GammaMeasure

open MeasureTheory Set
open scoped BigOperators
open CenteredCircle.AllN (CircleKernelKind imageTail samplingTail NormalizedCircleChart
  ratioFloor ratioFloor_bounds strictMonoOn_ratioFloor integral_strict_of_ae_lt positiveHalfLine_ne_zero)

private theorem imageTail_moment_sub {p L t : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (ht : 0 < t) (k₁ k₂ : CircleKernelKind) :
    imageTail (fun x => imageMoment p L k₁ 0 x - imageMoment p L k₂ 0 x / 4) L t =
      imageTail (imageMoment p L k₁ 0) L t - imageTail (imageMoment p L k₂ 0) L t / 4 := by
  have ha := imageMoment_samples_summable hp hp₂ hL ht hL k₁
  have hb := imageMoment_samples_summable hp hp₂ hL ht hL k₂
  simp only [imageTail, ha.tsum_sub (hb.div_const 4), tsum_div_const]

private theorem weighted_imageTail_moment_sub {ι : Type*} [Fintype ι] {p L : ℝ}
    (hp : 0 < p) (hp₂ : p ≤ 2) (hL : 0 < L) (q d : ι → ℝ) (hd : ∀ i, 0 < d i)
    (k₁ k₂ : CircleKernelKind) :
    (∑ i, q i * imageTail (fun x => imageMoment p L k₁ 0 x - imageMoment p L k₂ 0 x / 4) L (d i)) =
      (∑ i, q i * imageTail (imageMoment p L k₁ 0) L (d i)) -
        (∑ i, q i * imageTail (imageMoment p L k₂ 0) L (d i)) / 4 := by
  simp_rw [imageTail_moment_sub hp hp₂ hL (hd _), mul_sub, ← mul_div_assoc, Finset.sum_sub_distrib,
    Finset.sum_div]

theorem imageTail_moment_zero_a {p L t : ℝ} (hp : 0 < p) (hL : 0 < L) (ht : 0 < t) :
    imageTail (imageMoment p L .a 0) L t = imageTail (imageA p L) L t := by
  apply tsum_congr
  intro j
  exact imageMoment_zero_a hp hL (by positivity)

theorem imageTail_moment_zero_b {p L t : ℝ} (hp : 0 < p) (hL : 0 < L) (ht : 0 < t) :
    imageTail (imageMoment p L .b 0) L t = imageTail (imageB p L) L t := by
  apply tsum_congr
  intro j
  exact imageMoment_zero_b hp hL (by positivity)

noncomputable def circleDefect (p L b : ℝ) : ℝ :=
  samplingTail (imageLeftMoment p L 0) 0 1 +
    samplingTail (imageRightMoment p L 0) 0 b -
    (1 - b / 4) * imageSlope p L 1 -
    (5 / 4) * (1 - b) * (imagePotential p L 1 + imageSelf p L)

/-- The mixed quadrature comparison uses both exterior rays of the original
force source at its attained normalization. -/
theorem _root_.ACS12.Configuration.circleDefect_nonneg {n : ℕ} {p : ℝ}
    (F : Configuration n p) (hp : 0 < p) (hp₂ : p ≤ 2)
    (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi)) :
    0 ≤ circleDefect p C.source.period (C.source.mass C.source.neighbor) := by
  let S := C.source
  let L := S.period
  let b := S.mass S.neighbor
  have hL : 0 < L := S.period_pos
  have hb : 0 < b := S.mass_pos _
  have hleft := S.leftExterior_quadrature (imageLeft_quadratureData hp hp₂ hL) C.circular_caps
  have hright := S.rightExterior_quadrature (imageRight_quadratureData hp hp₂ hL hb) C.circular_caps
  have hLmix : S.leftExterior (imageLeftMoment p L 0) =
      S.leftExterior (imageA p L) - S.leftExterior (imageB p L) / 4 := by
    have h := weighted_imageTail_moment_sub hp hp₂ hL S.mass S.leftDistance S.leftDistance_pos .a .b
    simp_rw [imageTail_moment_zero_a hp hL (S.leftDistance_pos _),
      imageTail_moment_zero_b hp hL (S.leftDistance_pos _)] at h
    exact h
  have hRmix : S.rightExterior (imageRightMoment p L 0) =
      S.rightExterior (imageB p L) - S.rightExterior (imageA p L) / 4 := by
    have h := weighted_imageTail_moment_sub hp hp₂ hL S.mass S.rightDistance S.rightDistance_pos .b .a
    simp_rw [imageTail_moment_zero_a hp hL (S.rightDistance_pos _),
      imageTail_moment_zero_b hp hL (S.rightDistance_pos _)] at h
    exact h
  rw [hLmix] at hleft
  rw [hRmix] at hright
  obtain ⟨hA, hB⟩ := F.anchored_image_balances hp C
  change 0 ≤ circleDefect p L b
  unfold circleDefect
  linarith

private theorem imageTail_moment_pos {p L t : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2) (hL : 0 < L)
    (ht : 0 < t) (kind : CircleKernelKind) : 0 < imageTail (imageMoment p L kind 0) L t := by
  have hs := imageMoment_samples_summable hp hp₂ hL ht hL kind
  apply hs.tsum_pos (fun j => (imageMoment_pos hp hp₂ hL (by positivity) kind 0).le) 0
  simpa only [Nat.cast_zero, zero_mul, add_zero] using imageMoment_pos hp hp₂ hL ht kind 0

private theorem imageTail_moment_a_lt_b {p L t : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2) (hL : 0 < L)
    (ht : 0 < t) :
    imageTail (imageMoment p L .a 0) L t < imageTail (imageMoment p L .b 0) L t := by
  apply (imageMoment_samples_summable hp hp₂ hL ht hL .a).tsum_lt_tsum
    (fun j => (imageMoment_a_lt_b hp hp₂ hL (by positivity) 0).le) (i := 0)
    (by simpa only [Nat.cast_zero, zero_mul, add_zero] using imageMoment_a_lt_b hp hp₂ hL ht 0)
    (imageMoment_samples_summable hp hp₂ hL ht hL .b)

private theorem imageTail_moment_ratio {p L t b : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hb : 0 < b) (hbt : b ≤ t) :
    ratioFloor b * imageTail (imageMoment p L .b 0) L t ≤
      imageTail (imageMoment p L .a 0) L t := by
  have ht := hb.trans_le hbt
  have hB := imageMoment_samples_summable hp hp₂ hL ht hL .b
  have hA := imageMoment_samples_summable hp hp₂ hL ht hL .a
  rw [imageTail, imageTail, ← tsum_mul_left]
  apply (hB.mul_left (ratioFloor b)).tsum_le_tsum _ hA
  intro j
  have hj : b ≤ t + (j : ℝ) * L := hbt.trans (le_add_of_nonneg_right (by positivity))
  have hj₀ := hb.trans_le hj
  exact (mul_le_mul_of_nonneg_right (strictMonoOn_ratioFloor.monotoneOn hb hj₀ hj)
      (imageMoment_pos hp hp₂ hL hj₀ .b 0).le).trans
    (imageMoment_ratio_lower hp hp₂ hL hj₀)

private theorem massPolynomial_pos_of_row {p b U D : ℝ} (hb : 0 < b) (hb₁ : b ≤ 1)
    (hU : 0 < U) (hD : 0 < D) (hUD : U ≤ p * D)
    (hrow : ratioFloor b * (U + (1 - b) * D) < b * U - (1 - b) * D) :
    0 < LowScalar.massPolynomial p b := by
  have hc := ratioFloor_bounds hb
  have hcost : 0 ≤ (1 - b) * (1 + ratioFloor b) :=
    mul_nonneg (sub_nonneg.mpr hb₁) (by linarith [hc.1])
  have hd : 0 < b - ratioFloor b := by
    by_contra! h
    nlinarith [mul_nonpos_of_nonpos_of_nonneg h hU.le, mul_nonneg hcost hD.le]
  have hineq : (1 - b) * (1 + ratioFloor b) < p * (b - ratioFloor b) := by
    refine lt_of_mul_lt_mul_right ?_ hD.le
    nlinarith [mul_le_mul_of_nonneg_left hUD hd.le]
  have hden : 0 < (b + 1) * (3 * b + 2) := by positivity
  have hpoly := mul_lt_mul_of_pos_right hineq hden
  unfold ratioFloor at hpoly
  field_simp [hden.ne'] at hpoly
  unfold LowScalar.massPolynomial
  nlinarith

theorem _root_.ACS12.Configuration.anchored_massPolynomial_pos {n : ℕ} {p : ℝ}
    (F : Configuration n p) (hp : 0 < p) (hp₂ : p ≤ 2)
    (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi))
    (hUD : imageSlope p C.source.period 1 ≤
      p * (imagePotential p C.source.period 1 + imageSelf p C.source.period)) :
    0 < LowScalar.massPolynomial p (C.source.mass C.source.neighbor) := by
  let S := C.source
  let L := S.period
  let b := S.mass S.neighbor
  have hL : 0 < L := S.period_pos
  have hb : 0 < b := S.mass_pos _
  have hb₁ : b ≤ 1 := S.mass_neighbor_le_one
  have hC := ratioFloor_bounds hb
  have hLA : ratioFloor b * S.leftExterior (imageA p L) < S.leftExterior (imageB p L) := by
    unfold CenteredCircle.AllN.AnchoredCircleSource.leftExterior
    rw [Finset.mul_sum]
    have hstrict (i : Fin n) : ratioFloor b * imageTail (imageA p L) L (S.leftDistance i) <
        imageTail (imageB p L) L (S.leftDistance i) := by
      have h := imageTail_moment_a_lt_b hp hp₂ hL (S.leftDistance_pos i)
      rw [imageTail_moment_zero_a hp hL (S.leftDistance_pos i),
        imageTail_moment_zero_b hp hL (S.leftDistance_pos i)] at h
      have hpos := imageTail_moment_pos hp hp₂ hL (S.leftDistance_pos i) .a
      rw [imageTail_moment_zero_a hp hL (S.leftDistance_pos i)] at hpos
      exact (mul_le_of_le_one_left hpos.le hC.2.le).trans_lt h
    apply Finset.sum_lt_sum
    · intro i _
      rw [mul_left_comm]
      exact mul_le_mul_of_nonneg_left (hstrict i).le (S.mass_pos i).le
    · refine ⟨S.root, Finset.mem_univ _, ?_⟩
      rw [mul_left_comm]
      exact mul_lt_mul_of_pos_left (hstrict S.root) (S.mass_pos S.root)
  have hRA : ratioFloor b * S.rightExterior (imageB p L) ≤ S.rightExterior (imageA p L) := by
    unfold CenteredCircle.AllN.AnchoredCircleSource.rightExterior
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have h := imageTail_moment_ratio hp hp₂ hL hb (S.rightDistance_ge_neighbor C.circular_caps i)
    rw [imageTail_moment_zero_a hp hL (S.rightDistance_pos i),
      imageTail_moment_zero_b hp hL (S.rightDistance_pos i)] at h
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left h (S.mass_pos i).le
  have hU : 0 < imageSlope p L 1 := by
    letI : NeZero (volume.restrict (Ioi (0 : ℝ))) := ⟨positiveHalfLine_ne_zero⟩
    have h := integral_strict_of_ae_lt (volume.restrict (Ioi (0 : ℝ))) (integrable_zero ℝ ℝ _)
      (imageSlope_integrable hp hL (by norm_num : 0 < (1 : ℝ))) ?_
    · simpa only [imageSlope, integral_zero] using h
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact mul_pos (mul_pos (imageDensity_pos hp hL hs) hs) (Real.exp_pos _)
  have hD : 0 < imagePotential p L 1 + imageSelf p L :=
    add_pos (imagePotential_pos hp hL (by norm_num)) (imageSelf_pos hp hL)
  apply massPolynomial_pos_of_row hb hb₁ hU hD hUD
  have h := add_lt_add_of_lt_of_le hLA hRA
  rw [← mul_add] at h
  obtain ⟨h₁, h₂⟩ := F.anchored_image_balances hp C
  change _ * (S.leftExterior (imageA p L) + S.rightExterior (imageB p L)) <
    S.leftExterior (imageB p L) + S.rightExterior (imageA p L) at h
  rw [h₁, h₂] at h
  exact h

end ACS12.GammaMeasure

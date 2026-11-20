import CenteredCircle.KernelMoments

/-!
Signs of the first three moments of A - B/4 on t >= 1. These imply the
required shape of the left mixed kernel, without asserting a positive density.
-/

namespace CenteredCircle.AllN

open MeasureTheory Set

theorem polynomial_mixed_moment_pos (m : ℕ) (hm : m ≤ 2) {t : ℝ} (ht : 1 ≤ t) :
    0 < (∫ u : ℝ in Ioi 0, (u ^ (m + 1) * polyA u) * Real.exp (-u * t)) -
      (∫ u : ℝ in Ioi 0, (u ^ (m + 1) * polyB u) * Real.exp (-u * t)) / 4 := by
  have htp : 0 < t := by linarith
  have ht1 : 0 < t + 1 := by linarith
  have hy : 0 ≤ t - 1 := sub_nonneg.mpr ht
  rw [integral_polyA_moment (m + 1) htp, integral_polyB_moment (m + 1) htp]
  interval_cases m
  · norm_num only [Nat.factorial, Nat.cast_one, Nat.cast_ofNat, Nat.reduceAdd, Nat.cast_mul, mul_one]
    have he : 1 / t ^ 2 - 1 / (t + 1) ^ 2 - 2 / (t + 1) ^ 3 -
        (2 / t ^ 3 - 1 / t ^ 2 + 1 / (t + 1) ^ 2) / 4 =
        (9 * (t - 1) ^ 2 + 17 * (t - 1) + 6) / (4 * t ^ 3 * (t + 1) ^ 3) := by
      field_simp
      <;> ring
    rw [he]
    positivity
  · norm_num only [Nat.factorial, Nat.cast_one, Nat.cast_ofNat, Nat.reduceAdd, Nat.cast_mul, mul_one]
    have he : 2 / t ^ 3 - 2 / (t + 1) ^ 3 - 6 / (t + 1) ^ 4 -
        (6 / t ^ 4 - 2 / t ^ 3 + 2 / (t + 1) ^ 3) / 4 =
        (18 * (t - 1) ^ 3 + 56 * (t - 1) ^ 2 + 51 * (t - 1) + 10) /
          (2 * t ^ 4 * (t + 1) ^ 4) := by
      field_simp
      <;> ring
    rw [he]
    positivity
  · norm_num only [Nat.factorial, Nat.cast_one, Nat.cast_ofNat, Nat.reduceAdd, Nat.cast_mul, mul_one]
    have he : 6 / t ^ 4 - 6 / (t + 1) ^ 4 - 24 / (t + 1) ^ 5 -
        (24 / t ^ 5 - 6 / t ^ 4 + 6 / (t + 1) ^ 4) / 4 =
        (90 * (t - 1) ^ 4 + 390 * (t - 1) ^ 3 + 585 * (t - 1) ^ 2 +
          315 * (t - 1) + 18) / (2 * t ^ 5 * (t + 1) ^ 5) := by
      field_simp
      <;> ring
    rw [he]
    positivity

noncomputable def leftMixedMoment (L : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  kernelMoment L .a m t - kernelMoment L .b m t / 4

noncomputable def rightMixedMoment (L : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  kernelMoment L .b m t - kernelMoment L .a m t / 4

theorem leftMixedMoment_pos {L t : ℝ} (hL : 0 < L) (ht : 1 ≤ t)
    (m : ℕ) (hm : m ≤ 2) : 0 < leftMixedMoment L m t := by
  have htp : 0 < t := by linarith
  have hcmp := kernelMoment_comparison hL htp m
  have hline := polynomial_mixed_moment_pos m hm ht
  have hB := kernelMoment_pos hL htp .b m
  have hp := mul_pos hline hB
  have hb0 : 0 < ∫ u : ℝ in Ioi 0, (u ^ (m + 1) * polyB u) * Real.exp (-u * t) :=
    densityPolynomial_moment_pos .b (m + 1) htp
  apply (mul_pos_iff_of_pos_right hb0).mp
  dsimp [leftMixedMoment]
  nlinarith

theorem rightMixedMoment_pos {L t : ℝ} (hL : 0 < L) (ht : 0 < t) (m : ℕ) :
    0 < rightMixedMoment L m t := by
  have hlt := kernelMoment_a_lt_b hL ht m
  have hpos := kernelMoment_pos hL ht .a m
  dsimp [rightMixedMoment]
  linarith

theorem hasDerivAt_leftMixedMoment {L t : ℝ} (hL : 0 < L) (ht : 0 < t) (m : ℕ) :
    HasDerivAt (leftMixedMoment L m) (-leftMixedMoment L (m + 1) t) t := by
  convert (hasDerivAt_kernelMoment hL ht .a m).sub
    ((hasDerivAt_kernelMoment hL ht .b m).div_const 4) using 1 <;>
    dsimp [leftMixedMoment] <;> ring

theorem hasDerivAt_rightMixedMoment {L t : ℝ} (hL : 0 < L) (ht : 0 < t) (m : ℕ) :
    HasDerivAt (rightMixedMoment L m) (-rightMixedMoment L (m + 1) t) t := by
  convert (hasDerivAt_kernelMoment hL ht .b m).sub
    ((hasDerivAt_kernelMoment hL ht .a m).div_const 4) using 1 <;>
    dsimp [rightMixedMoment] <;> ring

end CenteredCircle.AllN

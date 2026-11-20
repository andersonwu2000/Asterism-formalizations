import ACS12.PeanoExponentIntegral
import ACS12.UnimodalSampling

/-! Complete mesh prices for the two Peano exponent curvatures. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set
open scoped BigOperators

private theorem peanoBad_samples_summable {p a x : ℝ} (hp : 1 ≤ p) (ha : 0 < a) (hx : 0 < x) :
    Summable (fun j : ℕ => peanoExponentBad p (x + j * a)) := by
  let B := 2 * (2 * p + 1)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  apply summable_of_power_decay _ B x a 2 (by decide) hB hx ha (fun t ht => peanoExponentBad_nonneg ht)
  intro t ht
  rcases le_or_gt t 1 with h | h
  · have hL := Real.log_nonpos ht.le h
    have hQ : peanoExponentQuadratic p (Real.log t) ≤ 0 := by
      change B * Real.log t - p * (p + 1) * Real.log t ^ 2 - 2 ≤ 0
      have h' := mul_nonpos_of_nonneg_of_nonpos hB hL
      have h'' : 0 ≤ p * (p + 1) * Real.log t ^ 2 := by positivity
      linarith only [h', h'']
    rw [peanoExponentBad, max_eq_left hQ, mul_zero]
    exact div_nonneg hB (sq_nonneg _)
  · have hQ : max 0 (peanoExponentQuadratic p (Real.log t)) ≤ B * t := by
      apply max_le (mul_nonneg hB ht.le)
      have hL := Real.log_le_sub_one_of_pos ht
      have h' := mul_le_mul_of_nonneg_left (show Real.log t ≤ t by linarith only [hL]) hB
      have h'' : 0 ≤ p * (p + 1) * Real.log t ^ 2 := by positivity
      change B * Real.log t - p * (p + 1) * Real.log t ^ 2 - 2 ≤ B * t
      linarith only [h', h'']
    have hStep : t ^ (-(p + 2)) * t = t ^ (-(p + 1)) := by
      rw [show -(p + 2) = -(p + 1) - 1 by ring,
        Real.rpow_sub_one ht.ne', div_mul_cancel₀ _ ht.ne']
    unfold peanoExponentBad
    calc
      _ ≤ t ^ (-(p + 2)) * (B * t) := mul_le_mul_of_nonneg_left hQ (Real.rpow_nonneg ht.le _)
      _ = B * t ^ (-(p + 1)) := by rw [← hStep]; ring
      _ ≤ B / t ^ 2 := by
        rw [div_eq_mul_inv, ← Real.rpow_two, ← Real.rpow_neg ht.le]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h.le (by linarith)) hB

private theorem peanoBad_mesh_le {p a t M : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) (ha : 0 < a)
    (ht : 0 ≤ t) (hPeak : ∀ s ≥ a + t, peanoExponentBad p s ≤ M) (N : ℕ) :
    a * (∑ j ∈ Finset.range N, peanoExponentBad p (a + t + j * a)) ≤ 8 / 25 + a * M := by
  have hx := add_pos_of_pos_of_nonneg ha ht
  obtain ⟨hI, hInt⟩ := peanoExponentBad_integral hp hP
  have hSum := peanoBad_samples_summable hp ha hx
  have hF := mul_le_mul_of_nonneg_left (hSum.sum_le_tsum (Finset.range N) (fun j _ =>
    peanoExponentBad_nonneg (add_pos_of_pos_of_nonneg hx (mul_nonneg (Nat.cast_nonneg j) ha.le)))) ha.le
  have hL := samplingHead_le_integral_add_peak_from hx ha (peanoExponentBad_continuousOn p)
    hI (fun _ hs => peanoExponentBad_nonneg hs) hPeak
    (fun ha hab hbc => peanoExponentBad_min (zero_lt_one.trans_le hp).le ha hab hbc) hSum
  exact hF.trans (hL.trans (add_le_add_left hInt.le _))

theorem peanoBad_small_mesh {p a t : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) (ha : 0 < a)
    (ha₁ : a ≤ 1) (ht : 0 ≤ t) (N : ℕ) :
    a * (∑ j ∈ Finset.range N, peanoExponentBad p (a + t + j * a)) ≤ 17 / 25 := by
  have h := peanoBad_mesh_le hp hP ha ht (fun s hs =>
    peanoExponentBad_le hp hP ((add_pos_of_pos_of_nonneg ha ht).trans_le hs)) N
  have h' := mul_le_of_le_one_left (by norm_num : (0 : ℝ) ≤ 9 / 25) ha₁
  linarith only [h, h']

theorem peanoBad_large_mesh {p a t : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) (ha : 0 < a)
    (ht : 0 ≤ t) (N : ℕ) :
    a * (∑ j ∈ Finset.range N, peanoExponentBad p (a + t + j * a)) ≤ 47 / 50 := by
  have hPeak (s : ℝ) (hs : a + t ≤ s) : peanoExponentBad p s ≤ (31 / 50) / a := by
    have hs₀ := (add_pos_of_pos_of_nonneg ha ht).trans_le hs
    have hA : a ≤ s := (le_add_of_nonneg_right ht).trans hs
    apply (le_div_iff₀ ha).mpr
    rw [mul_comm (peanoExponentBad p s) a]
    exact (mul_le_mul_of_nonneg_right hA (peanoExponentBad_nonneg hs₀)).trans
      (mul_peanoExponentBad_le hp hP hs₀)
  have h := peanoBad_mesh_le hp hP ha ht hPeak N
  have hE : a * ((31 / 50) / a) = 31 / 50 := by field_simp [ha.ne']
  rw [hE] at h
  linarith only [h]

end ACS12.GammaMeasure

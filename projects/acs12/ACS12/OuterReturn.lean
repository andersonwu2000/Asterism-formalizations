import ACS12.OuterNative
import ACS12.MiddleComparison

/-! The outer actual-to-pure comparison with one literal self term and every clipped atom. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaDeficit (signedDensity)

noncomputable def outerLawValue (p L θ u : ℝ) : ℝ :=
  outerLawSignedValue p L θ u (outerLawMass p L θ u) +
    samplingTail (lawRightNegative p L θ u) u u

theorem clipped_tail_eq {p L θ u t q : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (ht : 0 ≤ t) (hq : 0 < q) :
    samplingTail (fun x => max 0 (lawRightTest p L θ u x)) t q =
      samplingTail (lawRightTest p L θ u) t q + samplingTail (lawRightNegative p L θ u) t q := by
  let f (j : ℕ) := lawRightTest p L θ u (t + ((j + 1 : ℕ) : ℝ) * q)
  let g (j : ℕ) := lawRightNegative p L θ u (t + ((j + 1 : ℕ) : ℝ) * q)
  have hA : Summable (fun j => |f j|) := lawRight_abs_samples_summable hp hp₂ hL hθ ht hq
  have hf : Summable f := Summable.of_norm (by simpa only [Real.norm_eq_abs] using hA)
  have hg : Summable g := hA.of_nonneg_of_le (fun j => le_max_left _ _)
    (fun j => max_le (abs_nonneg _) (neg_le_abs _))
  have hP (j : ℕ) : max 0 (f j) = f j + g j := by
    change max 0 (f j) = f j + max 0 (-f j)
    by_cases h : 0 ≤ f j
    · rw [max_eq_right h, max_eq_left (neg_nonpos.mpr h), add_zero]
    · have h' := le_of_not_ge h
      rw [max_eq_left h', max_eq_right (neg_nonneg.mpr h'), add_neg_cancel]
  unfold samplingTail
  change q * (∑' j : ℕ, max 0 (f j)) = q * (∑' j : ℕ, f j) + q * (∑' j : ℕ, g j)
  simp_rw [hP]
  rw [hf.tsum_add hg, mul_add]

theorem outerLawValue_clipped {p L θ u : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hu : 0 < u) :
    outerLawValue p L θ u =
      middleLawBase p L θ u + outerLawMass p L θ u * lawRightTest p L θ u u +
        samplingTail (fun x => max 0 (lawRightTest p L θ u x)) u u := by
  rw [clipped_tail_eq hp hp₂ hL hθ hu.le hu, outerLawValue, outerLawSignedValue]
  ring

theorem outerLawValue_one {p L u : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hL : 0 < L) (hu : 0 < u) :
    outerLawValue p L 1 u = middleBase p L u +
      outerMass p L u * rightTest p L (middleA u) (middleZ u) u +
      samplingTail (rightClip p L (middleA u) (middleZ u)) u u := by
  have h1 : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  have hp₀ := zero_lt_one.trans_le hp
  have hZ : lawUnitSlope p L 1 = unitSlopeTotal p L := by
    have hEq : lawMoment p L 1 1 = imageSlope p L := funext (lawMoment_one_slope p L)
    rw [lawUnitSlope, unitSlopeTotal, hEq]
  have hB : middleLawBase p L 1 u = middleBase p L u := by
    simp only [middleLawBase, middleBase, lawMoment_one_radial, lawMoment_one_slope, hZ, lawSelf, one_mul]
  rw [outerLawValue_clipped hp hp₂ hL h1 hu, outerLawMass_one, lawRightTest_one hp₀ hL hu, hB]
  congr 1
  unfold samplingTail
  apply congrArg (u * ·)
  apply tsum_congr
  intro j
  change max 0 (lawRightTest p L 1 u _) = max 0 (rightTest p L (middleA u) (middleZ u) _)
  rw [lawRightTest_one hp₀ hL (by positivity)]

end ACS12.GammaMeasure


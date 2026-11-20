import ACS12.MiddleSource
import ACS12.PeanoSampling
import Mathlib.Topology.Order.IntermediateValue

/-! The original outer geometry yields the affine comparison mass. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter

noncomputable def outerMass (p L u : ℝ) : ℝ :=
  u - (samplingTail (peanoKernel p L u .b) 0 u -
    samplingTail (peanoKernel p L u .b) 0 1) /
    (u * imageSlope p L u + imagePotential p L u + imageSelf p L)

private theorem outerDenominator_pos {p L u : ℝ} (hp : 0 < p) (hL : 0 < L) (hu : 0 < u) :
    0 < u * imageSlope p L u + imagePotential p L u + imageSelf p L := by
  have hU : 0 ≤ imageSlope p L u := by
    unfold imageSlope
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0 < s := hs
    exact mul_nonneg (mul_nonneg (imageDensity_pos hp hL hs₀).le hs₀.le) (Real.exp_pos _).le
  exact add_pos (add_pos_of_nonneg_of_pos (mul_nonneg hu.le hU)
    (imagePotential_pos hp hL hu)) (imageSelf_pos hp hL)

theorem outerMass_lt_u {p L u : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hu : 0 < u) (hu₁ : u < 1) : outerMass p L u < u := by
  have hB := peanoTail_strictAnti hp hp₂ hL hu .b hu (mem_Ioi.mpr zero_lt_one) hu₁
  unfold outerMass
  exact sub_lt_self _ (div_pos (sub_pos.mpr hB) (outerDenominator_pos hp hL hu))

private theorem affine_source_eq {p L u : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hu : 0 < u) (m : ℝ) :
    samplingTail (peanoKernel p L u .b) 0 1 + u * (imagePotential p L u + imageSelf p L) -
      m * (u * imageSlope p L u + (imagePotential p L u + imageSelf p L)) +
      samplingTail (peanoKernel p L u .a) 0 u =
      (outerMass p L u - m) * (u * imageSlope p L u + imagePotential p L u + imageSelf p L) := by
  have ht := peanoTail_total hp hp₂ hL hu
  unfold outerMass
  let D := u * imageSlope p L u + imagePotential p L u + imageSelf p L
  have hD : 0 < D := outerDenominator_pos hp hL hu
  change _ = (u - (samplingTail (peanoKernel p L u .b) 0 u -
    samplingTail (peanoKernel p L u .b) 0 1) / D - m) * D
  rw [sub_mul, sub_mul, div_mul_cancel₀ _ hD.ne']
  dsimp [D]
  nlinarith only [ht]

/-- G5 from the original outer geometry, with the literal finite self term. -/
theorem _root_.ACS12.Configuration.mass_le_outerMass {n : ℕ} {p : ℝ}
    (F : Configuration n p) (hn : 2 ≤ n) (hp : 0 < p) (hp₂ : p ≤ 2)
    (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi)) {j k : Fin n}
    (hj : C.source.IsNext C.source.neighbor j) (hk : C.source.IsNext j k)
    (hOuter : C.source.forwardDistance C.source.neighbor j ≤ C.source.forwardDistance j k) :
    C.source.mass j ≤ outerMass p C.source.period (C.source.forwardDistance C.source.neighbor j) := by
  let S := C.source
  let L := S.period
  let u := S.forwardDistance S.neighbor j
  let m := S.mass j
  let D := imagePotential p L u + imageSelf p L
  have hL : 0 < L := S.period_pos
  have hu : 0 < u := S.forwardDistance_pos _ _
  have hjN : S.neighbor ≠ j := fun he => (lt_irrefl _) (he ▸ hj.1)
  have hjK : j ≠ k := fun he => (lt_irrefl _) (he ▸ hk.1)
  have hb := (S.forwardDistance_caps C.circular_caps hjN).1
  have hD : 0 < D := add_pos (imagePotential_pos hp hL hu) (imageSelf_pos hp hL)
  have hr := F.adjacent_source_necessary hn hp hp₂ C hj hk
  dsimp only at hr
  have hRight := peanoHead_le_tail hp hp₂ hL hu hu (S.mass_pos k) hOuter
    (S.forwardDistance_caps C.circular_caps hjK).2 .a
  have h :
      0 ≤ samplingTail (peanoKernel p L u .b) 0 1 + u * D -
        m * (u * imageSlope p L u + D) + samplingTail (peanoKernel p L u .a) 0 u := by
    linarith [mul_le_mul_of_nonneg_right hb hD.le]
  rw [affine_source_eq hp hp₂ hL hu] at h
  apply sub_nonneg.mp
  by_contra! hneg
  exact (not_lt_of_ge h) (mul_neg_of_neg_of_pos hneg (outerDenominator_pos hp hL hu))

end ACS12.GammaMeasure

import ACS12.PressureMinimumTest

/-! Transfer the complete fixed-neighbor mean under the original Gamma law. -/
namespace ACS12.Pressure

open Set Filter MeasureTheory CenteredCircle.AllN
open GammaMeasure (imageDensity_pos continuous_imageDensity imageDensity_div_antitone
  imagePotential imagePotential_integrable imageSlope_integrable)

theorem minimumAtomTest_bounds {a r g s : ℝ} (ha : 0 ≤ a) (hr : 0 < r) (hg : r ≤ g) (hs : 0 < s) :
    0 ≤ minimumAtomTest a r g s ∧ minimumAtomTest a r g s ≤ a * s + 1 := by
  have hB := (pressureBose_pos hr hs).le
  have hE := Real.exp_pos (-(g - r) * s)
  have hExp : Real.exp (-(g - r) * s) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sub_nonneg.mpr hg)) hs.le)
  have hTail : s * pressureBose r s ≤ 1 := by
    rw [pressureBose_eq hr hs,scaledExpTail,← mul_div_assoc,← expTailFactor]
    exact (BoseShape.expTail_bounds (mul_pos hs hr)).2
  refine ⟨mul_nonneg hs.le (add_nonneg ha (mul_nonneg hE.le hB)),?_⟩
  have h := (mul_le_of_le_one_left (mul_nonneg hs.le hB) hExp).trans hTail
  unfold minimumAtomTest oppositeRayBose
  linarith only [h]

end ACS12.Pressure

import ACS12.MiddleComparison
import ACS12.JointFourthBracket
import ACS12.JointPureSource

/-! The fourth-root strip and the feasible lower boundary at each image weight. -/
namespace ACS12.GammaMeasure

open MeasureTheory Set Filter
open GammaDeficit (signedDensity)

noncomputable def diagonalAdjacent (p L θ u m : ℝ) : ℝ :=
  adjacentSourceLaw p L θ u m m (fourthComparisonRoot p L θ u m m)

theorem fourthComparisonRoot_mono_law {p L θ₁ θ₂ u m : ℝ} (hp : 1 ≤ p) (hp₂ : p < 2)
    (hL : 0 < L) (hθ₁ : θ₁ ∈ Icc (0 : ℝ) 1) (hθ₂ : θ₂ ∈ Icc (0 : ℝ) 1) (hθ : θ₁ ≤ θ₂)
    (hm : 0 < m) (hmu : m ≤ u) (hu₁ : u < 1) :
    fourthComparisonRoot p L θ₁ u m m ≤ fourthComparisonRoot p L θ₂ u m m := by
  let r := fourthComparisonRoot p L θ₁ u m m
  have hu := hm.trans_le hmu
  obtain ⟨⟨hr, hrm⟩, hR, _⟩ := fourthComparisonRoot_spec hp hp₂ hL hθ₁ hm hmu hu₁ hm.le le_rfl
  obtain ⟨_, _, hCap⟩ := fourthComparisonRoot_spec hp hp₂ hL hθ₂ hm hmu hu₁ hm.le le_rfl
  obtain ⟨hI, hE⟩ := fourthSource_law_difference hp hp₂ hL hθ₁ hθ₂ hu hm hr
  have hPos : 0 ≤ ∫ s : ℝ in Ioi 0, signedDensity p L s * fourthSourceResponse u m r s := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (mul_pos (signedDensity_pos hp hp₂ hL hs) (fourthSourceResponse_pos hm hmu hu₁ hr hrm.le hs)).le
  change fourthSourceRow p L θ₁ u m r m = 0 at hR
  rw [hR, sub_zero] at hE
  exact hCap r hr (hE.symm ▸ mul_nonneg (sub_nonneg.mpr hθ) hPos)

theorem diagonalAdjacent_mono_law {p L θ₁ θ₂ u m : ℝ} (hp : 1 ≤ p) (hp₂ : p < 2)
    (hL : 0 < L) (hθ₁ : θ₁ ∈ Icc (0 : ℝ) 1) (hθ₂ : θ₂ ∈ Icc (0 : ℝ) 1) (hθ : θ₁ ≤ θ₂)
    (hm : 0 < m) (hmu : m ≤ u) (hu₁ : u < 1) :
    diagonalAdjacent p L θ₁ u m ≤ diagonalAdjacent p L θ₂ u m := by
  let r := fourthComparisonRoot p L θ₁ u m m
  let q := fourthComparisonRoot p L θ₂ u m m
  have hu := hm.trans_le hmu
  have ⟨hr, hrm⟩ := (fourthComparisonRoot_spec hp hp₂ hL hθ₁ hm hmu hu₁ hm.le le_rfl).1
  have hq := (fourthComparisonRoot_spec hp hp₂ hL hθ₂ hm hmu hu₁ hm.le le_rfl).1.1
  have hMove := fourthComparisonRoot_mono_law hp hp₂ hL hθ₁ hθ₂ hθ hm hmu hu₁
  obtain ⟨hI, hE⟩ := jointAdjacent_law_difference hp hp₂ hL hθ₁ hθ₂ hu hm hr
  have hPos : 0 ≤ ∫ s : ℝ in Ioi 0, signedDensity p L s * jointSourceResponse u m r s := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (mul_pos (signedDensity_pos hp hp₂ hL hs) (jointSourceResponse_pos hm hmu hu₁ hr hrm.le hs)).le
  have hFixed := sub_nonneg.mp (hE.symm ▸ mul_nonneg (sub_nonneg.mpr hθ) hPos)
  exact hFixed.trans (adjacentSourceLaw_mono_r hp hp₂.le hL hθ₂ hu hm hr hq hMove)

theorem diagonalAdjacent_lowMass_pos {p L θ u : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (huL : 7 / 8 ≤ u) (hu₁ : u < 1) :
    0 < diagonalAdjacent p L θ u (2 * u - 1) := by
  let x := 2 * u - 1
  let r := fourthComparisonRoot p L 0 u x x
  have hp₂ : p < 2 := hP.trans_lt (by norm_num)
  have h0 : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have hx : 0 < x := by dsimp only [x]; linarith only [huL]
  have hxu : x ≤ u := by dsimp only [x]; linarith only [hu₁]
  have ⟨hr, hrx⟩ := (fourthComparisonRoot_spec hp hp₂ hL h0 hx hxu hu₁ hx.le le_rfl).1
  have hR := fourthComparisonRoot_high_bracket hp hP hL h0 hx hxu hu₁ le_rfl
  have hTest : 0 < diagonalAdjacent p L 0 u x := pureJoint_at_lowMass_pos hp hP hL huL hu₁ hr hrx.le hR
  exact hTest.trans_le (diagonalAdjacent_mono_law hp hp₂ hL h0 hθ hθ.1 hx hxu hu₁)

end ACS12.GammaMeasure

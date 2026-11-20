import ACS12.PureNativeOneValue
import ACS12.PureAdjacentExponentTail

/-! Complete p = 1 endpoints for the majorizing value with the frozen following tail. -/

namespace ACS12.GammaMeasure

open Set
open scoped BigOperators

noncomputable def commonAdjacentUpperValue (u p : ℝ) : ℝ :=
  pureNativeBand u p - pureZ p + upperFollowingValue u / u + (13 / 1875) * (9 / 5 - p)

theorem commonAdjacentUpperValue_one_middle_lt {u : ℝ} (hu : 1 / 2 ≤ u) (hu' : u ≤ 3 / 4)
    (hTail : upperFollowingValue u / u < 7 / 80) :
    commonAdjacentUpperValue u 1 < -(1 / 100) := by
  have hu₀ := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hu
  have hU : u ≤ 7 / 8 := hu'.trans (by norm_num)
  have hNative := pureNativeBand_one_mono (show u ∈ Icc (1 / 2 : ℝ) (7 / 8) from ⟨hu, hU⟩)
    (show (3 / 4 : ℝ) ∈ Icc (1 / 2) (7 / 8) by constructor <;> norm_num) hu'
  unfold commonAdjacentUpperValue
  have hE : pureNativeBand (3 / 4) 1 ≤ 1467 / 1000 := by
    unfold pureNativeBand
    rw [pureRight_one_at_u (by norm_num : (0 : ℝ) < 3 / 4)]
    norm_num [adjacentRatio, middleA]
  linarith only [hNative.trans hE, hTail, pureZ_one_gt]

theorem commonAdjacentUpperValue_one_high_lt {u : ℝ} (hu : 3 / 4 ≤ u) (hu' : u ≤ 7 / 8)
    (hTail : upperFollowingValue u / u < 7 / 80) :
    commonAdjacentUpperValue u 1 < -(1 / 100) := by
  have hL : 1 / 2 ≤ u := (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4).trans hu
  have hU : (7 / 8 : ℝ) ∈ Icc (1 / 2) (7 / 8) := by constructor <;> norm_num
  have hNative := pureNativeBand_one_mono ⟨hL, hu'⟩ hU hu'
  unfold commonAdjacentUpperValue
  have hE : pureNativeBand (7 / 8) 1 ≤ 154 / 100 := by
    unfold pureNativeBand
    rw [pureRight_one_at_u (by norm_num : (0 : ℝ) < 7 / 8)]
    norm_num [adjacentRatio, middleA]
  linarith only [hNative.trans hE, hTail, pureZ_one_gt]

end ACS12.GammaMeasure

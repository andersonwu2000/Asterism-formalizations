import ACS12.JointHighBracket

namespace ACS12.GammaMeasure
open CenteredCircle.AllN MeasureTheory Set

/-- The physical inner source supplies a feasible comparison point directly. -/
theorem _root_.ACS12.Configuration.inner_feasible_necessary {n : ℕ} {p : ℝ}
    (F : Configuration n p) (hn : 2 ≤ n) (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi)) {j k : Fin n}
    (hj : C.source.IsNext C.source.neighbor j) (hk : C.source.IsNext j k)
    (huL : 7 / 8 ≤ C.source.forwardDistance C.source.neighbor j)
    (hu₁ : C.source.forwardDistance C.source.neighbor j < 1)
    (hInner : C.source.forwardDistance j k ≤ C.source.forwardDistance C.source.neighbor j) :
    let S := C.source
    let L := S.period
    let u := S.forwardDistance S.neighbor j
    ∃ M ∈ Ioo (u / 2) u, 2 * u - 1 ≤ M ∧ 0 ≤ diagonalAdjacent p L 1 u M ∧
      0 ≤ middleBase p L u + samplingHead (rightClip p L (middleA u) (middleZ u)) u M := by
  have hp₂ : p < 2 := hP.trans_lt (by norm_num)
  let S := C.source
  let L := S.period
  let u := S.forwardDistance S.neighbor j
  let v := S.forwardDistance j k
  let m := S.mass j
  let r := S.mass k
  let R := fourthComparisonRoot p L 1 u v m
  have hL : 0 < L := S.period_pos
  have hu : 0 < u := S.forwardDistance_pos _ _
  have hv : 0 < v := S.forwardDistance_pos _ _
  have hm : 0 < m := S.mass_pos j
  have hr : 0 < r := S.mass_pos k
  have hjk : j ≠ k := fun h => (lt_irrefl _) (h ▸ hk.1)
  have hnj : S.neighbor ≠ j := fun h => (lt_irrefl _) (h ▸ hj.1)
  have hmv : m ≤ v := (S.forwardDistance_caps C.circular_caps hjk).1
  have hmu : m ≤ u := (S.forwardDistance_caps C.circular_caps hnj).2
  have hθ : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  by_cases hsmall : m ≤ 2 * u - 1
  · refine ⟨2 * u - 1, ⟨by dsimp only [u] at *; linarith only [huL], by linarith only [hu₁]⟩,
      le_rfl, (diagonalAdjacent_lowMass_pos hp hP hL hθ huL hu₁).le, ?_⟩
    exact F.mesh_scalar_necessary hn (zero_lt_one.trans_le hp) hp₂.le C hj hk hu₁.le hsmall
  have hmLow : 2 * u - 1 < m := lt_of_not_ge hsmall
  have hmL : u / 3 < m := by linarith only [hmLow,huL]
  obtain ⟨hR, _, hCap⟩ := fourthComparisonRoot_spec hp hp₂ hL hθ hv hInner hu₁ hm.le hmv
  have hHr : 0 ≤ fourthSourceRow p L 1 u v r m := F.fourthSource_nonneg hn hp hp₂.le C hj hk
  have hrr : r ≤ R := hCap r hr hHr
  have hAr : 0 ≤ adjacentSourceLaw p L 1 u v m r := F.adjacentSourceLaw_nonneg hn hp hp₂.le C hj hk
  have hA : 0 ≤ adjacentSourceLaw p L 1 u v m R := hAr.trans
    (adjacentSourceLaw_mono_r hp hp₂.le hL hθ hu hv hr hR.1 hrr)
  have hD : 0 ≤ diagonalAdjacent p L 1 u m := by
    change 0 ≤ adjacentSourceLaw p L 1 u m m (fourthComparisonRoot p L 1 u m m)
    rcases lt_or_eq_of_le hmv with hlt | he
    · have hLow : v / 3 ≤ m := by linarith only [hInner, hmL]
      have hSpeed := (fourthComparisonRoot_fixed_speed hp hp₂ hL hθ hu₁ hm hlt hInner hLow le_rfl).2
      have hR₀ := (fourthComparisonRoot_spec hp hp₂ hL hθ hm hmu hu₁ hm.le le_rfl).1.1
      exact hA.trans (adjacentSourceLaw_advance_lt hp hp₂.le hL hθ hu hm hlt hR₀ hR.1 hSpeed.le).le
    · simpa only [R, he] using hA
  have hmuStrict : m < u := lt_of_le_of_ne hmu (by
    intro he
    have hR := (fourthComparisonRoot_spec hp hp₂ hL hθ hu le_rfl hu₁ hu.le le_rfl).1
    have hNeg := adjacentSourceLaw_at_u_neg hp hp₂.le hL hθ hu hu₁ hR.1 hR.2.le
    change diagonalAdjacent p L 1 u u < 0 at hNeg
    exact hNeg.not_ge (he ▸ hD))
  refine ⟨m, ⟨by linarith only [hmLow,huL], hmuStrict⟩, hmLow.le, hD, ?_⟩
  exact F.mesh_scalar_necessary hn (zero_lt_one.trans_le hp) hp₂.le C hj hk hu₁.le le_rfl

end ACS12.GammaMeasure

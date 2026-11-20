import ACS12.OuterAdjacentComparison

/-! Exact adjacent roots at the original period and their quantitative mass comparison. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN Set Filter
open scoped Topology

theorem adjacentDiagonal_secant_lt {p L θ u x y : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hu : 0 < u) (hx : 0 < x) (hxy : x < y) :
    adjacentDiagonal p L θ u y <
      adjacentDiagonal p L θ u x - (y - x) * outerLawDenom p L θ u := by
  have h := adjacentSourceLaw_advance_lt (m := x) hp hp₂ hL hθ hu hx hxy hx (hx.trans hxy)
    (by linarith only [hxy])
  have hE : adjacentSourceLaw p L θ u y y y = adjacentSourceLaw p L θ u y x y -
      (y - x) * outerLawDenom p L θ u := by
    unfold adjacentSourceLaw outerLawDenom
    ring
  unfold adjacentDiagonal
  rw [hE]
  exact sub_lt_sub_right h _

private theorem adjacentDiagonal_continuousOn {p L θ u : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hu : 0 < u) :
    ContinuousOn (adjacentDiagonal p L θ u) (Ioi 0) := by
  intro x hx
  let A := lawPeanoKernel p L θ u .a
  let B := lawPeanoKernel p L θ u .b
  let D := lawMoment p L θ 0 u + lawSelf p L θ
  let M := u * lawMoment p L θ 1 u + D
  have hT : Tendsto (fun t : ℝ => t) (𝓝[Ioi 0] x) (𝓝 x) := nhdsWithin_le_nhds
  have hW : ContinuousWithinAt (fun t => samplingHead A t t) (Ioi 0) x :=
    lawPeanoHead_tendsto hp hp₂ hL hθ hu hx hx hT hT .a
  have hC : Continuous (fun t : ℝ => samplingTail B 0 1 + u * D - t * M) := by fun_prop
  exact hC.continuousWithinAt.add hW

theorem exists_adjacentDiagonal_root {p L θ u : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hu : 0 < u) (hu₁ : u < 1) :
    ∃ m ∈ Ioo 0 u, adjacentDiagonal p L θ u m = 0 ∧
      u - m < 1 - u ∧ ∀ q > 0, 0 ≤ adjacentDiagonal p L θ u q → q ≤ m := by
  let r := outerLawMass p L θ u
  let f := adjacentDiagonal p L θ u
  have hp₂ := hP.trans (by norm_num : (9 / 5 : ℝ) ≤ 2)
  obtain ⟨hr, hru⟩ := outerLawMass_mem hp hp₂ hL hθ hu hu₁
  have hPos : 0 < f r := adjacentDiagonal_at_outer_pos hp hp₂ hL hθ hu hu₁
  have hNeg : f u < 0 := adjacentSourceLaw_at_u_neg hp hp₂ hL hθ hu hu₁ hu le_rfl
  have hC : ContinuousOn f (Icc r u) :=
    (adjacentDiagonal_continuousOn hp hp₂ hL hθ hu).mono (fun _ h => hr.trans_le h.1)
  obtain ⟨m, hm, hRoot⟩ := intermediate_value_Icc' hru.le hC ⟨hNeg.le, hPos.le⟩
  have hm₀ := hr.trans_le hm.1
  have hmU : m < u := lt_of_le_of_ne hm.2 (fun h => hNeg.ne (h ▸ hRoot))
  have hGap := outerLawGap_lt hp hP hL hθ hu hu₁
  change u - r < 1 - u at hGap
  refine ⟨m, ⟨hm₀, hmU⟩, hRoot, by linarith only [hGap, hm.1], ?_⟩
  intro q hq hF
  by_contra! h
  have hAnti := adjacentDiagonal_strictAnti hp hp₂ hL hθ hu hm₀ hq h
  exact (hAnti.trans_le hRoot.le).not_ge hF

theorem _root_.ACS12.Configuration.adjacent_mesh_necessary {n : ℕ} {p : ℝ} (F : Configuration n p)
    (hn : 2 ≤ n) (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi)) {j k : Fin n}
    (hj : C.source.IsNext C.source.neighbor j) (hk : C.source.IsNext j k)
    (hu₁ : C.source.forwardDistance C.source.neighbor j ≤ 1)
    {M : ℝ} (hM : ∀ q > 0, 0 ≤ adjacentDiagonal p C.source.period 1
      (C.source.forwardDistance C.source.neighbor j) q → q ≤ M) :
    let S := C.source
    let u := S.forwardDistance S.neighbor j
    0 ≤ middleLawBase p S.period 1 u + samplingHead (lawRightClip p S.period 1 u) u M := by
  let S := C.source
  let u := S.forwardDistance S.neighbor j
  let v := S.forwardDistance j k
  let m := S.mass j
  let r := S.mass k
  let L := S.period
  have hL : 0 < L := S.period_pos
  have hu : 0 < u := S.forwardDistance_pos _ _
  have hv : 0 < v := S.forwardDistance_pos _ _
  have hm : 0 < m := S.mass_pos j
  have hr : 0 < r := S.mass_pos k
  have hθ : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  have hjk : j ≠ k := fun h => (lt_irrefl _) (h ▸ hk.1)
  obtain ⟨hmv, hrv⟩ := S.forwardDistance_caps C.circular_caps hjk
  have hA := F.adjacentSourceLaw_nonneg hn hp hp₂ C hj hk
  have hB : 0 ≤ adjacentSourceLaw p L 1 u v m v := hA.trans
    (adjacentSourceLaw_mono_r hp hp₂ hL hθ hu hv hr hv hrv)
  have hC : 0 ≤ adjacentDiagonal p L 1 u m := by
    rcases lt_or_eq_of_le hmv with h | h
    · exact hB.trans (adjacentSourceLaw_advance_lt (m := m) hp hp₂ hL hθ hu hm h hm hv
        (by linarith only [h])).le
    · change m = v at h
      rw [← h] at hB
      exact hB
  have hCap := hM m hm hC
  have h := F.mesh_scalar_necessary hn (zero_lt_one.trans_le hp) hp₂ C hj hk hu₁ hCap
  change 0 ≤ middleLawBase p L 1 u + samplingHead (lawRightClip p L 1 u) u M
  rw [middleLawBase, lawMoment_one_radial, lawMoment_one_slope, lawSelf, one_mul]
  have hZ : lawUnitSlope p L 1 = unitSlopeTotal p L := by
    have hEq : lawMoment p L 1 1 = imageSlope p L := funext (lawMoment_one_slope p L)
    rw [lawUnitSlope, unitSlopeTotal, hEq]
  rw [hZ]
  have hK : EqOn (lawRightClip p L 1 u) (rightClip p L (middleA u) (middleZ u)) (Ioi 0) := by
    intro t ht
    unfold lawRightClip rightClip
    rw [lawRightTest_one (zero_lt_one.trans_le hp) hL ht]
  have hHead : samplingHead (lawRightClip p L 1 u) u M =
      samplingHead (rightClip p L (middleA u) (middleZ u)) u M := by
    unfold samplingHead
    apply congrArg (M * ·)
    apply tsum_congr
    intro i
    apply hK
    change 0 < u + (i : ℝ) * M
    have hM₀ := hm.trans_le hCap
    positivity
  rw [hHead]
  exact h

end ACS12.GammaMeasure

import CenteredCircle.ActualSourceBalances
import CenteredCircle.KernelRatio

/-!
The preliminary mass bound for one actual finite periodic source. Circular
mass caps are explicit geometric premises; the physical normalization bridge
will supply them. Force premises are only two tangential rows and equal radial rows.
-/

namespace CenteredCircle.AllN

open scoped BigOperators

theorem imageTail_circle_pos {L t : ℝ} (hL : 0 < L) (ht : 0 < t)
    (kind : CircleKernelKind) : 0 < imageTail (circleKernel L kind) L t := by
  apply (circleKernel_summable hL kind t L ht hL).tsum_pos
    (fun j => (circleKernel_pos hL kind _ (by positivity)).le) 0
  simpa using circleKernel_pos hL kind t ht

theorem imageTail_circle_a_lt_b {L t : ℝ} (hL : 0 < L) (ht : 0 < t) :
    imageTail (circleKernel L .a) L t < imageTail (circleKernel L .b) L t := by
  apply (circleKernel_summable hL .a t L ht hL).tsum_lt_tsum
    (fun j => (circleKernel_a_lt_b hL (by positivity)).le) (i := 0)
    (by simpa using circleKernel_a_lt_b hL ht)
    (circleKernel_summable hL .b t L ht hL)

theorem imageTail_circle_ratio {L b t : ℝ} (hL : 0 < L) (hb : 0 < b) (hbt : b ≤ t) :
    ratioFloor b * imageTail (circleKernel L .b) L t ≤ imageTail (circleKernel L .a) L t := by
  have ht := lt_of_lt_of_le hb hbt
  have hB := circleKernel_summable hL .b t L ht hL
  have hA := circleKernel_summable hL .a t L ht hL
  rw [imageTail, imageTail, ← tsum_mul_left]
  apply (hB.mul_left (ratioFloor b)).tsum_le_tsum _ hA
  intro j
  have hj : b ≤ t + (j : ℝ) * L := le_trans hbt (le_add_of_nonneg_right (by positivity))
  have hjpos := lt_of_lt_of_le hb hj
  exact le_trans (mul_le_mul_of_nonneg_right
    (strictMonoOn_ratioFloor.monotoneOn hb hjpos hj) (circleKernel_pos hL .b _ hjpos).le)
    (circleKernel_ratio_lower hL hjpos)

theorem mass_gt_seven_tenths_of_balances {b U D : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1) (hU : 0 < U) (hU1 : U < 1) (hD : 1 < D)
    (hrow : ratioFloor b * (U + (1 - b) * D) < b * U - (1 - b) * D) :
    (7 / 10 : ℝ) < b := by
  have hc := ratioFloor_bounds hb
  have hcost : 0 ≤ (1 - b) * (1 + ratioFloor b) :=
    mul_nonneg (sub_nonneg.mpr hb1) (by linarith [hc.1])
  have hcostD := mul_le_mul_of_nonneg_left hD.le hcost
  have hdiff : 0 < b - ratioFloor b := by
    by_contra hh
    have hbad := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hh) hU.le
    nlinarith
  have hUd := mul_le_mul_of_nonneg_left hU1.le hdiff.le
  have hineq : ratioFloor b * (2 - b) < 2 * b - 1 := by nlinarith
  have hden : 0 < (b + 1) * (3 * b + 2) := by positivity
  rw [ratioFloor, div_mul_eq_mul_div] at hineq
  have hp := (div_lt_iff₀ hden).mp hineq
  by_contra hh
  have hsmall : b ≤ 7 / 10 := le_of_not_gt hh
  have hfactor : 0 ≤ (7 / 10 - b) * (9 * b ^ 2 + (83 / 10) * b + 281 / 100) := by
    apply mul_nonneg (sub_nonneg.mpr hsmall)
    positivity
  nlinarith

namespace AnchoredCircleSource

variable {ι : Type*} (F : AnchoredCircleSource ι) [DecidableEq ι]

def HasCircularMassCaps : Prop :=
  ∀ i j, i ≠ j → F.mass i ≤ |F.coordinate j - F.coordinate i| ∧
    F.mass i ≤ F.period - |F.coordinate j - F.coordinate i|

theorem leftDistance_ge_one (hcaps : F.HasCircularMassCaps) (i : ι) :
    1 ≤ F.leftDistance i := by
  by_cases hi : i = F.root
  · rw [leftDistance, hi, F.coordinate_root, sub_zero]
    linarith [F.period_ge_two]
  · have h := (hcaps F.root i (Ne.symm hi)).2
    simpa only [F.mass_root, F.coordinate_root, sub_zero,
      abs_of_nonneg (F.coordinate_nonneg i), leftDistance] using h

theorem rightDistance_ge_neighbor (hcaps : F.HasCircularMassCaps) (i : ι) :
    F.mass F.neighbor ≤ F.rightDistance i := by
  by_cases hi : i = F.root ∨ i = F.neighbor
  · rw [rightDistance, if_pos hi]
    linarith [F.coordinate_nonneg i, F.period_ge_two, F.mass_neighbor_le_one]
  · have hni : i ≠ F.neighbor := fun h => hi (Or.inr h)
    have hri : i ≠ F.root := fun h => hi (Or.inl h)
    have h := (hcaps F.neighbor i (Ne.symm hni)).1
    have hp : 0 ≤ F.coordinate i - 1 := by linarith [F.other_coordinate i hri hni]
    rw [F.coordinate_neighbor, abs_of_nonneg hp] at h
    simpa only [rightDistance, if_neg hi] using h

variable [Fintype ι]

theorem leftExterior_circle_a_pos : 0 < F.leftExterior (circleKernel F.period .a) := by
  apply Finset.sum_pos'
  · intro i _
    exact (mul_pos (F.mass_pos i) (imageTail_circle_pos F.period_pos (F.leftDistance_pos i) .a)).le
  · exact ⟨F.root, Finset.mem_univ _,
      mul_pos (F.mass_pos _) (imageTail_circle_pos F.period_pos (F.leftDistance_pos _) .a)⟩

theorem leftExterior_circle_a_lt_b :
    F.leftExterior (circleKernel F.period .a) < F.leftExterior (circleKernel F.period .b) := by
  apply Finset.sum_lt_sum
  · intro i _
    exact mul_le_mul_of_nonneg_left
      (imageTail_circle_a_lt_b F.period_pos (F.leftDistance_pos i)).le (F.mass_pos i).le
  · exact ⟨F.root, Finset.mem_univ _, mul_lt_mul_of_pos_left
      (imageTail_circle_a_lt_b F.period_pos (F.leftDistance_pos _)) (F.mass_pos _)⟩

theorem rightExterior_circle_ratio (hcaps : F.HasCircularMassCaps) :
    ratioFloor (F.mass F.neighbor) * F.rightExterior (circleKernel F.period .b) ≤
      F.rightExterior (circleKernel F.period .a) := by
  unfold rightExterior
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := mul_le_mul_of_nonneg_left
    (imageTail_circle_ratio F.period_pos (F.mass_pos _) (F.rightDistance_ge_neighbor hcaps i))
    (F.mass_pos i).le
  simpa only [mul_left_comm] using h

theorem exterior_circle_ratio_strict (hcaps : F.HasCircularMassCaps) :
    ratioFloor (F.mass F.neighbor) *
        (F.leftExterior (circleKernel F.period .a) + F.rightExterior (circleKernel F.period .b)) <
      F.leftExterior (circleKernel F.period .b) + F.rightExterior (circleKernel F.period .a) := by
  have hright := F.rightExterior_circle_ratio hcaps
  have hleft := F.leftExterior_circle_a_lt_b
  have hc := (ratioFloor_bounds (F.mass_pos F.neighbor)).2
  have hpos := F.leftExterior_circle_a_pos
  have hscale := mul_lt_mul_of_pos_right hc hpos
  nlinarith

theorem neighbor_mass_gt_seven_tenths (hcaps : F.HasCircularMassCaps)
    (hrad : F.rootRadialRow = F.neighborRadialRow)
    (hroot : F.rootTorqueRow = 0) (hneighbor : F.neighborTorqueRow = 0) :
    (7 / 10 : ℝ) < F.mass F.neighbor := by
  have h := F.exterior_circle_ratio_strict hcaps
  have he := F.actual_exterior_balances hrad hroot hneighbor
  rw [he.1, he.2] at h
  exact mass_gt_seven_tenths_of_balances (F.mass_pos _) F.mass_neighbor_le_one
    (torqueKernel_one_bounds F.period_pos).1 (torqueKernel_one_bounds F.period_pos).2
    (radialCorrection_gt_one F.period_pos) h

end AnchoredCircleSource

end CenteredCircle.AllN

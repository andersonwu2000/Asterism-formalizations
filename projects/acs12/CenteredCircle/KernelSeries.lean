import CenteredCircle.KernelCalculus

/-! Absolute convergence and the A/B telescoping total. -/

namespace CenteredCircle.AllN

open MeasureTheory Filter Set
open scoped BigOperators Topology

theorem summable_radialKernel {L : ℝ} (hL : 0 < L)
    (t s : ℝ) (ht : 0 < t) (hs : 0 < s) :
    Summable (fun j : ℕ => radialKernel L (t + j * s)) :=
  summable_of_power_decay (radialKernel L) (L / 2) t s 2 (by norm_num)
    (by positivity) ht hs (fun x hx => (radialKernel_pos hL x hx).le)
    (radialKernel_quadratic_bound hL)

theorem summable_torqueKernel {L : ℝ} (hL : 0 < L)
    (t s : ℝ) (ht : 0 < t) (hs : 0 < s) :
    Summable (fun j : ℕ => torqueKernel L (t + j * s)) :=
  summable_of_cubic_decay (torqueKernel L) L t s hL.le ht hs
    (fun x hx => (torqueKernel_pos hL x hx).le) (torqueKernel_cubic_bound hL)

theorem circleKernel_pair_tsum {L : ℝ} (hL : 0 < L)
    (t : ℝ) (ht : 0 < t) :
    (∑' j : ℕ, circleKernel L .a (t + j)) +
      (∑' j : ℕ, circleKernel L .b (t + j)) = torqueKernel L t := by
  have ha : Summable (fun j : ℕ => circleKernel L .a (t + j)) := by
    simpa using circleKernel_summable hL .a t 1 ht (by norm_num)
  have hb : Summable (fun j : ℕ => circleKernel L .b (t + j)) := by
    simpa using circleKernel_summable hL .b t 1 ht (by norm_num)
  have hu : Summable (fun j : ℕ => torqueKernel L (t + j)) := by
    simpa using summable_torqueKernel hL t 1 ht (by norm_num)
  have huv : Summable (fun j : ℕ => torqueKernel L (t + (j + 1))) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hu
  have hzero := hu.tsum_eq_zero_add
  simp only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one] at hzero
  rw [← ha.tsum_add hb]
  calc
    (∑' j : ℕ, (circleKernel L .a (t + j) + circleKernel L .b (t + j))) =
        ∑' j : ℕ, (torqueKernel L (t + j) - torqueKernel L (t + (j + 1))) := by
      apply tsum_congr
      intro j
      have hx : 0 < t + (j : ℝ) := by positivity
      rw [circleKernel_add_eq_torque_difference hL _ hx]
      congr 2
      push_cast
      ring
    _ = (∑' j : ℕ, torqueKernel L (t + j)) -
        (∑' j : ℕ, torqueKernel L (t + (j + 1))) := hu.tsum_sub huv
    _ = torqueKernel L t := by linarith

theorem circleKernel_pair_unit_sampling {L : ℝ} (hL : 0 < L) :
    samplingTail (circleKernel L .a) 0 1 + samplingTail (circleKernel L .b) 0 1 =
      torqueKernel L 1 := by
  simpa only [samplingTail, zero_add, mul_one, one_mul, Nat.cast_add, Nat.cast_one,
    add_comm] using circleKernel_pair_tsum hL 1 (by norm_num)

end CenteredCircle.AllN

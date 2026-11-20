import ACS12.HighPhysicalHumpArc
import ACS12.HighCurrentHumpTransport
import Mathlib.Analysis.Real.Pi.Bounds

/-! Both complete original half-circles pay one hump atom and their entire curved integral. -/
namespace ACS12.Configuration

open Finset Set HighCurrent
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {α : ℝ} (F : ACS12.Configuration n α)

theorem physical_currentHump_capacity (o : Fin n) (w : Fin n → ℝ) {τ : ℝ}
    (hτ : 0 < τ) (hDiam : 1 ≤ 2 * F.radius)
    (hRoot : ∀ j ∈ univ.erase o,
      1 ≤ ‖F.position (F.currentOrder j) - F.position (F.currentOrder o)‖)
    (hw : ∀ j ∈ univ.erase o, 0 ≤ w j ∧ w j ≤ 1)
    (hPack : ∀ i ∈ univ.erase o, ∀ j ∈ univ.erase o, i ≠ j →
      w i ≤ ‖F.position (F.currentOrder i) - F.position (F.currentOrder j)‖) :
    (∑ j ∈ univ.erase o, w j * currentHump τ (F.currentZeta o j)) ≤
      27 * τ ^ 5 / 128 + τ ^ 6 / (10 / (2 * F.radius) ^ 2 + 3 * τ ^ 2) := by
  let D := 2 * F.radius
  let x := 1 / D ^ 2
  let B := Real.pi * D / 2
  let I := ∫ v in (0 : ℝ)..τ, τ * v ^ 3 * (τ - v) / (x + v ^ 2)
  have hD : 0 < D := mul_pos (by norm_num) F.radius_pos
  have hx : 0 < x := by unfold x; positivity
  have hB : 1 ≤ B := by
    have hPi : 2 < Real.pi := (by linarith only [Real.pi_gt_three])
    have hMul := mul_le_mul_of_nonneg_left hDiam Real.pi_pos.le
    unfold B D
    linarith only [hPi,hMul]
  have hHalf (t : Fin n → ℝ) (T : Finset (Fin n)) (hT : T ⊆ univ.erase o)
      (hDom : ∀ j ∈ T, t j ∈ Icc 1 B)
      (hSep : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → w i ≤ |t i - t j|)
      (hEq : ∀ j ∈ T, F.currentZeta o j = circleCurrentZeta D (t j)) :
      (∑ j ∈ T, w j * currentHump τ (F.currentZeta o j)) ≤ 27 * τ ^ 5 / 256 + I := by
    have h := finite_currentHump_capacity t w T hτ hx hB
      (circleCurrentZeta_continuousOn hD (by norm_num : (0 : ℝ) < 1))
      (circleCurrentZeta_antitone hD (by norm_num : (0 : ℝ) < 1))
      (fun s hs => circleCurrentZeta_nonneg hD (zero_lt_one.trans_le hs.1) hs.2)
      (fun s hs => circleCurrentZeta_deriv hD (zero_lt_one.trans_le hs.1) hs.2)
      (circleCurrentZeta_end hD) (fun j hj => hw j (hT hj)) hDom hSep
    have hSum : (∑ j ∈ T, w j * currentHump τ (F.currentZeta o j)) =
        ∑ j ∈ T, w j * currentHump τ (circleCurrentZeta D (t j)) :=
      sum_congr rfl (fun j hj => by rw [hEq j hj])
    rw [hSum]
    exact h
  let S := univ.erase o
  let front := S.filter (fun j => halfArc F.currentAngles o j ≤ Real.pi / 2)
  let back := S.filter (fun j => ¬halfArc F.currentAngles o j ≤ Real.pi / 2)
  have hFront : (∑ j ∈ front, w j * currentHump τ (F.currentZeta o j)) ≤
      27 * τ ^ 5 / 256 + I := by
    apply hHalf (F.currentForwardArc o) front (fun _ hj => (mem_filter.mp hj).1)
    · intro j hj
      have hj' := mem_filter.mp hj
      exact F.currentForwardArc_half_bounds (mem_erase.mp hj'.1).1 (hRoot j hj'.1) hj'.2
    · intro i hi j hj hij
      exact (hPack i (mem_filter.mp hi).1 j (mem_filter.mp hj).1 hij).trans
        (F.currentForwardArc_pair_chord o i j)
    · intro j hj
      have hj' := mem_filter.mp hj
      exact F.currentZeta_forward (mem_erase.mp hj'.1).1 hj'.2
  have hBack : (∑ j ∈ back, w j * currentHump τ (F.currentZeta o j)) ≤
      27 * τ ^ 5 / 256 + I := by
    apply hHalf (F.currentBackwardArc o) back (fun _ hj => (mem_filter.mp hj).1)
    · intro j hj
      have hj' := mem_filter.mp hj
      exact F.currentBackwardArc_half_bounds (mem_erase.mp hj'.1).1 (hRoot j hj'.1)
        (le_of_not_ge hj'.2)
    · intro i hi j hj hij
      exact (hPack i (mem_filter.mp hi).1 j (mem_filter.mp hj).1 hij).trans
        (F.currentBackwardArc_pair_chord o i j)
    · intro j hj
      have hj' := mem_filter.mp hj
      exact F.currentZeta_backward (mem_erase.mp hj'.1).1 (le_of_not_ge hj'.2)
  have hPartition : (∑ j ∈ front, w j * currentHump τ (F.currentZeta o j)) +
      (∑ j ∈ back, w j * currentHump τ (F.currentZeta o j)) =
      ∑ j ∈ univ.erase o, w j * currentHump τ (F.currentZeta o j) := by
    exact sum_filter_add_sum_filter_not S _ _
  have hIntegral := complete_current_hump_integral hτ hx
  change 2 * I ≤ τ ^ 6 / (10 * x + 3 * τ ^ 2) at hIntegral
  have hDen : 10 * x + 3 * τ ^ 2 = 10 / (2 * F.radius) ^ 2 + 3 * τ ^ 2 := by
    unfold x D
    ring
  rw [← hDen]
  linarith only [hFront,hBack,hPartition,hIntegral]

end ACS12.Configuration

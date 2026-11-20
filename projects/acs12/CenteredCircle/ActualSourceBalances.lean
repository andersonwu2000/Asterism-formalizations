import CenteredCircle.CorrectedRows

/-!
The two A/B identities on one actual finite periodic source. The force-row
hypotheses are explicit; they are not independent optimized exterior sources.
-/

namespace CenteredCircle.AllN

open scoped BigOperators

theorem imageTail_circle_a {L t : ℝ} (hL : 0 < L) (ht : 0 < t) :
    imageTail (circleKernel L .a) L t = imageTail (radialKernel L) L t -
      imageTail (fun x => radialKernel L (x + 1)) L t -
      imageTail (fun x => torqueKernel L (x + 1)) L t := by
  have h0 := summable_radialKernel hL t L ht hL
  have h1 : Summable (fun j : ℕ => radialKernel L ((t + j * L) + 1)) := by
    simpa only [add_assoc, add_left_comm, add_comm] using
      summable_radialKernel hL (t + 1) L (by linarith) hL
  have h2 : Summable (fun j : ℕ => torqueKernel L ((t + j * L) + 1)) := by
    simpa only [add_assoc, add_left_comm, add_comm] using
      summable_torqueKernel hL (t + 1) L (by linarith) hL
  change (∑' j : ℕ, circleKernel L .a (t + j * L)) =
    (∑' j : ℕ, radialKernel L (t + j * L)) -
    (∑' j : ℕ, radialKernel L ((t + j * L) + 1)) -
    (∑' j : ℕ, torqueKernel L ((t + j * L) + 1))
  rw [← h0.tsum_sub h1, ← (h0.sub h1).tsum_sub h2]
  apply tsum_congr
  intro j
  exact circleKernel_a_eq_difference hL _ (by positivity)

theorem imageTail_circle_b {L t : ℝ} (hL : 0 < L) (ht : 0 < t) :
    imageTail (circleKernel L .b) L t = imageTail (torqueKernel L) L t -
      (imageTail (radialKernel L) L t - imageTail (fun x => radialKernel L (x + 1)) L t) := by
  have h0 := summable_torqueKernel hL t L ht hL
  have h1 := summable_radialKernel hL t L ht hL
  have h2 : Summable (fun j : ℕ => radialKernel L ((t + j * L) + 1)) := by
    simpa only [add_assoc, add_left_comm, add_comm] using
      summable_radialKernel hL (t + 1) L (by linarith) hL
  change (∑' j : ℕ, circleKernel L .b (t + j * L)) =
    (∑' j : ℕ, torqueKernel L (t + j * L)) -
    ((∑' j : ℕ, radialKernel L (t + j * L)) -
    (∑' j : ℕ, radialKernel L ((t + j * L) + 1)))
  rw [← h1.tsum_sub h2, ← h0.tsum_sub (h1.sub h2)]
  apply tsum_congr
  intro j
  exact circleKernel_b_eq_difference hL _ (by positivity)

theorem weighted_image_circle_a {ι : Type*} [Fintype ι] (q d : ι → ℝ)
    {L : ℝ} (hL : 0 < L) (hd : ∀ i, 0 < d i) :
    (∑ i, q i * imageTail (circleKernel L .a) L (d i)) =
      (∑ i, q i * imageTail (radialKernel L) L (d i)) -
      (∑ i, q i * imageTail (fun x => radialKernel L (x + 1)) L (d i)) -
      (∑ i, q i * imageTail (fun x => torqueKernel L (x + 1)) L (d i)) := by
  calc
    _ = ∑ i, q i * (imageTail (radialKernel L) L (d i) -
        imageTail (fun x => radialKernel L (x + 1)) L (d i) -
        imageTail (fun x => torqueKernel L (x + 1)) L (d i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [imageTail_circle_a hL (hd i)]
    _ = _ := by simp only [mul_sub, Finset.sum_sub_distrib]

theorem weighted_image_circle_b {ι : Type*} [Fintype ι] (q d : ι → ℝ)
    {L : ℝ} (hL : 0 < L) (hd : ∀ i, 0 < d i) :
    (∑ i, q i * imageTail (circleKernel L .b) L (d i)) =
      (∑ i, q i * imageTail (torqueKernel L) L (d i)) -
      ((∑ i, q i * imageTail (radialKernel L) L (d i)) -
      (∑ i, q i * imageTail (fun x => radialKernel L (x + 1)) L (d i))) := by
  calc
    _ = ∑ i, q i * (imageTail (torqueKernel L) L (d i) -
        (imageTail (radialKernel L) L (d i) -
        imageTail (fun x => radialKernel L (x + 1)) L (d i))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [imageTail_circle_b hL (hd i)]
    _ = _ := by simp only [mul_sub, Finset.sum_sub_distrib]

namespace AnchoredCircleSource

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : AnchoredCircleSource ι)

theorem leftExterior_circle_a :
    F.leftExterior (circleKernel F.period .a) = F.leftExterior (radialKernel F.period) -
      F.leftExterior (fun x => radialKernel F.period (x + 1)) -
      F.leftExterior (fun x => torqueKernel F.period (x + 1)) :=
  weighted_image_circle_a F.mass F.leftDistance F.period_pos F.leftDistance_pos

theorem rightExterior_circle_a :
    F.rightExterior (circleKernel F.period .a) = F.rightExterior (radialKernel F.period) -
      F.rightExterior (fun x => radialKernel F.period (x + 1)) -
      F.rightExterior (fun x => torqueKernel F.period (x + 1)) :=
  weighted_image_circle_a F.mass F.rightDistance F.period_pos F.rightDistance_pos

theorem leftExterior_circle_b :
    F.leftExterior (circleKernel F.period .b) = F.leftExterior (torqueKernel F.period) -
      (F.leftExterior (radialKernel F.period) - F.leftExterior (fun x => radialKernel F.period (x + 1))) :=
  weighted_image_circle_b F.mass F.leftDistance F.period_pos F.leftDistance_pos

theorem rightExterior_circle_b :
    F.rightExterior (circleKernel F.period .b) = F.rightExterior (torqueKernel F.period) -
      (F.rightExterior (radialKernel F.period) - F.rightExterior (fun x => radialKernel F.period (x + 1))) :=
  weighted_image_circle_b F.mass F.rightDistance F.period_pos F.rightDistance_pos

theorem actual_exterior_balances (hrad : F.rootRadialRow = F.neighborRadialRow)
    (hroot : F.rootTorqueRow = 0) (hneighbor : F.neighborTorqueRow = 0) :
    (F.leftExterior (circleKernel F.period .a) + F.rightExterior (circleKernel F.period .b) =
      torqueKernel F.period 1 + (1 - F.mass F.neighbor) * radialCorrection F.period) ∧
    (F.leftExterior (circleKernel F.period .b) + F.rightExterior (circleKernel F.period .a) =
      F.mass F.neighbor * torqueKernel F.period 1 -
        (1 - F.mass F.neighbor) * radialCorrection F.period) := by
  have hr0 := F.root_radial_images
  have hr1 := F.neighbor_radial_images
  have ht0 := F.root_torque_images
  have ht1 := F.neighbor_torque_images
  rw [hrad] at hr0
  rw [hroot, neg_zero] at ht0
  rw [hneighbor, neg_zero] at ht1
  rw [F.leftExterior_circle_a, F.rightExterior_circle_b,
    F.leftExterior_circle_b, F.rightExterior_circle_a, radialCorrection]
  constructor <;> nlinarith

end AnchoredCircleSource

end CenteredCircle.AllN

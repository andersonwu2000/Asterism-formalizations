import CenteredCircle.ImageRowDecomposition

/-! Weighted image decompositions and their exact radial/torque specializations. -/

namespace CenteredCircle.AllN

open scoped BigOperators

theorem weighted_sum_with_anchor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι) (c : ℝ) (q f : ι → ℝ) :
    (∑ i, q i * (if i = a then c else f i)) =
      q a * c + ∑ i ∈ Finset.univ.erase a, q i * f i := by
  rw [← sum_with_anchor a (q a * c) (fun i => q i * f i)]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i = a <;> simp [h]

namespace AnchoredCircleSource

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : AnchoredCircleSource ι)

theorem root_image_decomposition (K : ℝ → ℝ) (ε : ℝ)
    (hs : Summable (fun j : ℕ => K (1 + j * F.period))) :
    ε * F.leftExterior K + F.rightExterior (fun t => K (t + 1)) + F.mass F.neighbor * K 1 =
      (1 + ε) * imageTail K F.period F.period +
        ∑ i ∈ Finset.univ.erase F.root, F.mass i *
          (imageTail K F.period (F.coordinate i) +
            ε * imageTail K F.period (F.period - F.coordinate i)) := by
  calc
    _ = ∑ i, F.mass i * (ε * imageTail K F.period (F.leftDistance i) +
        imageTail K F.period (F.rightDistance i + 1) +
          (if i = F.neighbor then K 1 else 0)) := by
      simp only [leftExterior, rightExterior, imageTail_shift, mul_add,
        Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true, Finset.mul_sum, mul_assoc, mul_left_comm]
    _ = ∑ i, F.mass i * (if i = F.root then (1 + ε) * imageTail K F.period F.period
        else imageTail K F.period (F.coordinate i) +
          ε * imageTail K F.period (F.period - F.coordinate i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [F.root_image_atom K ε hs i]
    _ = _ := by rw [weighted_sum_with_anchor, F.mass_root, one_mul]

theorem neighbor_image_decomposition (K : ℝ → ℝ) (ε : ℝ)
    (hs : Summable (fun j : ℕ => K (1 + j * F.period))) :
    ε * F.leftExterior (fun t => K (t + 1)) + F.rightExterior K + ε * K 1 =
      F.mass F.neighbor * ((1 + ε) * imageTail K F.period F.period) +
        ∑ i ∈ Finset.univ.erase F.neighbor, F.mass i *
          (imageTail K F.period (F.rightDistance i) +
            ε * imageTail K F.period (F.period - F.rightDistance i)) := by
  calc
    _ = ∑ i, F.mass i * (ε * imageTail K F.period (F.leftDistance i + 1) +
        imageTail K F.period (F.rightDistance i) +
          (if i = F.root then ε * K 1 else 0)) := by
      simp only [leftExterior, rightExterior, imageTail_shift, mul_add,
        Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true, Finset.mul_sum, F.mass_root, one_mul,
        mul_assoc, mul_left_comm]
    _ = ∑ i, F.mass i * (if i = F.neighbor then (1 + ε) * imageTail K F.period F.period
        else imageTail K F.period (F.rightDistance i) +
          ε * imageTail K F.period (F.period - F.rightDistance i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [F.neighbor_image_atom K ε hs i]
    _ = _ := weighted_sum_with_anchor _ _ _ _

theorem rootRadialRow_eq_image_pairs :
    F.rootRadialRow = ∑ i ∈ Finset.univ.erase F.root, F.mass i *
      (imageTail (radialKernel F.period) F.period (F.coordinate i) +
        imageTail (radialKernel F.period) F.period (F.period - F.coordinate i)) := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [radial_image_pair F.period_pos (F.coordinate_pos_of_ne_root (Finset.mem_erase.mp hi).1)
    (F.coordinate_lt_period i)]

theorem neighborRadialRow_eq_image_pairs :
    F.neighborRadialRow = ∑ i ∈ Finset.univ.erase F.neighbor, F.mass i *
      (imageTail (radialKernel F.period) F.period (F.rightDistance i) +
        imageTail (radialKernel F.period) F.period (F.period - F.rightDistance i)) := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [radial_image_pair F.period_pos (F.rightDistance_pos i)
    (F.rightDistance_lt_period (Finset.mem_erase.mp hi).1)]

theorem neg_rootTorqueRow_eq_image_pairs :
    -F.rootTorqueRow = ∑ i ∈ Finset.univ.erase F.root, F.mass i *
      (imageTail (torqueKernel F.period) F.period (F.coordinate i) -
        imageTail (torqueKernel F.period) F.period (F.period - F.coordinate i)) := by
  rw [rootTorqueRow, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [torque_image_pair F.period_pos (F.coordinate_pos_of_ne_root (Finset.mem_erase.mp hi).1)
    (F.coordinate_lt_period i)]
  ring

theorem neg_neighborTorqueRow_eq_image_pairs :
    -F.neighborTorqueRow = ∑ i ∈ Finset.univ.erase F.neighbor, F.mass i *
      (imageTail (torqueKernel F.period) F.period (F.rightDistance i) -
        imageTail (torqueKernel F.period) F.period (F.period - F.rightDistance i)) := by
  rw [neighborTorqueRow, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [torque_image_pair F.period_pos (F.rightDistance_pos i)
    (F.rightDistance_lt_period (Finset.mem_erase.mp hi).1)]
  ring

theorem root_radial_images :
    F.leftExterior (radialKernel F.period) +
      F.rightExterior (fun t => radialKernel F.period (t + 1)) +
      F.mass F.neighbor * radialKernel F.period 1 =
        selfImageTerm F.period + F.rootRadialRow := by
  have h := F.root_image_decomposition (radialKernel F.period) 1
    (summable_radialKernel F.period_pos 1 F.period (by norm_num) F.period_pos)
  simp only [one_mul, one_add_one_eq_two] at h
  rw [← F.rootRadialRow_eq_image_pairs] at h
  simpa only [imageTail, selfImageTerm] using h

theorem neighbor_radial_images :
    F.leftExterior (fun t => radialKernel F.period (t + 1)) +
      F.rightExterior (radialKernel F.period) + radialKernel F.period 1 =
        F.mass F.neighbor * selfImageTerm F.period + F.neighborRadialRow := by
  have h := F.neighbor_image_decomposition (radialKernel F.period) 1
    (summable_radialKernel F.period_pos 1 F.period (by norm_num) F.period_pos)
  simp only [one_mul, one_add_one_eq_two] at h
  rw [← F.neighborRadialRow_eq_image_pairs] at h
  simpa only [imageTail, selfImageTerm] using h

theorem root_torque_images :
    -F.leftExterior (torqueKernel F.period) +
      F.rightExterior (fun t => torqueKernel F.period (t + 1)) +
      F.mass F.neighbor * torqueKernel F.period 1 = -F.rootTorqueRow := by
  have h := F.root_image_decomposition (torqueKernel F.period) (-1)
    (summable_torqueKernel F.period_pos 1 F.period (by norm_num) F.period_pos)
  simpa only [neg_one_mul, add_neg_cancel, zero_mul, zero_add, zero_sub, ← sub_eq_add_neg,
    ← F.neg_rootTorqueRow_eq_image_pairs] using h

theorem neighbor_torque_images :
    -F.leftExterior (fun t => torqueKernel F.period (t + 1)) +
      F.rightExterior (torqueKernel F.period) - torqueKernel F.period 1 = -F.neighborTorqueRow := by
  have h := F.neighbor_image_decomposition (torqueKernel F.period) (-1)
    (summable_torqueKernel F.period_pos 1 F.period (by norm_num) F.period_pos)
  simpa only [neg_one_mul, add_neg_cancel, zero_mul, mul_zero, zero_add, zero_sub, ← sub_eq_add_neg,
    ← F.neg_neighborTorqueRow_eq_image_pairs] using h

end AnchoredCircleSource

end CenteredCircle.AllN

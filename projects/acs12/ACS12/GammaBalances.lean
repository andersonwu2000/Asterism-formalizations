import ACS12.GammaTorque

/-! The two exterior A/B balances of the original occupied source. -/

namespace ACS12.GammaMeasure

open Set
open scoped BigOperators
open CenteredCircle.AllN (AnchoredCircleSource NormalizedCircleChart imageTail)

noncomputable def imageA (p L t : ℝ) : ℝ :=
  imagePotential p L t - imagePotential p L (t + 1) - imageSlope p L (t + 1)

noncomputable def imageB (p L t : ℝ) : ℝ :=
  imageSlope p L t - (imagePotential p L t - imagePotential p L (t + 1))

private theorem imageTail_imageA {p L t : ℝ} (hp : 0 < p) (hL : 0 < L) (ht : 0 < t) :
    imageTail (imageA p L) L t =
      imageTail (imagePotential p L) L t -
      imageTail (fun x => imagePotential p L (x + 1)) L t -
      imageTail (fun x => imageSlope p L (x + 1)) L t := by
  have hk := imagePotential_samples_summable hp hL ht
  have hk' : Summable (fun j : ℕ => imagePotential p L (t + (j : ℝ) * L + 1)) := by
    simpa only [add_right_comm] using
      imagePotential_samples_summable hp hL (show 0 < t + 1 by linarith)
  have hu' : Summable (fun j : ℕ => imageSlope p L (t + (j : ℝ) * L + 1)) := by
    simpa only [add_right_comm] using
      (imageSlope_samples_hasSum hp hL (show 0 < t + 1 by linarith)).summable
  simp only [imageTail, imageA, (hk.sub hk').tsum_sub hu', hk.tsum_sub hk']

private theorem imageTail_imageB {p L t : ℝ} (hp : 0 < p) (hL : 0 < L) (ht : 0 < t) :
    imageTail (imageB p L) L t =
      imageTail (imageSlope p L) L t -
      (imageTail (imagePotential p L) L t -
        imageTail (fun x => imagePotential p L (x + 1)) L t) := by
  have hu := (imageSlope_samples_hasSum hp hL ht).summable
  have hk := imagePotential_samples_summable hp hL ht
  have hk' : Summable (fun j : ℕ => imagePotential p L (t + (j : ℝ) * L + 1)) := by
    simpa only [add_right_comm] using
      imagePotential_samples_summable hp hL (show 0 < t + 1 by linarith)
  simp only [imageTail, imageB, hu.tsum_sub (hk.sub hk'), hk.tsum_sub hk']

private theorem weighted_imageA {ι : Type*} [Fintype ι] {p L : ℝ}
    (hp : 0 < p) (hL : 0 < L) (q d : ι → ℝ) (hd : ∀ i, 0 < d i) :
    (∑ i, q i * imageTail (imageA p L) L (d i)) =
      (∑ i, q i * imageTail (imagePotential p L) L (d i)) -
      (∑ i, q i * imageTail (fun x => imagePotential p L (x + 1)) L (d i)) -
      (∑ i, q i * imageTail (fun x => imageSlope p L (x + 1)) L (d i)) := by
  simp_rw [imageTail_imageA hp hL (hd _), mul_sub, Finset.sum_sub_distrib]

private theorem weighted_imageB {ι : Type*} [Fintype ι] {p L : ℝ}
    (hp : 0 < p) (hL : 0 < L) (q d : ι → ℝ) (hd : ∀ i, 0 < d i) :
    (∑ i, q i * imageTail (imageB p L) L (d i)) =
      (∑ i, q i * imageTail (imageSlope p L) L (d i)) -
      ((∑ i, q i * imageTail (imagePotential p L) L (d i)) -
       (∑ i, q i * imageTail (fun x => imagePotential p L (x + 1)) L (d i))) := by
  simp_rw [imageTail_imageB hp hL (hd _), mul_sub, Finset.sum_sub_distrib]

private theorem radialRow_from_images {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p L : ℝ} (hp : 0 < p) (hL : 0 < L) (q d : ι → ℝ) (a : ι)
    (hd : ∀ i, i ≠ a → 0 < d i ∧ d i < L) :
    (∑ i ∈ Finset.univ.erase a, q i *
      (imageTail (imagePotential p L) L (d i) +
        imageTail (imagePotential p L) L (L - d i))) =
      ∑ i ∈ Finset.univ.erase a, q i * circlePower p L (d i) := by
  apply Finset.sum_congr rfl
  intro i hi
  have h := hd i (Finset.mem_erase.mp hi).1
  rw [imagePotential_pair hp hL h.1 h.2]

private theorem torqueRow_from_images {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p L : ℝ} (hp : 0 < p) (hL : 0 < L) (q d : ι → ℝ) (a : ι)
    (hd : ∀ i, i ≠ a → 0 < d i ∧ d i < L) :
    (∑ i ∈ Finset.univ.erase a, q i *
      (imageTail (imageSlope p L) L (d i) -
        imageTail (imageSlope p L) L (L - d i))) =
      p * (Real.pi / L) ^ (p + 1) *
        ∑ i ∈ Finset.univ.erase a, q i * circleTorque p L (d i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have h := hd i (Finset.mem_erase.mp hi).1
  rw [imageSlope_pair hp hL h.1 h.2]
  ring

/-- The positive-power A/B balances at the two actual anchors. The radial
row keeps the positive literal self term and the signed self torque cancels. -/
theorem _root_.ACS12.Configuration.anchored_image_balances {n : ℕ} {p : ℝ}
    (F : Configuration n p) (hp : 0 < p) (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi)) :
    let S := C.source
    let L := S.period
    let b := S.mass S.neighbor
    let D := imagePotential p L 1 + imageSelf p L
    (S.leftExterior (imageA p L) + S.rightExterior (imageB p L) =
        imageSlope p L 1 + (1 - b) * D) ∧
      (S.leftExterior (imageB p L) + S.rightExterior (imageA p L) =
        b * imageSlope p L 1 - (1 - b) * D) := by
  let S := C.source
  let L := S.period
  let k := imagePotential p L
  let u := imageSlope p L
  have hL : 0 < L := S.period_pos
  have hSelf : 2 * imageTail k L L = imageSelf p L := by
    unfold imageTail imageSelf
    congr 1
    apply tsum_congr
    intro j
    change imagePotential p L (L + (j : ℝ) * L) = imagePotential p L (((j : ℝ) + 1) * L)
    congr 1
    ring
  have rootRange (i : Fin n) (hi : i ≠ S.root) : 0 < S.coordinate i ∧ S.coordinate i < L :=
    ⟨S.coordinate_pos_of_ne_root hi, S.coordinate_lt_period i⟩
  have neighborRange (i : Fin n) (hi : i ≠ S.neighbor) :
      0 < S.rightDistance i ∧ S.rightDistance i < L :=
    ⟨S.rightDistance_pos i, S.rightDistance_lt_period hi⟩
  have hk := imagePotential_samples_summable hp hL (show 0 < (1 : ℝ) by norm_num)
  have hu := (imageSlope_samples_hasSum hp hL (show 0 < (1 : ℝ) by norm_num)).summable
  have hr₀ := S.root_image_decomposition k 1 hk
  have hr₁ := S.neighbor_image_decomposition k 1 hk
  have ht₀ := S.root_image_decomposition u (-1) hu
  have ht₁ := S.neighbor_image_decomposition u (-1) hu
  simp only [one_mul, one_add_one_eq_two] at hr₀ hr₁
  simp only [neg_one_mul, add_neg_cancel, zero_mul, zero_add, mul_zero, ← sub_eq_add_neg] at ht₀ ht₁
  have hrad := F.anchored_radial_eq C
  obtain ⟨hroot, hneighbor⟩ := F.anchored_torque_eq_zero C
  rw [hSelf, radialRow_from_images hp hL S.mass S.coordinate S.root rootRange, hrad] at hr₀
  rw [hSelf, radialRow_from_images hp hL S.mass S.rightDistance S.neighbor neighborRange] at hr₁
  rw [torqueRow_from_images hp hL S.mass S.coordinate S.root rootRange, hroot, mul_zero] at ht₀
  rw [torqueRow_from_images hp hL S.mass S.rightDistance S.neighbor neighborRange,
    hneighbor, mul_zero] at ht₁
  have hLA : S.leftExterior (imageA p L) = S.leftExterior k -
      S.leftExterior (fun x => k (x + 1)) - S.leftExterior (fun x => u (x + 1)) :=
    weighted_imageA hp hL S.mass S.leftDistance S.leftDistance_pos
  have hRA : S.rightExterior (imageA p L) = S.rightExterior k -
      S.rightExterior (fun x => k (x + 1)) - S.rightExterior (fun x => u (x + 1)) :=
    weighted_imageA hp hL S.mass S.rightDistance S.rightDistance_pos
  have hLB : S.leftExterior (imageB p L) = S.leftExterior u -
      (S.leftExterior k - S.leftExterior (fun x => k (x + 1))) :=
    weighted_imageB hp hL S.mass S.leftDistance S.leftDistance_pos
  have hRB : S.rightExterior (imageB p L) = S.rightExterior u -
      (S.rightExterior k - S.rightExterior (fun x => k (x + 1))) :=
    weighted_imageB hp hL S.mass S.rightDistance S.rightDistance_pos
  change (S.leftExterior (imageA p L) + S.rightExterior (imageB p L) =
      u 1 + (1 - S.mass S.neighbor) * (k 1 + imageSelf p L)) ∧
    (S.leftExterior (imageB p L) + S.rightExterior (imageA p L) =
      S.mass S.neighbor * u 1 - (1 - S.mass S.neighbor) * (k 1 + imageSelf p L))
  rw [hLA, hRA, hLB, hRB]
  constructor <;> nlinarith

end ACS12.GammaMeasure

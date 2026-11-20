import ACS12.MiddleSource

/-! The exact signed receiver from the original pair of radial and torque rows. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN
open scoped BigOperators

noncomputable def leftTest (p L a z t : ℝ) : ℝ :=
  imagePotential p L t - imagePotential p L (t + 1) -
    a * imageSlope p L t - z * imageSlope p L (t + 1)

noncomputable def rightTest (p L a z t : ℝ) : ℝ :=
  z * imageSlope p L t + a * imageSlope p L (t + 1) -
    imagePotential p L t + imagePotential p L (t + 1)

private theorem leftTest_tail_eq {p L t : ℝ} (hp : 0 < p) (hL : 0 < L) (ht : 0 < t)
    (a z : ℝ) :
    imageTail (leftTest p L a z) L t = imageTail (imagePotential p L) L t -
      imageTail (fun x => imagePotential p L (x + 1)) L t - a * imageTail (imageSlope p L) L t -
      z * imageTail (fun x => imageSlope p L (x + 1)) L t := by
  have hk := imagePotential_samples_summable hp hL ht
  have hk' : Summable (fun j : ℕ => imagePotential p L (t + j * L + 1)) := by
    simpa only [add_right_comm] using imagePotential_samples_summable hp hL (show 0 < t + 1 by positivity)
  have hu := (imageSlope_samples_hasSum hp hL ht).summable
  have hu' : Summable (fun j : ℕ => imageSlope p L (t + j * L + 1)) := by
    simpa only [add_right_comm] using (imageSlope_samples_hasSum hp hL (show 0 < t + 1 by positivity)).summable
  simp only [imageTail, leftTest, (((hk.sub hk').sub (hu.mul_left a)).tsum_sub (hu'.mul_left z)),
    ((hk.sub hk').tsum_sub (hu.mul_left a)), hk.tsum_sub hk', tsum_mul_left]

private theorem rightTest_tail_eq {p L t : ℝ} (hp : 0 < p) (hL : 0 < L) (ht : 0 < t)
    (a z : ℝ) :
    imageTail (rightTest p L a z) L t = z * imageTail (imageSlope p L) L t +
      a * imageTail (fun x => imageSlope p L (x + 1)) L t -
      imageTail (imagePotential p L) L t + imageTail (fun x => imagePotential p L (x + 1)) L t := by
  have hk := imagePotential_samples_summable hp hL ht
  have hk' : Summable (fun j : ℕ => imagePotential p L (t + j * L + 1)) := by
    simpa only [add_right_comm] using imagePotential_samples_summable hp hL (show 0 < t + 1 by positivity)
  have hu := (imageSlope_samples_hasSum hp hL ht).summable
  have hu' : Summable (fun j : ℕ => imageSlope p L (t + j * L + 1)) := by
    simpa only [add_right_comm] using (imageSlope_samples_hasSum hp hL (show 0 < t + 1 by positivity)).summable
  simp only [imageTail, rightTest, (((hu.mul_left z).add (hu'.mul_left a)).sub hk).tsum_add hk',
    ((hu.mul_left z).add (hu'.mul_left a)).tsum_sub hk, (hu.mul_left z).tsum_add (hu'.mul_left a),
    tsum_mul_left]

theorem _root_.ACS12.Configuration.exact_middle_covector {n : ℕ} {p : ℝ}
    (F : Configuration n p) (hp : 0 < p) (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi))
    (a z : ℝ) :
    let S := C.source
    let L := S.period
    let b := S.mass S.neighbor
    S.backwardExterior (leftTest p L a z) S.root + S.forwardExterior (rightTest p L a z) S.neighbor =
      (1 - b) * (imagePotential p L 1 + imageSelf p L) - a * b * imageSlope p L 1 + z * imageSlope p L 1 := by
  let S := C.source
  let L := S.period
  let K := imagePotential p L
  let U := imageSlope p L
  have hL : 0 < L := S.period_pos
  have hNext := S.root_neighbor_next
  have hOne : S.forwardDistance S.root S.neighbor = 1 := by
    rw [S.forwardDistance_eq_sub hNext.1, S.coordinate_root, S.coordinate_neighbor, sub_zero]
  have hk := imagePotential_samples_summable hp hL (S.forwardDistance_pos S.root S.neighbor)
  have hu := (imageSlope_samples_hasSum hp hL (S.forwardDistance_pos S.root S.neighbor)).summable
  have hr₀ := F.chart_radial_images C hp S.root
  have hr₁ := F.chart_radial_images C hp S.neighbor
  have ht₀ := F.chart_torque_images C hp S.root
  have ht₁ := F.chart_torque_images C hp S.neighbor
  rw [S.forwardExterior_edge K hNext.1 hNext.2 hk, hOne] at hr₀
  rw [S.backwardExterior_edge K hNext.1 hNext.2 hk, hOne] at hr₁
  rw [S.forwardExterior_edge U hNext.1 hNext.2 hu, hOne] at ht₀
  rw [S.backwardExterior_edge U hNext.1 hNext.2 hu, hOne] at ht₁
  rw [S.mass_root, one_mul] at hr₀ hr₁ ht₁
  have hLP :
      S.backwardExterior (leftTest p L a z) S.root =
        S.backwardExterior K S.root - S.backwardExterior (fun t => K (t + 1)) S.root -
          a * S.backwardExterior U S.root - z * S.backwardExterior (fun t => U (t + 1)) S.root := by
    unfold AnchoredCircleSource.backwardExterior
    have hpt (k : Fin n) :
        imageTail (leftTest p L a z) S.period (S.forwardDistance k S.root) =
        imageTail K S.period (S.forwardDistance k S.root) -
          imageTail (fun t => K (t + 1)) S.period (S.forwardDistance k S.root) -
          a * imageTail U S.period (S.forwardDistance k S.root) -
          z * imageTail (fun t => U (t + 1)) S.period (S.forwardDistance k S.root) :=
      leftTest_tail_eq hp hL (S.forwardDistance_pos k S.root) a z
    simp only [hpt, mul_sub,
      Finset.sum_sub_distrib, mul_left_comm (S.mass _) a, mul_left_comm (S.mass _) z, Finset.mul_sum]
  have hRG :
      S.forwardExterior (rightTest p L a z) S.neighbor =
        z * S.forwardExterior U S.neighbor + a * S.forwardExterior (fun t => U (t + 1)) S.neighbor -
          S.forwardExterior K S.neighbor + S.forwardExterior (fun t => K (t + 1)) S.neighbor := by
    unfold AnchoredCircleSource.forwardExterior
    have hpt (k : Fin n) :
        imageTail (rightTest p L a z) S.period (S.forwardDistance S.neighbor k) =
        z * imageTail U S.period (S.forwardDistance S.neighbor k) +
          a * imageTail (fun t => U (t + 1)) S.period (S.forwardDistance S.neighbor k) -
          imageTail K S.period (S.forwardDistance S.neighbor k) +
          imageTail (fun t => K (t + 1)) S.period (S.forwardDistance S.neighbor k) :=
      rightTest_tail_eq hp hL (S.forwardDistance_pos S.neighbor k) a z
    simp only [hpt, mul_add, mul_sub,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_left_comm (S.mass _) a,
      mul_left_comm (S.mass _) z, Finset.mul_sum]
  dsimp only
  rw [hLP, hRG]
  linear_combination hr₀ - hr₁ + a * ht₀ + z * ht₁

end ACS12.GammaMeasure

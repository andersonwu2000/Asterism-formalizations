import ACS12.GammaEdgeRows

/-! Two undivided balances at every actual consecutive edge. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN
open scoped BigOperators

private theorem peanoTail_a {p L h t : ℝ} (hp : 0 < p) (hL : 0 < L) (hh : 0 < h)
    (ht : 0 < t) :
    imageTail (peanoKernel p L h .a) L t = imageTail (imagePotential p L) L t -
      imageTail (fun x => imagePotential p L (x + h)) L t -
      h * imageTail (fun x => imageSlope p L (x + h)) L t := by
  have hk := imagePotential_samples_summable hp hL ht
  have hk' : Summable (fun j : ℕ => imagePotential p L (t + (j : ℝ) * L + h)) := by
    simpa only [add_right_comm] using imagePotential_samples_summable hp hL (add_pos ht hh)
  have hu' : Summable (fun j : ℕ => imageSlope p L (t + (j : ℝ) * L + h)) := by
    simpa only [add_right_comm] using (imageSlope_samples_hasSum hp hL (add_pos ht hh)).summable
  have hEq (j : ℕ) : peanoKernel p L h .a (t + (j : ℝ) * L) =
      imagePotential p L (t + (j : ℝ) * L) - imagePotential p L (t + (j : ℝ) * L + h) -
        h * imageSlope p L (t + (j : ℝ) * L + h) :=
    peanoKernel_a_eq hp hL hh (by positivity)
  unfold imageTail
  simp_rw [hEq]
  exact (((hk.sub hk').tsum_sub (hu'.mul_left h)).trans (by rw [hk.tsum_sub hk', tsum_mul_left]))

private theorem peanoTail_b {p L h t : ℝ} (hp : 0 < p) (hL : 0 < L) (hh : 0 < h)
    (ht : 0 < t) :
    imageTail (peanoKernel p L h .b) L t = h * imageTail (imageSlope p L) L t -
      (imageTail (imagePotential p L) L t - imageTail (fun x => imagePotential p L (x + h)) L t) := by
  have hk := imagePotential_samples_summable hp hL ht
  have hk' : Summable (fun j : ℕ => imagePotential p L (t + (j : ℝ) * L + h)) := by
    simpa only [add_right_comm] using imagePotential_samples_summable hp hL (add_pos ht hh)
  have hu := (imageSlope_samples_hasSum hp hL ht).summable
  have hEq (j : ℕ) : peanoKernel p L h .b (t + (j : ℝ) * L) =
      h * imageSlope p L (t + (j : ℝ) * L) -
        (imagePotential p L (t + (j : ℝ) * L) - imagePotential p L (t + (j : ℝ) * L + h)) :=
    peanoKernel_b_eq hp hL hh (by positivity)
  unfold imageTail
  simp_rw [hEq]
  exact ((hu.mul_left h).tsum_sub (hk.sub hk')).trans (by rw [hk.tsum_sub hk', tsum_mul_left])

private theorem weightedPeanoTail_a {ι : Type*} [Fintype ι] {p L h : ℝ}
    (hp : 0 < p) (hL : 0 < L) (hh : 0 < h) (q d : ι → ℝ) (hd : ∀ i, 0 < d i) :
    (∑ i, q i * imageTail (peanoKernel p L h .a) L (d i)) =
      (∑ i, q i * imageTail (imagePotential p L) L (d i)) -
      (∑ i, q i * imageTail (fun x => imagePotential p L (x + h)) L (d i)) -
      h * (∑ i, q i * imageTail (fun x => imageSlope p L (x + h)) L (d i)) := by
  simp_rw [peanoTail_a hp hL hh (hd _), mul_sub, Finset.sum_sub_distrib, mul_left_comm (q _) h,
    Finset.mul_sum]

private theorem weightedPeanoTail_b {ι : Type*} [Fintype ι] {p L h : ℝ}
    (hp : 0 < p) (hL : 0 < L) (hh : 0 < h) (q d : ι → ℝ) (hd : ∀ i, 0 < d i) :
    (∑ i, q i * imageTail (peanoKernel p L h .b) L (d i)) =
      h * (∑ i, q i * imageTail (imageSlope p L) L (d i)) -
      ((∑ i, q i * imageTail (imagePotential p L) L (d i)) -
      (∑ i, q i * imageTail (fun x => imagePotential p L (x + h)) L (d i))) := by
  simp_rw [peanoTail_b hp hL hh (hd _), mul_sub, Finset.sum_sub_distrib, mul_left_comm (q _) h,
    Finset.mul_sum]

theorem _root_.ACS12.Configuration.consecutive_image_balances {n : ℕ} {p : ℝ}
    (F : Configuration n p) (hp : 0 < p) (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi))
    {i j : Fin n} (hij : C.source.coordinate i < C.source.coordinate j)
    (hEmpty : ∀ k, ¬(C.source.coordinate i < C.source.coordinate k ∧
      C.source.coordinate k < C.source.coordinate j)) :
    let S := C.source
    let L := S.period
    let h := S.forwardDistance i j
    let D := imagePotential p L h + imageSelf p L
    (S.backwardExterior (peanoKernel p L h .a) i + S.forwardExterior (peanoKernel p L h .b) j =
      S.mass i * h * imageSlope p L h + (S.mass i - S.mass j) * D) ∧
    (S.backwardExterior (peanoKernel p L h .b) i + S.forwardExterior (peanoKernel p L h .a) j =
      S.mass j * h * imageSlope p L h + (S.mass j - S.mass i) * D) := by
  let S := C.source
  let L := S.period
  let h := S.forwardDistance i j
  let K := imagePotential p L
  let U := imageSlope p L
  have hL : 0 < L := S.period_pos
  have hh : 0 < h := S.forwardDistance_pos i j
  have hK := imagePotential_samples_summable hp hL hh
  have hU := (imageSlope_samples_hasSum hp hL hh).summable
  have hri := F.chart_radial_images C hp i
  have hrj := F.chart_radial_images C hp j
  have hti := F.chart_torque_images C hp i
  have htj := F.chart_torque_images C hp j
  rw [S.forwardExterior_edge K hij hEmpty hK] at hri
  rw [S.backwardExterior_edge K hij hEmpty hK] at hrj
  rw [S.forwardExterior_edge U hij hEmpty hU] at hti
  rw [S.backwardExterior_edge U hij hEmpty hU] at htj
  have hLA := weightedPeanoTail_a hp hL hh S.mass (fun k => S.forwardDistance k i)
    (fun k => S.forwardDistance_pos k i)
  have hLB := weightedPeanoTail_b hp hL hh S.mass (fun k => S.forwardDistance k i)
    (fun k => S.forwardDistance_pos k i)
  have hRA := weightedPeanoTail_a hp hL hh S.mass (S.forwardDistance j)
    (S.forwardDistance_pos j)
  have hRB := weightedPeanoTail_b hp hL hh S.mass (S.forwardDistance j)
    (S.forwardDistance_pos j)
  dsimp only
  unfold AnchoredCircleSource.backwardExterior AnchoredCircleSource.forwardExterior at *
  rw [hLA, hLB, hRA, hRB]
  constructor <;> nlinarith

end ACS12.GammaMeasure

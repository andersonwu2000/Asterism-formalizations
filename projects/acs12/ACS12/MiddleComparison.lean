import ACS12.MiddleScalar

/-! Same-law middle comparisons from the complete original scalar. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter

noncomputable def middleBase (p L u : ℝ) : ℝ :=
  u * (imagePotential p L 1 + middleA u * imageSlope p L 1 - unitSlopeTotal p L) -
    (1 - u) * imageSelf p L

theorem middleBase_neg {p L u : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2) (hL : 0 < L)
    (hu : 0 < u) (hu₁ : u ≤ 1) : middleBase p L u < 0 := by
  unfold middleBase
  have h := unitSlopeTotal_gt_baseline hp hp₂ hL (middleA_le u)
  exact sub_neg_of_lt (lt_of_lt_of_le (mul_neg_of_pos_of_neg hu (sub_neg.mpr h))
    (mul_nonneg (sub_nonneg.mpr hu₁) (imageSelf_pos hp hL).le))

private theorem original_scalar_after_b {n : ℕ} {p : ℝ} (F : Configuration n p)
    (hn : 2 ≤ n) (hp : 0 < p) (hp₂ : p ≤ 2)
    (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi)) {j k : Fin n}
    (hj : C.source.IsNext C.source.neighbor j) (hk : C.source.IsNext j k)
    (hu₁ : C.source.forwardDistance C.source.neighbor j ≤ 1) :
    let S := C.source
    let L := S.period
    let u := S.forwardDistance S.neighbor j
    let v := S.forwardDistance j k
    let a := middleA u
    let z := middleZ u
    0 ≤ middleBase p L u + S.mass j * rightTest p L a z u +
      samplingHead (rightClip p L a z) (u + v) (S.mass k) := by
  let S := C.source
  let L := S.period
  let u := S.forwardDistance S.neighbor j
  let v := S.forwardDistance j k
  let a := middleA u
  let z := middleZ u
  let b := S.mass S.neighbor
  have hL : 0 < L := S.period_pos
  have hu : 0 < u := S.forwardDistance_pos _ _
  have ha : 0 < a := middleA_pos hu hu₁
  have hb : b ≤ u := (S.forwardDistance_caps C.circular_caps (fun he => (lt_irrefl _) (he ▸ hj.1))).1
  have hK := imagePotential_pos hp hL zero_lt_one
  have hU : 0 ≤ imageSlope p L 1 := by
    unfold imageSlope
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_nonneg (mul_nonneg (imageDensity_pos hp hL hs).le hs.le) (Real.exp_pos _).le
  have hS := imageSelf_pos hp hL
  have hMono := mul_le_mul_of_nonneg_right hb (show
    0 ≤ imagePotential p L 1 + a * imageSlope p L 1 + imageSelf p L from
      add_nonneg (add_nonneg hK.le (mul_nonneg ha.le hU)) hS.le)
  have h := F.clipped_scalar_necessary hn hp hp₂ C hj hk hu₁
  change 0 ≤ b * (imagePotential p L 1 + a * imageSlope p L 1) - u * unitSlopeTotal p L +
    (b - 1) * imageSelf p L + S.mass j * rightTest p L a z u +
    samplingHead (rightClip p L a z) (u + v) (S.mass k) at h
  change 0 ≤ middleBase p L u + S.mass j * rightTest p L a z u +
    samplingHead (rightClip p L a z) (u + v) (S.mass k)
  change 0 ≤ u * (imagePotential p L 1 + a * imageSlope p L 1 - unitSlopeTotal p L) -
    (1 - u) * imageSelf p L + S.mass j * rightTest p L a z u +
    samplingHead (rightClip p L a z) (u + v) (S.mass k)
  nlinarith only [h, hMono]

theorem _root_.ACS12.Configuration.rightTest_active {n : ℕ} {p : ℝ} (F : Configuration n p)
    (hn : 2 ≤ n) (hp : 0 < p) (hp₂ : p ≤ 2)
    (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi)) {j k : Fin n}
    (hj : C.source.IsNext C.source.neighbor j) (hk : C.source.IsNext j k)
    (hu₁ : C.source.forwardDistance C.source.neighbor j ≤ 1) :
    let S := C.source
    let u := S.forwardDistance S.neighbor j
    0 < rightTest p S.period (middleA u) (middleZ u) u := by
  let S := C.source
  let L := S.period
  let u := S.forwardDistance S.neighbor j
  let v := S.forwardDistance j k
  let a := middleA u
  let z := middleZ u
  let G := rightTest p L a z
  let J := rightClip p L a z
  change 0 < G u
  by_contra! hG
  have hL : 0 < L := S.period_pos
  have hu : 0 < u := S.forwardDistance_pos _ _
  have hv : 0 < v := S.forwardDistance_pos _ _
  have hJ : J u = 0 := max_eq_left hG
  have ha : a ≤ 1 / 2 := (middleA_le u).trans (by norm_num)
  have hA := rightClip_antitone (z := z) hp hL ha
  have hQ (t : ℝ) (ht : u ≤ t) : J t = 0 :=
    le_antisymm ((hA hu (hu.trans_le ht) ht).trans hJ.le) (le_max_left _ _)
  have hTail : samplingHead J (u + v) (S.mass k) = 0 := by
    unfold samplingHead
    have hTerm (i : ℕ) : J (u + v + i * S.mass k) = 0 := by
      apply hQ
      have hm := mul_nonneg (Nat.cast_nonneg i) (S.mass_pos k).le
      linarith
    simp only [hTerm, tsum_zero, mul_zero]
  have h := original_scalar_after_b F hn hp hp₂ C hj hk hu₁
  change 0 ≤ middleBase p L u + S.mass j * G u + samplingHead J (u + v) (S.mass k) at h
  rw [hTail, add_zero] at h
  have hNeg := add_neg_of_neg_of_nonpos (middleBase_neg hp hp₂ hL hu hu₁)
    (mul_nonpos_of_nonneg_of_nonpos (S.mass_pos j).le hG)
  exact hNeg.not_ge h

/-- G6 for the entire original outer geometry, at the actual law. -/
theorem _root_.ACS12.Configuration.outer_scalar_necessary {n : ℕ} {p : ℝ} (F : Configuration n p)
    (hn : 2 ≤ n) (hp : 0 < p) (hp₂ : p ≤ 2)
    (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi)) {j k : Fin n}
    (hj : C.source.IsNext C.source.neighbor j) (hk : C.source.IsNext j k)
    (hu₁ : C.source.forwardDistance C.source.neighbor j ≤ 1)
    (hOuter : C.source.forwardDistance C.source.neighbor j ≤ C.source.forwardDistance j k) :
    let S := C.source
    let L := S.period
    let u := S.forwardDistance S.neighbor j
    let a := middleA u
    let z := middleZ u
    0 ≤ middleBase p L u + outerMass p L u * rightTest p L a z u +
      samplingTail (rightClip p L a z) u u := by
  let S := C.source
  let L := S.period
  let u := S.forwardDistance S.neighbor j
  let v := S.forwardDistance j k
  let a := middleA u
  let z := middleZ u
  let G := rightTest p L a z
  let J := rightClip p L a z
  have hL : 0 < L := S.period_pos
  have hu : 0 < u := S.forwardDistance_pos _ _
  have ha : a ≤ 1 / 2 := (middleA_le u).trans (by norm_num)
  have hm : S.mass j ≤ outerMass p L u := F.mass_le_outerMass hn hp hp₂ C hj hk hOuter
  have hG : 0 < G u := F.rightTest_active hn hp hp₂ C hj hk hu₁
  have hr : S.mass k ≤ v := (S.forwardDistance_caps C.circular_caps (fun he => (lt_irrefl _) (he ▸ hk.1))).2
  have hTail : samplingHead J (u + v) (S.mass k) ≤ samplingTail J u u :=
    clipHead_le_tail hp hp₂ hL ha hu hu (S.mass_pos k) hOuter hr
  have h := original_scalar_after_b F hn hp hp₂ C hj hk hu₁
  change 0 ≤ middleBase p L u + S.mass j * G u + samplingHead J (u + v) (S.mass k) at h
  change 0 ≤ middleBase p L u + outerMass p L u * G u + samplingTail J u u
  exact h.trans (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hm hG.le)) hTail)

/-- The complete original scalar bounded by the mesh at any lawful upper mass. -/
theorem _root_.ACS12.Configuration.mesh_scalar_necessary {n : ℕ} {p : ℝ} (F : Configuration n p)
    (hn : 2 ≤ n) (hp : 0 < p) (hp₂ : p ≤ 2)
    (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi)) {j k : Fin n}
    (hj : C.source.IsNext C.source.neighbor j) (hk : C.source.IsNext j k)
    (hu₁ : C.source.forwardDistance C.source.neighbor j ≤ 1)
    {M : ℝ} (hM : C.source.mass j ≤ M) :
    let S := C.source
    let L := S.period
    let u := S.forwardDistance S.neighbor j
    0 ≤ middleBase p L u + samplingHead (rightClip p L (middleA u) (middleZ u)) u M := by
  let S := C.source
  let L := S.period
  let u := S.forwardDistance S.neighbor j
  let v := S.forwardDistance j k
  let a := middleA u
  let z := middleZ u
  let G := rightTest p L a z
  let J := rightClip p L a z
  let m := S.mass j
  have hL : 0 < L := S.period_pos
  have hu : 0 < u := S.forwardDistance_pos _ _
  have ha : a ≤ 1 / 2 := (middleA_le u).trans (by norm_num)
  have hm : 0 < m := S.mass_pos j
  have hM₀ : 0 < M := hm.trans_le hM
  have hG : 0 < G u := F.rightTest_active hn hp hp₂ C hj hk hu₁
  have hjk : j ≠ k := fun he => (lt_irrefl _) (he ▸ hk.1)
  have hcap := S.forwardDistance_caps C.circular_caps hjk
  have hTail : samplingHead J (u + v) (S.mass k) ≤ samplingTail J u m :=
    clipHead_le_tail hp hp₂ hL ha hu hm (S.mass_pos k) hcap.1 hcap.2
  have h := original_scalar_after_b F hn hp hp₂ C hj hk hu₁
  change 0 ≤ middleBase p L u + m * G u + samplingHead J (u + v) (S.mass k) at h
  change 0 ≤ middleBase p L u + samplingHead J u M
  have hJ : QuadratureData J u := rightClip_quadratureData hp hp₂ hL ha hu
  have hEq : J u = G u := max_eq_right hG.le
  have hHead := hJ.head_mono u le_rfl hm hM₀ hM
  have hPre : 0 ≤ middleBase p L u + samplingHead J u m := by
    rw [samplingHead_split J u m (hJ.summable u m le_rfl hm), hEq]
    linarith only [h, hTail]
  exact hPre.trans (add_le_add le_rfl hHead)

end ACS12.GammaMeasure


import ACS12.RightClip
import ACS12.OuterRoot

/-! The complete positive-part packing after the known signed third atom. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN Set
open scoped BigOperators

private theorem rightTest_samples_summable {p L t : ℝ}
    (hp : 0 < p) (hL : 0 < L) (ht : 0 < t) (a z : ℝ) :
    Summable (fun j : ℕ => rightTest p L a z (t + j * L)) := by
  have hk := imagePotential_samples_summable hp hL ht
  have hk' : Summable (fun j : ℕ => imagePotential p L (t + j * L + 1)) := by
    simpa only [add_right_comm] using imagePotential_samples_summable hp hL (show 0 < t + 1 by positivity)
  have hu := (imageSlope_samples_hasSum hp hL ht).summable
  have hu' : Summable (fun j : ℕ => imageSlope p L (t + j * L + 1)) := by
    simpa only [add_right_comm] using (imageSlope_samples_hasSum hp hL (show 0 < t + 1 by positivity)).summable
  exact (((hu.mul_left z).add (hu'.mul_left a)).sub hk).add hk'

private theorem samplingHead_antitone_base {K : ℝ → ℝ} {d t v r : ℝ}
    (hK : QuadratureData K d) (hA : AntitoneOn K (Ici d)) (hd : d ≤ t) (htv : t ≤ v)
    (hr : 0 < r) :
    samplingHead K v r ≤ samplingHead K t r := by
  unfold samplingHead
  refine mul_le_mul_of_nonneg_left ((hK.summable _ _ (hd.trans htv) hr).tsum_le_tsum ?_
    (hK.summable _ _ hd hr)) hr.le
  intro j
  have hj : 0 ≤ (j : ℝ) * r := by positivity
  exact hA (hd.trans (le_add_of_nonneg_right hj)) (hd.trans (htv.trans (le_add_of_nonneg_right hj)))
    (add_le_add_left htv _)

theorem clipHead_le_tail {p L a z u v m r : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (ha : a ≤ 1 / 2) (hu : 0 < u)
    (hm : 0 < m) (hr : 0 < r) (hmv : m ≤ v) (hrv : r ≤ v) :
    samplingHead (rightClip p L a z) (u + v) r ≤
      samplingTail (rightClip p L a z) u m := by
  let J := rightClip p L a z
  have hJ := rightClip_quadratureData (z := z) hp hp₂ hL ha hu
  have hA : AntitoneOn J (Ici u) := (rightClip_antitone hp hL ha).mono
    (fun _ h => hu.trans_le h)
  rcases le_total r m with hrm | hmr
  · rw [samplingTail_eq_shift]
    exact (samplingHead_antitone_base hJ hA (le_add_of_nonneg_right hm.le)
      (add_le_add_right hmv u) hr).trans (hJ.head_mono _ (le_add_of_nonneg_right hm.le) hr hm hrm)
  · refine (samplingHead_antitone_base hJ hA (le_add_of_nonneg_right hr.le)
      (add_le_add_right hrv u) hr).trans ?_
    rw [← samplingTail_eq_shift]
    exact hJ.tail_anti u le_rfl hm hr hmr

/-- The full original right side, retaining the sign of the third atom. -/
theorem _root_.ACS12.Configuration.rightExterior_le_clipped {n : ℕ} {p : ℝ}
    (F : Configuration n p) (hn : 2 ≤ n) (hp : 0 < p) (hp₂ : p ≤ 2)
    (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi)) {j k : Fin n}
    (hj : C.source.IsNext C.source.neighbor j) (hk : C.source.IsNext j k)
    (a z : ℝ) (ha : a ≤ 1 / 2) :
    let S := C.source
    let L := S.period
    let u := S.forwardDistance S.neighbor j
    let v := S.forwardDistance j k
    S.forwardExterior (rightTest p L a z) S.neighbor ≤
      S.mass j * rightTest p L a z u + samplingHead (rightClip p L a z) (u + v) (S.mass k) := by
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  let S := C.source
  let L := S.period
  let u := S.forwardDistance S.neighbor j
  let v := S.forwardDistance j k
  let G := rightTest p L a z
  let J := rightClip p L a z
  have hL : 0 < L := S.period_pos
  have hu : 0 < u := S.forwardDistance_pos _ _
  have hv : 0 < v := S.forwardDistance_pos _ _
  have hJ := rightClip_quadratureData (z := z) hp hp₂ hL ha hu
  have hShift := shift_quadratureData hJ hv
  have hCmp : S.forwardExterior (fun t => G (t + u)) j ≤
      S.forwardExterior (fun t => J (t + u)) j := by
    unfold AnchoredCircleSource.forwardExterior
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (S.mass_pos i).le
    unfold imageTail
    have hD : 0 < S.forwardDistance j i + u := add_pos (S.forwardDistance_pos _ _) hu
    have hG : Summable (fun t : ℕ => G (S.forwardDistance j i + t * L + u)) := by
      simpa only [add_right_comm] using rightTest_samples_summable hp hL hD a z
    have hC : Summable (fun t : ℕ => J (S.forwardDistance j i + t * L + u)) := by
      simpa only [add_right_comm] using hJ.summable (S.forwardDistance j i + u) L
        (le_add_of_nonneg_left (S.forwardDistance_pos _ _).le) hL
    exact hG.tsum_le_tsum (fun _ => le_max_right _ _) hC
  have hPack := S.forwardExterior_le_head C.circular_caps hv hShift j k (hk.forward_le S) le_rfl
    (S.mass_pos k) le_rfl
  have hShiftEq : samplingHead (fun t => J (t + u)) v (S.mass k) =
      samplingHead J (u + v) (S.mass k) := by
    unfold samplingHead
    exact congrArg (S.mass k * ·) (tsum_congr fun q => congrArg J (by ring))
  rw [hShiftEq] at hPack
  dsimp only
  change S.forwardExterior G S.neighbor ≤ S.mass j * G u + _
  rw [S.forwardExterior_edge G hj.1 hj.2 (rightTest_samples_summable hp hL hu a z)]
  exact add_le_add_right (hCmp.trans hPack) _

end ACS12.GammaMeasure


import ACS12.GammaEdgeBalances
import ACS12.ChartPackedArc
import ACS12.ChartNext

/-! The original adjacent and fourth-edge source necessities before
moving roots, clipping, and finite value estimates. -/

namespace ACS12

open CenteredCircle.AllN Set
open GammaMeasure
open scoped BigOperators

theorem shift_quadratureData {K : ℝ → ℝ} {u d : ℝ} (hK : QuadratureData K u)
    (hd : 0 < d) : QuadratureData (fun t => K (t + u)) d := by
  have he (t s : ℝ) : samplingHead (fun t => K (t + u)) t s = samplingHead K (t + u) s := by
    unfold samplingHead
    exact congrArg (s * ·) (tsum_congr fun j => congrArg K (by ring))
  have ht (t s : ℝ) : samplingTail (fun t => K (t + u)) t s = samplingTail K (t + u) s := by
    unfold samplingTail
    exact congrArg (s * ·) (tsum_congr fun j => congrArg K (by ring))
  refine ⟨fun x hx => hK.nonneg _ (by linarith), ?_, ?_, ?_, ?_⟩
  · intro x s hx hs
    simpa only [add_right_comm] using hK.summable (x + u) s (by linarith) hs
  · intro x hx v hv w hw hvw
    rw [he, he]
    exact hK.head_mono (x + u) (by linarith) hv hw hvw
  · intro x hx v hv w hw hvw
    rw [ht, ht]
    exact hK.tail_anti (x + u) (by linarith) hv hw hvw
  · intro v hv w hw hvw
    rw [ht, ht, zero_add]
    exact hK.tail_anti u le_rfl (hd.trans_le hv) (hd.trans_le hw) hvw

private theorem backwardNeighbor_le_unit {ι : Type*} [DecidableEq ι] [Fintype ι] [Nontrivial ι]
    (S : AnchoredCircleSource ι) (hcaps : S.HasCircularMassCaps) {K : ℝ → ℝ}
    (hK : QuadratureData K 1) :
    S.backwardExterior K S.neighbor ≤ samplingTail K 0 1 := by
  have hNext := S.root_neighbor_next
  have hOne : S.forwardDistance S.root S.neighbor = 1 := by
    rw [S.forwardDistance_eq_sub hNext.1, S.coordinate_neighbor, S.coordinate_root, sub_zero]
  rw [samplingTail_eq_shift, zero_add]
  have h := S.backwardExterior_le_head hcaps (s := 1) (by norm_num) hK S.neighbor S.root
    (hNext.backward_le S) hOne.ge (by norm_num) (by rw [S.mass_root])
  simpa only [hOne] using h

/-- P1510 AB78 in its complete geometric sampling form. -/
theorem Configuration.adjacent_source_necessary {n : ℕ} {p : ℝ}
    (F : Configuration n p) (hn : 2 ≤ n) (hp : 0 < p) (hp₂ : p ≤ 2)
    (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi)) {j k : Fin n}
    (hj : C.source.IsNext C.source.neighbor j) (hk : C.source.IsNext j k) :
    let S := C.source
    let L := S.period
    let u := S.forwardDistance S.neighbor j
    let v := S.forwardDistance j k
    let b := S.mass S.neighbor
    let m := S.mass j
    let r := S.mass k
    let D := imagePotential p L u + imageSelf p L
    0 ≤ samplingTail (peanoKernel p L u .b) 0 1 + b * D -
      m * (u * imageSlope p L u + D) + samplingHead (peanoKernel p L u .a) v r := by
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  let S := C.source
  let L := S.period
  let u := S.forwardDistance S.neighbor j
  let v := S.forwardDistance j k
  have hu : 0 < u := S.forwardDistance_pos _ _
  have hv : 0 < v := S.forwardDistance_pos _ _
  have hL : 0 < L := S.period_pos
  have hLeft := backwardNeighbor_le_unit S C.circular_caps
    (peanoKernel_quadratureData hp hp₂ hL hu (by norm_num : 0 < (1 : ℝ)) .b)
  have hRight := S.forwardExterior_le_head C.circular_caps hv
    (peanoKernel_quadratureData hp hp₂ hL hu hv .a) j k (hk.forward_le S)
    le_rfl (S.mass_pos k) le_rfl
  have hRow := (F.consecutive_image_balances hp C hj.1 hj.2).2
  dsimp only at hRow ⊢
  linarith

/-- P1510 AB79 in its complete geometric sampling form. -/
theorem Configuration.fourth_source_necessary {n : ℕ} {p : ℝ}
    (F : Configuration n p) (hn : 2 ≤ n) (hp : 0 < p) (hp₂ : p ≤ 2)
    (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi)) {j k : Fin n}
    (hj : C.source.IsNext C.source.neighbor j) (hk : C.source.IsNext j k) :
    let S := C.source
    let L := S.period
    let u := S.forwardDistance S.neighbor j
    let v := S.forwardDistance j k
    let b := S.mass S.neighbor
    let m := S.mass j
    let r := S.mass k
    let A := peanoKernel p L v .a
    let B := peanoKernel p L v .b
    let D := imagePotential p L v + imageSelf p L
    0 ≤ b * B u + samplingTail (fun x => B (x + u)) 0 1 +
      samplingTail A 0 r - v * r * imageSlope p L v + (m - r) * D := by
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  let S := C.source
  let L := S.period
  let u := S.forwardDistance S.neighbor j
  let v := S.forwardDistance j k
  let A := peanoKernel p L v .a
  let B := peanoKernel p L v .b
  have hu : 0 < u := S.forwardDistance_pos _ _
  have hv : 0 < v := S.forwardDistance_pos _ _
  have hL : 0 < L := S.period_pos
  have hB := peanoKernel_quadratureData hp hp₂ hL hv hu .b
  have hLeft := backwardNeighbor_le_unit S C.circular_caps (shift_quadratureData hB zero_lt_one)
  have hLeftEq := S.backwardExterior_edge B hj.1 hj.2 (hB.summable u L le_rfl hL)
  have hRight := S.forwardExterior_le_tail C.circular_caps k
    (peanoKernel_quadratureData hp hp₂ hL hv (S.mass_pos k) .a)
  have hRow := (F.consecutive_image_balances hp C hk.1 hk.2).2
  change S.backwardExterior B j + S.forwardExterior A k = _ at hRow
  rw [hLeftEq] at hRow
  dsimp only
  nlinarith

end ACS12

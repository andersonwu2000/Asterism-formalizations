import ACS12.PressurePairLaw

/-! The original flat tilt and the strict row-corrected pair factor. -/
namespace ACS12.Pressure

open Set
open NativeCells (analyticRow)

theorem massTotal_gt_mass {n : ℕ} (hn : 2 ≤ n) {m : Fin n → ℝ} (hm : ∀ i, 0 < m i)
    (i : Fin n) : m i < massTotal m := by
  have hNon : (Finset.univ.erase i : Finset (Fin n)).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem (Finset.mem_univ i),Finset.card_univ,Fintype.card_fin]
    omega
  have h := Finset.sum_pos (s := Finset.univ.erase i) (fun j _ => hm j) hNon
  rwa [Finset.sum_erase_eq_sub (Finset.mem_univ i),sub_pos] at h

theorem massGeometricMean_lt_total {n : ℕ} (hn : 2 ≤ n) {m : Fin n → ℝ} (hm : ∀ i, 0 < m i) :
    massGeometricMean m < massTotal m := by
  have hM := massTotal_pos (by omega) hm
  have h := Finset.sum_lt_sum_of_nonempty (s := Finset.univ) ⟨⟨0,by omega⟩,Finset.mem_univ _⟩
    (fun i _ => mul_lt_mul_of_pos_left (Real.log_lt_log (hm i) (massTotal_gt_mass hn hm i))
      (div_pos (hm i) hM))
  rw [← Finset.sum_mul] at h
  change (∑ i, massWeight m i * Real.log (m i)) < (∑ i, massWeight m i) * Real.log (massTotal m) at h
  rw [massWeight_sum_one (by omega) hm,one_mul] at h
  exact (Real.exp_lt_exp.mpr h).trans_eq (Real.exp_log hM)

noncomputable def pairFlatWeight {n : ℕ} {p : ℝ} (F : Configuration n p) (i j : Fin n) : ℝ :=
  let X := centeredLogMass (sortedPressureMass F)
  let c := (p - 1) / (2 * (p + 1))
  originalPairLaw F i j * Real.exp (-c * (X i + X j))

noncomputable def pairFlatTotal {n : ℕ} {p : ℝ} (F : Configuration n p) : ℝ :=
  ∑ i, ∑ j, pairFlatWeight F i j

theorem pairFlatTotal_ge_one {n : ℕ} {p : ℝ} (hp : 0 < p) (hn : 2 ≤ n) (F : Configuration n p) :
    1 ≤ pairFlatTotal F := by
  let m := sortedPressureMass F
  let X := centeredLogMass m
  let c := (p - 1) / (2 * (p + 1))
  let w := originalPairLaw F
  have hm (i : Fin n) : 0 < m i := F.mass_pos _
  obtain ⟨hw,hL,hR⟩ := originalPairLaw_marginals hp hn F
  change ∀ i, ∑ j, w i j = massWeight m i at hL
  change ∀ j, ∑ i, w i j = massWeight m j at hR
  have hC : (∑ i, ∑ j, w i j * (X i + X j)) = 0 := by
    simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hL]
    rw [Finset.sum_comm (f := fun i j => w i j * X j)]
    simp only [← Finset.sum_mul,hR,X,centeredLogMass_mean_zero (show 0 < n by omega) hm,add_zero]
  have hW : (∑ i, ∑ j, w i j) = 1 := by
    rw [Finset.sum_congr rfl (fun i _ => hL i)]
    exact massWeight_sum_one (by omega) hm
  have hT (i j : Fin n) : w i j * (1 + (-c) * (X i + X j)) ≤ pairFlatWeight F i j := by
    change w i j * (1 + (-c) * (X i + X j)) ≤ w i j * Real.exp ((-c) * (X i + X j))
    simpa only [add_comm] using mul_le_mul_of_nonneg_left (Real.add_one_le_exp ((-c) * (X i + X j))) (hw i j)
  have h := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) fun j _ => hT i j
  have hId (i j : Fin n) : w i j * (1 + -c * (X i + X j)) =
      w i j + (-c) * (w i j * (X i + X j)) := by ring
  simp only [hId,Finset.sum_add_distrib,← Finset.mul_sum,hW,hC,mul_zero,add_zero] at h
  exact h

noncomputable def pressureRowOrigin {n : ℕ} {p : ℝ} (F : Configuration n p) : ℝ :=
  let m := sortedPressureMass F
  Real.log (massTotal m / massGeometricMean m)

noncomputable def pairRowLog {n : ℕ} {p : ℝ} (F : Configuration n p) (i j : Fin n) : ℝ :=
  let s₀ := pressureRowOrigin F
  let X := centeredLogMass (sortedPressureMass F)
  let φ (s : ℝ) := Real.log (pressureLogCountRow p s)
  (1 / (p + 1)) * (φ s₀ - (φ (s₀ + X i) + φ (s₀ + X j)) / 2)

noncomputable def pairRowFactor {n : ℕ} {p : ℝ} (F : Configuration n p) : ℝ :=
  (∑ i, ∑ j, pairFlatWeight F i j * Real.exp (pairRowLog F i j)) / pairFlatTotal F

theorem pressureRowOrigin_add {n : ℕ} {p : ℝ} (F : Configuration n p) (hn : 2 ≤ n) (i : Fin n) :
    pressureRowOrigin F + centeredLogMass (sortedPressureMass F) i =
      Real.log (massTotal (sortedPressureMass F) / sortedPressureMass F i) := by
  have hM : 0 < massTotal (sortedPressureMass F) := massTotal_pos (by omega) (fun i => F.mass_pos _)
  have hg : 0 < massGeometricMean (sortedPressureMass F) := Real.exp_pos _
  have hm : 0 < sortedPressureMass F i := F.mass_pos _
  unfold pressureRowOrigin centeredLogMass
  rw [Real.log_div hM.ne' hg.ne',Real.log_div hg.ne' hm.ne',Real.log_div hM.ne' hm.ne']
  ring

theorem originalRow_surplus_pos {n : ℕ} {p : ℝ} (hp : 1 < p) (hp₂ : p ≤ 2) (hn : 2 ≤ n)
    (F : Configuration n p) (hWord : ∃ i j, sortedPressureMass F i ≠ sortedPressureMass F j) :
    0 < (∑ i, ∑ j, pairFlatWeight F i j * pairRowLog F i j) / pairFlatTotal F := by
  let m := sortedPressureMass F
  have hm (i : Fin n) : 0 < m i := F.mass_pos _
  have hs₀ : 0 < pressureRowOrigin F := Real.log_pos
    ((one_lt_div (Real.exp_pos _)).mpr (massGeometricMean_lt_total hn hm))
  have hs (i : Fin n) : 0 < pressureRowOrigin F + centeredLogMass m i := by
    rw [pressureRowOrigin_add F hn i]
    exact Real.log_pos ((one_lt_div (hm i)).mpr (massTotal_gt_mass hn hm i))
  obtain ⟨hπ,hL,hR⟩ := originalPairLaw_marginals (zero_lt_one.trans hp) hn F
  exact pressureRow_surplus_pos hp hp₂ (by omega) hm hWord hπ hL hR hs₀ hs

theorem pairRowFactor_gt_one {n : ℕ} {p : ℝ} (hp : 1 < p) (hp₂ : p ≤ 2) (hn : 2 ≤ n)
    (F : Configuration n p) (hWord : ∃ i j, sortedPressureMass F i ≠ sortedPressureMass F j) :
    1 < pairRowFactor F := by
  have hπ := (originalPairLaw_marginals (zero_lt_one.trans hp) hn F).1
  have hQ := zero_lt_one.trans_le (pairFlatTotal_ge_one (zero_lt_one.trans hp) hn F)
  have hTilt (i j : Fin n) : 0 ≤ pairFlatWeight F i j := mul_nonneg (hπ i j) (Real.exp_pos _).le
  have hT (i j : Fin n) : pairFlatWeight F i j + pairFlatWeight F i j * pairRowLog F i j ≤
      pairFlatWeight F i j * Real.exp (pairRowLog F i j) := by
    simpa only [mul_add,mul_one,add_comm] using
      mul_le_mul_of_nonneg_left (Real.add_one_le_exp (pairRowLog F i j)) (hTilt i j)
  have h := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) fun j _ => hT i j
  simp only [Finset.sum_add_distrib] at h
  have hPos := (div_pos_iff_of_pos_right hQ).mp (originalRow_surplus_pos hp hp₂ hn F hWord)
  unfold pairRowFactor
  apply (lt_div_iff₀ hQ).mpr
  rw [one_mul]
  exact (lt_add_of_pos_right (pairFlatTotal F) hPos).trans_le h

end ACS12.Pressure


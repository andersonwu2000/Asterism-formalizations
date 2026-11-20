import ACS12.PressurePathMass
import ACS12.NativeCellAnalytic
import ACS12.PressureMoments

/-! Exact original midpoint arc lengths in the periodic mass-cell trial. -/
namespace ACS12.Pressure

open CenteredCircle.AllN
open NativeCells (massCells center)

def forwardPathLength {n : ℕ} (i j : Fin n) : ℕ :=
  if i < j then j.val - i.val else n + j.val - i.val

theorem forwardPathLength_bounds {n : ℕ} {i j : Fin n} (h : j ≠ i) :
    0 < forwardPathLength i j ∧ forwardPathLength i j < n := by
  have hij : i.val ≠ j.val := fun h' => h (Fin.ext h'.symm)
  unfold forwardPathLength
  split_ifs with h' <;> simp only [Fin.lt_def] at h' <;> omega

noncomputable def periodicPathMass {n : ℕ} [NeZero n] (m : Fin n → ℝ) (k : ℕ) : ℝ :=
  m ⟨k % n,Nat.mod_lt k (NeZero.pos n)⟩

private theorem periodicPathMass_add_period {n : ℕ} [NeZero n] (m : Fin n → ℝ) (k : ℕ) :
    periodicPathMass m (n + k) = periodicPathMass m k := by
  unfold periodicPathMass
  congr 1
  apply Fin.ext
  simp only [Nat.add_mod_left]

theorem periodicPathMass_in_range {n : ℕ} [NeZero n] (m : Fin n → ℝ) {k : ℕ} (hk : k < n) :
    periodicPathMass m k = m ⟨k,hk⟩ := by
  unfold periodicPathMass
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt hk)

private noncomputable def periodicMassEdges {n : ℕ} [NeZero n] (m : Fin n → ℝ) (j : ℕ) : ℝ :=
  (2 * Real.pi / massTotal m) * ∑ k ∈ Finset.range j, periodicPathMass m k

private theorem periodicMassEdges_eq {n : ℕ} [NeZero n] (m : Fin n → ℝ) {j : ℕ} (hj : j ≤ n) :
    periodicMassEdges m j = massCells (massWeight m) j := by
  unfold periodicMassEdges massCells
  rw [div_mul_eq_mul_div,mul_div_assoc]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < n := (Finset.mem_range.mp hk).trans_le hj
  change periodicPathMass m k / massTotal m =
    if h : k < n then massWeight m ⟨k,h⟩ else 0
  rw [dif_pos hk',periodicPathMass_in_range m hk']
  rfl

private theorem periodicMassEdges_add_period {n : ℕ} [NeZero n] {m : Fin n → ℝ}
    (hm : ∀ i, 0 < m i) (j : ℕ) :
    periodicMassEdges m (n + j) = 2 * Real.pi + periodicMassEdges m j := by
  unfold periodicMassEdges
  rw [Finset.sum_range_add]
  simp only [periodicPathMass_add_period,mul_add]
  congr 1
  change periodicMassEdges m n = 2 * Real.pi
  rw [periodicMassEdges_eq m le_rfl,NativeCells.massCells_end (massWeight_sum_one (NeZero.pos n) hm)]

private theorem periodicMassCenter_eq {n : ℕ} [NeZero n] (m : Fin n → ℝ) (i : Fin n) :
    center (periodicMassEdges m) i.val = center (massCells (massWeight m)) i.val := by
  unfold center
  rw [periodicMassEdges_eq m i.isLt.le,periodicMassEdges_eq m i.isLt]

private theorem periodicMassCenter_add_period {n : ℕ} [NeZero n] {m : Fin n → ℝ}
    (hm : ∀ i, 0 < m i) (j : ℕ) :
    center (periodicMassEdges m) (n + j) = 2 * Real.pi + center (periodicMassEdges m) j := by
  unfold center
  rw [show n + j + 1 = n + (j + 1) by omega,periodicMassEdges_add_period hm j,periodicMassEdges_add_period hm (j + 1)]
  ring

private theorem periodicMassCenter_diff {n : ℕ} [NeZero n] (m : Fin n → ℝ) (i : ℕ)
    {k : ℕ} (hk : 0 < k) :
    center (periodicMassEdges m) (i + k) - center (periodicMassEdges m) i =
      (Real.pi / massTotal m) * pathMassDistance (fun j => periodicPathMass m (i + j)) k := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  unfold center periodicMassEdges pathMassDistance
  simp only [Nat.succ_sub_one,Nat.add_zero]
  rw [Finset.sum_range_succ (n := i + (d + 1)),Finset.sum_range_add,Finset.sum_range_succ',
    Finset.sum_range_succ (n := i)]
  simp only [Nat.succ_eq_add_one]
  ring

theorem midpoint_forwardPath_eq {n : ℕ} [NeZero n] {m : Fin n → ℝ} (hm : ∀ i, 0 < m i)
    {i j : Fin n} (h : j ≠ i) :
    let θ (k : Fin n) := center (massCells (massWeight m)) k.val
    let k := forwardPathLength i j
    (massTotal m / Real.pi) * (2 * halfArc θ i j) =
      pathMassDistance (fun l => periodicPathMass m (i.val + l)) k := by
  dsimp only
  let θ (k : Fin n) := center (massCells (massWeight m)) k.val
  let k := forwardPathLength i j
  have hM := massTotal_pos (NeZero.pos n) hm
  have hk := (forwardPathLength_bounds h).1
  have hC := periodicMassCenter_diff m i.val hk
  have hArc : 2 * halfArc θ i j =
      center (periodicMassEdges m) (i.val + k) - center (periodicMassEdges m) i.val := by
    unfold halfArc
    rw [periodicMassCenter_eq m i]
    by_cases hlt : i < j
    · have hK : i.val + k = j.val := by unfold k forwardPathLength; rw [if_pos hlt]; omega
      rw [hK,periodicMassCenter_eq m j,if_neg (not_lt_of_gt hlt)]
      unfold θ
      ring
    · have hlt' : j < i := lt_of_le_of_ne (le_of_not_gt hlt) h
      have hK : i.val + k = n + j.val := by
        unfold k forwardPathLength
        rw [if_neg hlt]
        have hI := i.isLt
        omega
      rw [hK,periodicMassCenter_add_period hm,periodicMassCenter_eq m j,if_pos hlt']
      unfold θ
      ring
  change (massTotal m / Real.pi) * (2 * halfArc θ i j) =
    pathMassDistance (fun l => periodicPathMass m (i.val + l)) k
  rw [hArc,hC]
  field_simp [Real.pi_ne_zero,hM.ne']
  rfl

theorem forwardPathMass_last {n : ℕ} [NeZero n] (m : Fin n → ℝ) {i j : Fin n} :
    periodicPathMass m (i.val + forwardPathLength i j) = m j := by
  unfold forwardPathLength
  by_cases hlt : i < j
  · rw [if_pos hlt,show i.val + (j.val - i.val) = j.val by omega,periodicPathMass_in_range m j.isLt]
  · rw [if_neg hlt,show i.val + (n + j.val - i.val) = n + j.val by have h := i.isLt; omega,
      periodicPathMass_add_period,periodicPathMass_in_range m j.isLt]

end ACS12.Pressure


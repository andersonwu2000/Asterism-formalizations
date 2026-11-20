import ACS12.NativeCellTrial
import ACS12.NativeRegularRow

/-! Exact normalization of the two prices on the same finite physical mass law. -/
namespace ACS12.NativeCells

open Set
open Pressure (massTotal massTotal_pos massWeight massWeight_sum_one)

noncomputable def meanMass {n : ℕ} (m : Fin n → ℝ) : ℝ := massTotal m / (n : ℝ)

noncomputable def relativeMass {n : ℕ} (m : Fin n → ℝ) (i : Fin n) : ℝ := m i / meanMass m

noncomputable def relativeRootMoment {n : ℕ} (p : ℝ) (m : Fin n → ℝ) : ℝ :=
  (∑ i, relativeMass m i ^ (1 / (p + 1))) / (n : ℝ)

noncomputable def nativeDeficit {n : ℕ} (p : ℝ) (m : Fin n → ℝ) : ℝ :=
  -∑ i, massWeight m i * Real.log (relativeMass m i *
    (analyticRow p ((n : ℝ) / relativeMass m i) / analyticRow p (n : ℝ)))

private theorem meanMass_pos {n : ℕ} (hn : 0 < n) {m : Fin n → ℝ} (hm : ∀ i, 0 < m i) :
    0 < meanMass m := div_pos (massTotal_pos hn hm) (Nat.cast_pos.mpr hn)

theorem relativeMass_sum {n : ℕ} (hn : 0 < n) {m : Fin n → ℝ} (hm : ∀ i, 0 < m i) :
    (∑ i, relativeMass m i) = (n : ℝ) := by
  have hM := massTotal_pos hn hm
  have hN : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  unfold relativeMass meanMass
  rw [← Finset.sum_div, ← massTotal]
  field_simp [hM.ne',hN.ne']

theorem trialCount_eq {n : ℕ} (hn : 0 < n) {m : Fin n → ℝ} (hm : ∀ i, 0 < m i) (i : Fin n) :
    (massWeight m i)⁻¹ = (n : ℝ) / relativeMass m i := by
  have hM := massTotal_pos hn hm
  have hN : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  unfold relativeMass meanMass massWeight
  field_simp [(hm i).ne',hM.ne',hN.ne']

theorem rootRow_normalized {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 0 < p)
    {m : Fin n → ℝ} (hm : ∀ i, 0 < m i) :
    rootRow p m = meanMass m * analyticRow p (n : ℝ) * relativeRootMoment p m ^ (p + 1) := by
  let b : ℝ := 1 / (p + 1)
  have hM := meanMass_pos hn hm
  have hP : 0 < p + 1 := by positivity
  have hPos : 0 ≤ relativeRootMoment p m := by
    unfold relativeRootMoment
    exact div_nonneg (Finset.sum_nonneg fun i _ =>
      Real.rpow_nonneg (div_nonneg (hm i).le hM.le) _) (Nat.cast_nonneg _)
  have hTerm (i : Fin n) : m i ^ b = meanMass m ^ b * relativeMass m i ^ b := by
    unfold relativeMass
    rw [← Real.mul_rpow hM.le (div_nonneg (hm i).le hM.le)]
    congr 1
    field_simp [hM.ne']
  have hRoot : Rank.meanRoot p m = meanMass m ^ b * relativeRootMoment p m := by
    unfold Rank.meanRoot relativeRootMoment
    change (∑ i, m i ^ b) / (n : ℝ) = _
    simp_rw [hTerm]
    rw [← Finset.mul_sum,mul_div_assoc]
  rw [rootRow,hRoot,Real.mul_rpow (Real.rpow_nonneg hM.le _) hPos,← Real.rpow_mul hM.le,
    show b * (p + 1) = 1 by dsimp only [b]; field_simp [hP.ne'],Real.rpow_one]
  ring

theorem logRowMean_normalized {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 0 < p)
    {m : Fin n → ℝ} (hm : ∀ i, 0 < m i) :
    logRowMean p m = meanMass m * analyticRow p (n : ℝ) * Real.exp (-nativeDeficit p m) := by
  have hM := meanMass_pos (by omega) hm
  have hN : (1 : ℝ) < n := Nat.one_lt_cast.mpr (by omega)
  have hA := analyticRow_pos hp hN
  let c := meanMass m * analyticRow p (n : ℝ)
  have hc : 0 < c := mul_pos hM hA
  let X (i : Fin n) := relativeMass m i *
    (analyticRow p ((n : ℝ) / relativeMass m i) / analyticRow p (n : ℝ))
  have hT (i : Fin n) : 1 < (massWeight m i)⁻¹ := by
    unfold massWeight
    rw [inv_div]
    apply (lt_div_iff₀ (hm i)).mpr
    have hi : (Finset.univ.erase i : Finset (Fin n)).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem (Finset.mem_univ i),Finset.card_univ,Fintype.card_fin]
      omega
    have h := Finset.sum_pos (s := Finset.univ.erase i) (fun j _ => hm j) hi
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i),sub_pos] at h
    simpa only [massTotal,one_mul] using h
  have hX (i : Fin n) : 0 < X i := by
    unfold X relativeMass
    have h := analyticRow_pos hp ((trialCount_eq (by omega) hm i).symm ▸
      (hT i) : 1 < (n : ℝ) / relativeMass m i)
    exact mul_pos (div_pos (hm i) hM) (div_pos h hA)
  have hEq (i : Fin n) : m i * analyticRow p (massWeight m i)⁻¹ = c * X i := by
    rw [trialCount_eq (by omega) hm]
    unfold c X relativeMass
    field_simp [hM.ne',hA.ne']
  have hE : (∑ i, massWeight m i * Real.log (m i * analyticRow p (massWeight m i)⁻¹)) =
      Real.log c - nativeDeficit p m := by
    simp_rw [hEq,Real.log_mul hc.ne' (hX _).ne',mul_add]
    rw [Finset.sum_add_distrib,← Finset.sum_mul,massWeight_sum_one (by omega) hm,one_mul]
    unfold nativeDeficit
    ring
  rw [logRowMean,hE,sub_eq_add_neg,Real.exp_add,Real.exp_log hc]

end ACS12.NativeCells

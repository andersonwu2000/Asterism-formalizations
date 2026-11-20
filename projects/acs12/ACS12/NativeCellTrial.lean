import ACS12.NativeCellEnergy
import ACS12.JointEnergy
import ACS12.PressureMoments
import ACS12.Rank

/-! The balanced original trial masses and the two exact inequalities around the native reserve. -/
namespace ACS12.NativeCells

open CenteredCircle.AllN Set
open Pressure (massTotal massTotal_pos massWeight massWeight_sum_one)

private theorem massWeight_lt_one {n : ℕ} (hn : 2 ≤ n) {m : Fin n → ℝ} (hm : ∀ i, 0 < m i)
    (i : Fin n) : massWeight m i < 1 := by
  classical
  have hi : (Finset.univ.erase i : Finset (Fin n)).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem (Finset.mem_univ i),Finset.card_univ,Fintype.card_fin]
    omega
  have h := Finset.sum_pos (s := Finset.univ.erase i) (fun j _ => hm j) hi
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)] at h
  unfold massWeight
  exact (div_lt_one (massTotal_pos (by omega) hm)).mpr (sub_pos.mp h)

noncomputable def logRowMean {n : ℕ} (p : ℝ) (m : Fin n → ℝ) : ℝ :=
  Real.exp (∑ i, massWeight m i * Real.log (m i * analyticRow p (massWeight m i)⁻¹))

theorem logRowMean_pos {n : ℕ} (p : ℝ) (m : Fin n → ℝ) : 0 < logRowMean p m :=
  Real.exp_pos _

theorem logRowMean_permute {n : ℕ} (p : ℝ) (m : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    logRowMean p (m ∘ σ) = logRowMean p m := by
  have hM : massTotal (m ∘ σ) = massTotal m := Equiv.sum_comp σ m
  simp only [logRowMean, massWeight, hM]
  congr 1
  exact Equiv.sum_comp σ (fun i => m i / massTotal m * Real.log (m i * analyticRow p (m i / massTotal m)⁻¹))

/-- The trial is balanced in the original masses and its entire cell row has exactly
the advertised weighted geometric mean. -/
theorem exists_balanced_trial {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 0 < p) {m : Fin n → ℝ}
    (hm : ∀ i, 0 < m i) :
    ∃ v : Fin n → ℝ, (∀ i, 0 < v i) ∧ (∑ i, m i * Real.log (v i / m i)) = 0 ∧
      (∑ i, v i ^ 2 * analyticRow p (massWeight m i)⁻¹) = massTotal m * logRowMean p m := by
  let w := massWeight m
  let S (i : Fin n) := analyticRow p (w i)⁻¹
  let b (i : Fin n) := Real.log (m i * S i)
  let A := ∑ i, w i * b i
  let ell (i : Fin n) := (A - b i) / 2
  let v (i : Fin n) := m i * Real.exp (ell i)
  have hM := massTotal_pos (by omega) hm
  have hw (i : Fin n) : 0 < w i := div_pos (hm i) hM
  have hS (i : Fin n) : 0 < S i :=
    analyticRow_pos hp ((one_lt_inv₀ (hw i)).mpr (massWeight_lt_one hn hm i))
  have hMW (i : Fin n) : massTotal m * w i = m i := by
    unfold w massWeight
    field_simp [hM.ne']
  have hA : (∑ i, m i * b i) = massTotal m * A := by
    dsimp only [A]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← mul_assoc,hMW]
  refine ⟨v, fun i => mul_pos (hm i) (Real.exp_pos _), ?_, ?_⟩
  · have hE (i : Fin n) : Real.log (v i / m i) = ell i := by
      dsimp only [v]
      rw [mul_comm,mul_div_cancel_right₀ _ (hm i).ne',Real.log_exp]
    have hTerm (i : Fin n) : m i * ell i = (m i * A - m i * b i) / 2 := by
      dsimp only [ell]
      ring
    simp only [hE,hTerm,← Finset.sum_div,Finset.sum_sub_distrib,← Finset.sum_mul,hA]
    change (massTotal m * A - massTotal m * A) / 2 = 0
    simp
  · have hV (i : Fin n) : v i ^ 2 * S i = m i * Real.exp A := by
      dsimp only [v,ell]
      rw [mul_pow, ← Real.exp_nat_mul, Nat.cast_ofNat, show (2 : ℝ) * ((A - b i) / 2) = A - b i by ring,
        Real.exp_sub, Real.exp_log (mul_pos (hm i) (hS i))]
      field_simp [(hm i).ne', (hS i).ne']
    change (∑ i, v i ^ 2 * S i) = _
    simp only [hV, ← Finset.sum_mul]
    rfl

theorem commonRow_le_logRowMean {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 0 < p)
    (F : Configuration n p) :
    (2 * F.radius) ^ p * (2 * F.coefficient * F.radius ^ 2) ≤ logRowMean p F.mass := by
  let σ := Tuple.sort F.phase
  let a := F.phase ∘ σ
  let m := F.mass ∘ σ
  let w := massWeight m
  let b (i : Fin n) := center (massCells w) i
  have ha : StrictMono a := (Tuple.monotone_sort F.phase).strictMono_of_injective
    (F.phase_injective.comp σ.injective)
  have ha₀ (i : Fin n) : 0 ≤ a i := (positiveAngle_range _).1
  have haU (i : Fin n) : a i < 2 * Real.pi := (positiveAngle_range _).2
  have hm (i : Fin n) : 0 < m i := F.mass_pos _
  have hM := massTotal_pos (by omega) hm
  have hw (i : Fin n) : 0 < w i := div_pos (hm i) hM
  have hwU (i : Fin n) : w i < 1 := massWeight_lt_one hn hm i
  have hW := massWeight_sum_one (by omega) hm
  have he := massCells_strictMonoOn hw
  have hb (i : Fin n) : b i ∈ Ioo 0 (2 * Real.pi) :=
    center_mem he (massCells_zero w) (massCells_end hW) i
  obtain ⟨v,hv,hBal,hPrice⟩ := exists_balanced_trial hn hp hm
  have hTrial := F.joint_trial_energy_le hp a b v σ ha ha₀ haU (fun i => F.phase_eq (σ i))
    (center_strictMono he) (fun i => (hb i).1.le) (fun i => (hb i).2) hv hBal
  have hCell := cellEnergy_le hw hwU hW hp v
  rw [hPrice] at hCell
  have hInitial : angularEnergy p m a = massTotal m * ((2 * F.radius) ^ p * (2 * F.coefficient * F.radius ^ 2)) := by
    unfold angularEnergy
    have hRow (i : Fin n) : (∑ j, m i * m j * angularCost p (halfArc a i j)) =
        m i * ((2 * F.radius) ^ p * (2 * F.coefficient * F.radius ^ 2)) := by
      simp only [mul_assoc, ← Finset.mul_sum]
      change m i * (∑ j, F.mass (σ j) * angularCost p (halfArc a i j)) = _
      rw [F.weighted_radial_row hp a σ ha ha₀ haU (fun i => F.phase_eq (σ i)) i]
      ring
    simp only [hRow, ← Finset.sum_mul]
    rfl
  rw [hInitial] at hTrial
  rw [← logRowMean_permute p F.mass σ]
  exact (mul_le_mul_iff_right₀ hM).mp (hTrial.trans hCell)

end ACS12.NativeCells

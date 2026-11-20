import ACS12.NativeCellEnergy
import ACS12.Rank

/-! Exact real-count row at the original integer count and its rank normalization. -/
namespace ACS12.NativeCells

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaMeasure (gammaDensity)

private theorem massCells_uniform {n j : ℕ} (hj : j ≤ n) :
    massCells (fun _ : Fin n => (n : ℝ)⁻¹) j = 2 * Real.pi * ((j : ℝ) * (n : ℝ)⁻¹) := by
  let w : Fin n → ℝ := fun _ => (n : ℝ)⁻¹
  have h0 : massCells w 0 = 2 * Real.pi * ((0 : ℝ) * (n : ℝ)⁻¹) := by simp [w]
  induction j with
  | zero => simpa only [Nat.cast_zero] using h0
  | succ j ih =>
    let i : Fin n := ⟨j, by omega⟩
    have h := massCells_halfWidth (w := w) i
    change (massCells w (j + 1) - massCells w j) / 2 = Real.pi * (n : ℝ)⁻¹ at h
    push_cast
    change massCells w (j + 1) = 2 * Real.pi * (((j : ℝ) + 1) * (n : ℝ)⁻¹)
    linarith only [h,ih (by omega)]

theorem analyticRow_integer {n : ℕ} [NeZero n] (hn : 2 ≤ n) {p : ℝ} (hp : 0 < p) :
    analyticRow p (n : ℝ) =
      ∑ j ∈ (Finset.univ : Finset (Fin n)).erase 0, angularCost p (Real.pi * (j : ℝ) / (n : ℝ)) := by
  let w : Fin n → ℝ := fun _ => (n : ℝ)⁻¹
  let edge := massCells w
  let a (i : Fin n) := center edge i
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hw (_ : Fin n) : 0 < (n : ℝ)⁻¹ := inv_pos.mpr hn₀
  have hW : (∑ i, w i) = 1 := by
    simp only [w,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_inv_cancel₀ hn₀.ne']
  have he := massCells_strictMonoOn (w := w) hw
  have h0 := massCells_zero w
  have hN := massCells_end hW
  have hWidth (i : Fin n) : halfWidth edge i = Real.pi * (n : ℝ)⁻¹ := massCells_halfWidth i
  have hRow (s : ℝ) (hs : 0 < s) : rowAtFrequency (n : ℝ)⁻¹ s = ∑ j : Fin n, cellEntry s edge 0 j := by
    have h := cellEntry_row he h0 hN s (0 : Fin n)
    change (∑ j : Fin n, Real.sinh (s * halfWidth edge j) * cellEntry s edge 0 j) =
      Real.sinh (s * (Real.pi - halfWidth edge (0 : Fin n))) at h
    simp only [hWidth,← Finset.mul_sum] at h
    have hPos := Real.sinh_pos_iff.mpr (mul_pos hs (mul_pos Real.pi_pos (inv_pos.mpr hn₀)))
    unfold rowAtFrequency
    exact (eq_div_iff hPos.ne').mpr (by rw [mul_comm]; exact h) |>.symm
  have hArc (j : Fin n) : halfArc a 0 j = Real.pi * (j : ℝ) / (n : ℝ) := by
    have h0Lt : 0 + 1 ≤ n := by omega
    have hz : ¬ j < (0 : Fin n) := fun h => (Nat.not_lt_zero j.val) (by simpa only [Fin.lt_def,Fin.val_zero] using h)
    simp only [halfArc,if_neg hz,add_zero,a,center,edge,Fin.val_zero]
    rw [massCells_uniform j.isLt.le,massCells_uniform j.isLt,
      massCells_uniform (show 0 ≤ n by omega),massCells_uniform h0Lt]
    push_cast
    simp only [div_eq_mul_inv]
    ring
  have hI (j : Fin n) : IntegrableOn (fun s => 2 * gammaDensity p s * cellEntry s edge 0 j) (Ioi 0) :=
    (cellEntry_integral he h0 hN hp 0 j).1
  unfold analyticRow
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s hs => by rw [hRow s hs,Finset.mul_sum]),
    integral_finsetSum _ (fun j _ => hI j)]
  have hVal (j : Fin n) : (∫ s : ℝ in Ioi 0, 2 * gammaDensity p s * cellEntry s edge 0 j) =
      angularCost p (Real.pi * (j : ℝ) / (n : ℝ)) :=
    (cellEntry_integral he h0 hN hp 0 j).2.trans (congrArg (angularCost p) (hArc j))
  simp only [hVal]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ 0)]
  simp [angularCost,Real.zero_rpow hp.ne']

noncomputable def rootRow {n : ℕ} (p : ℝ) (m : Fin n → ℝ) : ℝ :=
  analyticRow p (n : ℝ) * Rank.meanRoot p m ^ (p + 1)

theorem rootRow_le_commonRow {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 0 < p)
    (F : Configuration n p) :
    rootRow p F.mass ≤ (2 * F.radius) ^ p * (2 * F.coefficient * F.radius ^ 2) := by
  letI : NeZero n := ⟨by omega⟩
  have hR : 0 < 2 * F.radius := by have := F.radius_pos; positivity
  have hRp := Real.rpow_pos_of_pos hR p
  have h := mul_le_mul_of_nonneg_left (Rank.referenceRow_le hp.le F) hRp.le
  have hEq : (2 * F.radius) ^ p * Rank.referenceRow p F.radius F.mass = rootRow p F.mass := by
    rw [Rank.referenceRow,rootRow,analyticRow_integer hn hp,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    have hj₀ : 0 < (j : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero fun hz =>
      (Finset.mem_erase.mp hj).1 (Fin.ext (by simpa only [Fin.val_zero] using hz)))
    have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    have hjn : (j : ℝ) < (n : ℝ) := Nat.cast_lt.mpr j.isLt
    have ht : Real.pi * (j : ℝ) / (n : ℝ) ∈ Ioo 0 Real.pi := ⟨by positivity,
      (div_lt_iff₀ hn₀).mpr (mul_lt_mul_of_pos_left hjn Real.pi_pos)⟩
    have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
    rw [angularCost,Real.mul_rpow hR.le hs.le]
    field_simp [hRp.ne',(Real.rpow_pos_of_pos hs p).ne']
  rwa [hEq] at h

end ACS12.NativeCells

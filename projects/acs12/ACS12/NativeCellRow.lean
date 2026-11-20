import ACS12.AngularEnergy

/-! The exact self-subtracted cell inequality on a single positive frequency. -/
namespace ACS12.NativeCells

open Set

noncomputable def center (edge : ℕ → ℝ) (i : ℕ) : ℝ := (edge i + edge (i + 1)) / 2

noncomputable def halfWidth (edge : ℕ → ℝ) (i : ℕ) : ℝ := (edge (i + 1) - edge i) / 2

noncomputable def cellEntry (s : ℝ) (edge : ℕ → ℝ) (i j : ℕ) : ℝ :=
  if i = j then 0 else Real.cosh (s * (Real.pi - |center edge j - center edge i|))

theorem center_strictMono {n : ℕ} {edge : ℕ → ℝ} (he : StrictMonoOn edge (Icc (0 : ℕ) n)) :
    StrictMono (fun i : Fin n => center edge i) := by
  intro i j hij
  have hi := he (show i.val ∈ Icc 0 n from ⟨Nat.zero_le _, i.isLt.le⟩)
    (show i.val + 1 ∈ Icc 0 n from ⟨Nat.zero_le _, i.isLt⟩) (Nat.lt_succ_self _)
  have hj := he (show j.val ∈ Icc 0 n from ⟨Nat.zero_le _, j.isLt.le⟩)
    (show j.val + 1 ∈ Icc 0 n from ⟨Nat.zero_le _, j.isLt⟩) (Nat.lt_succ_self _)
  have h := he.monotoneOn (show i.val + 1 ∈ Icc 0 n from ⟨Nat.zero_le _, i.isLt⟩)
    (show j.val ∈ Icc 0 n from ⟨Nat.zero_le _, j.isLt.le⟩) (show i.val + 1 ≤ j.val from hij)
  unfold center
  linarith only [hi,hj,h]

theorem halfWidth_pos {n : ℕ} {edge : ℕ → ℝ} (he : StrictMonoOn edge (Icc (0 : ℕ) n)) (i : Fin n) :
    0 < halfWidth edge i := by
  have h := he (show i.val ∈ Icc 0 n from ⟨Nat.zero_le _, i.isLt.le⟩)
    (show i.val + 1 ∈ Icc 0 n from ⟨Nat.zero_le _, i.isLt⟩) (Nat.lt_succ_self _)
  exact half_pos (sub_pos.mpr h)

private theorem sinh_cosh_eq (a b : ℝ) :
    Real.sinh b * Real.cosh a = (Real.sinh (a + b) - Real.sinh (a - b)) / 2 := by
  rw [Real.sinh_add, Real.sinh_sub]
  ring

private theorem cellEntry_symm (s : ℝ) (edge : ℕ → ℝ) (i j : ℕ) :
    cellEntry s edge i j = cellEntry s edge j i := by
  by_cases h : i = j
  · subst j
    rfl
  · simp only [cellEntry, h, Ne.symm h, if_false, abs_sub_comm]

private theorem cellEntry_nonneg (s : ℝ) (edge : ℕ → ℝ) (i j : ℕ) : 0 ≤ cellEntry s edge i j := by
  unfold cellEntry
  split_ifs
  · exact le_rfl
  · exact (Real.cosh_pos _).le

theorem cellEntry_row {n : ℕ} {edge : ℕ → ℝ} (he : StrictMonoOn edge (Icc (0 : ℕ) n))
    (h0 : edge 0 = 0) (hN : edge n = 2 * Real.pi) (s : ℝ) (i : Fin n) :
    (∑ j : Fin n, Real.sinh (s * halfWidth edge j) * cellEntry s edge i j) =
      Real.sinh (s * (Real.pi - halfWidth edge i)) := by
  let c := center edge i
  let f (j : ℕ) := Real.sinh (s * halfWidth edge j) * cellEntry s edge i j
  let l (j : ℕ) := Real.sinh (s * (Real.pi - c + edge j))
  let r (j : ℕ) := Real.sinh (s * (Real.pi + c - edge j))
  have hL (j : ℕ) (hj : j < i.val) : f j = (l (j + 1) - l j) / 2 := by
    have hjN := hj.trans i.isLt
    have hC : center edge j < c := center_strictMono he (show (⟨j,hjN⟩ : Fin n) < i from hj)
    have hne : i.val ≠ j := (Nat.ne_of_lt hj).symm
    dsimp only [f,cellEntry]
    rw [if_neg hne, abs_of_neg (sub_neg.mpr hC), sinh_cosh_eq]
    dsimp only [l,c,center,halfWidth]
    have h₁ : s * (Real.pi - -((edge j + edge (j + 1)) / 2 - (edge i + edge (i + 1)) / 2)) +
        s * ((edge (j + 1) - edge j) / 2) =
      s * (Real.pi - (edge i + edge (i + 1)) / 2 + edge (j + 1)) := by ring
    have h₂ : s * (Real.pi - -((edge j + edge (j + 1)) / 2 - (edge i + edge (i + 1)) / 2)) -
        s * ((edge (j + 1) - edge j) / 2) =
      s * (Real.pi - (edge i + edge (i + 1)) / 2 + edge j) := by ring
    rw [h₁,h₂]
  have hR (j : ℕ) (hij : i.val < j) (hj : j < n) : f j = (r j - r (j + 1)) / 2 := by
    have hC : c < center edge j := center_strictMono he (show i < (⟨j,hj⟩ : Fin n) from hij)
    dsimp only [f,cellEntry]
    rw [if_neg (Nat.ne_of_lt hij), abs_of_pos (sub_pos.mpr hC), sinh_cosh_eq]
    dsimp only [r,c,center,halfWidth]
    have h₁ : s * (Real.pi - ((edge j + edge (j + 1)) / 2 - (edge i + edge (i + 1)) / 2)) +
        s * ((edge (j + 1) - edge j) / 2) =
      s * (Real.pi + (edge i + edge (i + 1)) / 2 - edge j) := by ring
    have h₂ : s * (Real.pi - ((edge j + edge (j + 1)) / 2 - (edge i + edge (i + 1)) / 2)) -
        s * ((edge (j + 1) - edge j) / 2) =
      s * (Real.pi + (edge i + edge (i + 1)) / 2 - edge (j + 1)) := by ring
    rw [h₁,h₂]
  have hSelf : f i = 0 := by simp [f,cellEntry]
  let k := n - (i.val + 1)
  have hk : i.val + 1 + k = n := Nat.add_sub_of_le i.isLt
  have hsumL : (∑ j ∈ Finset.range i.val, f j) = (l i.val - l 0) / 2 := by
    rw [← Finset.sum_range_sub l, Finset.sum_div]
    exact Finset.sum_congr rfl (fun j hj => hL j (Finset.mem_range.mp hj))
  have hsumR : (∑ j ∈ Finset.range k, f (i.val + 1 + j)) = (r (i.val + 1) - r n) / 2 := by
    let g (j : ℕ) := r (i.val + 1 + j)
    have h := Finset.sum_range_sub' g k
    dsimp only [g] at h
    rw [add_zero,hk] at h
    rw [← h, Finset.sum_div]
    exact Finset.sum_congr rfl (fun j hj => by
      have hj' := Finset.mem_range.mp hj
      have hjn : i.val + 1 + j < n := by omega
      rw [hR _ (by omega) hjn]
      simp only [Nat.add_assoc])
  change (∑ j : Fin n, f j.val) = _
  rw [Fin.sum_univ_eq_sum_range f]
  conv_lhs => rw [← hk, Finset.sum_range_add]
  rw [Finset.sum_range_succ, hSelf, add_zero, hsumL, hsumR]
  have hA : l i.val = Real.sinh (s * (Real.pi - halfWidth edge i)) := by
    dsimp only [l,c,center,halfWidth]
    congr 1
    ring
  have hB : r (i.val + 1) = Real.sinh (s * (Real.pi - halfWidth edge i)) := by
    dsimp only [r,c,center,halfWidth]
    congr 1
    ring
  have hC : r n = -l 0 := by
    dsimp only [r,l]
    rw [hN,h0,add_zero, show s * (Real.pi + c - 2 * Real.pi) = -(s * (Real.pi - c)) by ring, Real.sinh_neg]
  rw [hA,hB,hC]
  ring

theorem cellEnergy_frequency_square {n : ℕ} {edge : ℕ → ℝ}
    (he : StrictMonoOn edge (Icc (0 : ℕ) n)) (h0 : edge 0 = 0) (hN : edge n = 2 * Real.pi)
    (v : Fin n → ℝ) {s : ℝ} (hs : 0 < s) :
    let h (i : Fin n) := Real.sinh (s * halfWidth edge i)
    let c (i : Fin n) := v i / h i
    (∑ i : Fin n, v i ^ 2 * (Real.sinh (s * (Real.pi - halfWidth edge i)) / h i)) -
      (∑ i : Fin n, ∑ j : Fin n, v i * v j * cellEntry s edge i j) =
        (1 / 2 : ℝ) * ∑ i : Fin n, ∑ j : Fin n,
          (c i - c j) ^ 2 * (h i * h j * cellEntry s edge i j) := by
  dsimp only
  let h (i : Fin n) := Real.sinh (s * halfWidth edge i)
  let c (i : Fin n) := v i / h i
  let F (i j : Fin n) := h i * h j * cellEntry s edge i j
  let S (i : Fin n) := Real.sinh (s * (Real.pi - halfWidth edge i))
  have hh (i : Fin n) : 0 < h i := Real.sinh_pos_iff.mpr (mul_pos hs (NativeCells.halfWidth_pos he i))
  have hc (i : Fin n) : c i * h i = v i := div_mul_cancel₀ _ (hh i).ne'
  have hSym (i j : Fin n) : F i j = F j i := by
    unfold F
    rw [mul_comm (h i)]
    congr 1
    by_cases e : i = j
    · subst j
      rfl
    · have e' : i.val ≠ j.val := fun e' => e (Fin.ext e')
      simp only [cellEntry,e',e'.symm,if_false,abs_sub_comm]
  have hRow (i : Fin n) : (∑ j : Fin n, F i j) = h i * S i := by
    unfold S
    rw [← cellEntry_row he h0 hN s i,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    unfold F h
    ring
  have hDiag : (∑ i : Fin n, ∑ j : Fin n, c i ^ 2 * F i j) =
      ∑ i : Fin n, v i ^ 2 * (S i / h i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.mul_sum,hRow]
    change (v i / h i) ^ 2 * (h i * S i) = _
    field_simp [(hh i).ne']
  have hSwap : (∑ i : Fin n, ∑ j : Fin n, c j ^ 2 * F i j) =
      ∑ i : Fin n, ∑ j : Fin n, c i ^ 2 * F i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hSym j i]
  have hCross : (∑ i : Fin n, ∑ j : Fin n, c i * c j * F i j) =
      ∑ i : Fin n, ∑ j : Fin n, v i * v j * cellEntry s edge i j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [← hc i,← hc j]
    unfold F
    ring
  change (∑ i : Fin n, v i ^ 2 * (S i / h i)) -
    (∑ i : Fin n, ∑ j : Fin n, v i * v j * cellEntry s edge i j) =
      (1 / 2 : ℝ) * ∑ i : Fin n, ∑ j : Fin n, (c i - c j) ^ 2 * F i j
  simp_rw [show ∀ i j : Fin n, (c i - c j) ^ 2 * F i j =
      c i ^ 2 * F i j + c j ^ 2 * F i j - 2 * (c i * c j * F i j) from fun i j => by ring,
    Finset.sum_sub_distrib,Finset.sum_add_distrib]
  have hDouble : (∑ i : Fin n, ∑ j : Fin n, 2 * (c i * c j * F i j)) =
      2 * (∑ i : Fin n, ∑ j : Fin n, v i * v j * cellEntry s edge i j) := by
    simp_rw [← Finset.mul_sum]
    rw [hCross]
  rw [hDouble,hSwap,hDiag]
  ring

theorem cellEnergy_frequency_le {n : ℕ} {edge : ℕ → ℝ}
    (he : StrictMonoOn edge (Icc (0 : ℕ) n)) (h0 : edge 0 = 0) (hN : edge n = 2 * Real.pi)
    (v : Fin n → ℝ) {s : ℝ} (hs : 0 < s) :
    (∑ i : Fin n, ∑ j : Fin n, v i * v j * cellEntry s edge i j) ≤
      ∑ i : Fin n, v i ^ 2 * (Real.sinh (s * (Real.pi - halfWidth edge i)) / Real.sinh (s * halfWidth edge i)) := by
  have hId:=cellEnergy_frequency_square he h0 hN v hs
  have hNonneg : 0≤(1/2:ℝ)*∑ i : Fin n,∑ j : Fin n,
      (v i/Real.sinh (s*halfWidth edge i)-v j/Real.sinh (s*halfWidth edge j))^2*
        (Real.sinh (s*halfWidth edge i)*Real.sinh (s*halfWidth edge j)*cellEntry s edge i j) := by
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg (sq_nonneg _)
    exact mul_nonneg (mul_nonneg
      (Real.sinh_pos_iff.mpr (mul_pos hs (halfWidth_pos he i))).le
      (Real.sinh_pos_iff.mpr (mul_pos hs (halfWidth_pos he j))).le) (cellEntry_nonneg _ _ _ _)
  dsimp only at hId
  linarith only [hId,hNonneg]

end ACS12.NativeCells

import ACS12.PressureCut
import ACS12.BoseShape

/-! Whole-period packing at the original maximum mass. -/
namespace ACS12.Pressure

open Set CenteredCircle.AllN

private theorem periodicDen_mono {s a b : ℝ} (hs : 0 < s) (hab : a ≤ b) :
    periodicDen a s ≤ periodicDen b s := by
  unfold periodicDen
  exact sub_le_sub_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hab (neg_nonpos.mpr hs.le))) _

private theorem packedSample_le {s x y m Q : ℝ} (hs : 0 < s) (hm : 0 < m) (hM : m ≤ Q) (h : m ≤ y - x) :
    m * Real.exp (-s * x) ≤ (Q / periodicDen Q s) * (Real.exp (-s * x) - Real.exp (-s * y)) := by
  have hQ := hm.trans_le hM
  have hDenM := periodicDen_pos hm hs
  have hDenQ := periodicDen_pos hQ hs
  have hF := strictMonoOn_expHeadFactor.monotoneOn (show s * m ∈ Ioi 0 from mul_pos hs hm)
    (show s * Q ∈ Ioi 0 from mul_pos hs hQ) (mul_le_mul_of_nonneg_left hM hs.le)
  have hA : m / periodicDen m s ≤ Q / periodicDen Q s := by
    apply (mul_le_mul_iff_right₀ hs).mp
    simp only [expHeadFactor,periodicDen,← mul_div_assoc,neg_mul] at hF ⊢
    exact hF
  have hB := (div_le_iff₀ hDenM).mp hA
  have hC := mul_le_mul_of_nonneg_left (periodicDen_mono hs h) (div_nonneg hQ.le hDenQ.le)
  have hE : Real.exp (-s * x) - Real.exp (-s * y) = Real.exp (-s * x) * periodicDen (y - x) s := by
    unfold periodicDen
    rw [mul_sub,mul_one,← Real.exp_add]
    congr 2
    ring
  rw [hE]
  have hT := mul_le_mul_of_nonneg_right (hB.trans hC) (Real.exp_pos (-s * x)).le
  nlinarith only [hT]

theorem rayWeight_packed_le {n : ℕ} (hn : 0 < n) {L Q s : ℝ} (hL : 0 < L) (hs : 0 < s)
    (m d : Fin n → ℝ) (hm : ∀ j, 0 < m j) (hM : ∀ j, m j ≤ Q)
    (hd : Function.Injective d) (hd₀ : ∀ j, Q ≤ d j) (hdL : ∀ j, d j ≤ L)
    (hGap : ∀ i j, d i < d j → m i ≤ d j - d i) :
    rayWeight L m d s ≤ Q * (Real.exp (-s * Q) / periodicDen Q s) := by
  let i₀ : Fin n := ⟨0,hn⟩
  let σ := Tuple.sort d
  let t (j : ℕ) := if h : j < n then d (σ ⟨j,h⟩) else d (σ i₀) + L
  have hQ := (hm i₀).trans_le (hM i₀)
  have ht : StrictMono (d ∘ σ) := (Tuple.monotone_sort d).strictMono_of_injective (hd.comp σ.injective)
  have h0 : t 0 = d (σ i₀) := dif_pos hn
  have hN : t n = t 0 + L := by unfold t; rw [dif_neg (lt_irrefl n),dif_pos hn]
  have hStep (j : Fin n) : m (σ j) ≤ t (j.val + 1) - t j.val := by
    unfold t
    rw [dif_pos j.isLt]
    split_ifs with h
    · exact hGap (σ j) (σ ⟨j.val + 1,h⟩) (ht (show j < (⟨j.val + 1,h⟩ : Fin n) from Nat.lt_succ_self _))
    · linarith only [hdL (σ j),hd₀ (σ i₀),hM (σ j)]
  have hBound (j : Fin n) :
      m (σ j) * Real.exp (-s * t j.val) ≤ (Q / periodicDen Q s) *
        (Real.exp (-s * t j.val) - Real.exp (-s * t (j.val + 1))) :=
    packedSample_le hs (hm (σ j)) (hM (σ j)) (hStep j)
  have hS := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hBound j)
  have hLeft : (∑ j : Fin n, m (σ j) * Real.exp (-s * t j.val)) =
      ∑ j : Fin n, m j * Real.exp (-s * d j) := by
    calc
      _ = ∑ j : Fin n, m (σ j) * Real.exp (-s * d (σ j)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [show t j.val = d (σ j) from dif_pos j.isLt]
      _ = _ := Equiv.sum_comp σ (fun j => m j * Real.exp (-s * d j))
  let f (j : ℕ) := Real.exp (-s * t j)
  have hTel : (∑ j : Fin n, (f j.val - f (j.val + 1))) = f 0 - f n := by
    rw [Fin.sum_univ_eq_sum_range (fun j => f j - f (j + 1))]
    exact (Finset.sum_range_sub' f n).trans (by simp)
  rw [hLeft,← Finset.mul_sum,hTel] at hS
  have hE : f 0 - f n = Real.exp (-s * t 0) * periodicDen L s := by
    dsimp only [f]
    rw [hN,mul_add,Real.exp_add,periodicDen]
    ring
  rw [hE] at hS
  have hDen := periodicDen_pos hL hs
  unfold rayWeight
  simp only [← mul_div_assoc,← Finset.sum_div]
  apply (div_le_iff₀ hDen).mpr
  have hT : Real.exp (-s * t 0) ≤ Real.exp (-s * Q) := by
    rw [h0]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hd₀ (σ i₀)) (neg_nonpos.mpr hs.le))
  have hPrice := mul_le_mul_of_nonneg_left hT (div_nonneg hQ.le (periodicDen_pos hQ hs).le)
  have hP := mul_le_mul_of_nonneg_right hPrice hDen.le
  calc
    _ ≤ (Q / periodicDen Q s * Real.exp (-s * t 0)) * periodicDen L s := hS.trans_eq (by ring)
    _ ≤ (Q / periodicDen Q s * Real.exp (-s * Q)) * periodicDen L s := hP
    _ = _ := by ring


theorem maximum_rays_le {n : ℕ} (hn : 2 ≤ n) (S : AnchoredCircleSource (Fin n))
    (hc : S.HasCircularMassCaps) (i : Fin n) (hM : ∀ j, S.mass j ≤ S.mass i) {s : ℝ} (hs : 0 < s) :
    let Q := S.mass i
    let B := Q * (Real.exp (-s * Q) / periodicDen Q s)
    leftRay S i s ≤ B ∧ rightRay S i s ≤ B := by
  let Q := S.mass i
  have hOther : ∃ j : Fin n, j ≠ i := by
    by_contra! h
    have hA : (⟨0,by omega⟩ : Fin n) = i := h _
    have hB : (⟨1,by omega⟩ : Fin n) = i := h _
    have hEq := congrArg Fin.val (hA.trans hB.symm)
    exact Nat.zero_ne_one hEq
  obtain ⟨j,hji⟩ := hOther
  have hQL : Q ≤ S.period :=
    (S.forwardDistance_caps hc hji.symm).1.trans (S.forwardDistance_le_period i j)
  have hF (j : Fin n) : Q ≤ S.forwardDistance i j := by
    by_cases h : j = i
    · simpa only [h,S.forwardDistance_self] using hQL
    · exact (S.forwardDistance_caps hc (Ne.symm h)).1
  have hB (j : Fin n) : Q ≤ S.forwardDistance j i := by
    by_cases h : j = i
    · simpa only [h,S.forwardDistance_self] using hQL
    · exact (S.forwardDistance_caps hc h).2
  have hForward (j k : Fin n) (hjk : S.forwardDistance i j < S.forwardDistance i k) :
      S.mass j ≤ S.forwardDistance i k - S.forwardDistance i j := by
    have hj : j ≠ i := by
      intro h
      subst j
      rw [S.forwardDistance_self] at hjk
      exact not_lt_of_ge (S.forwardDistance_le_period i k) hjk
    by_cases hk : k = i
    · subst k
      rw [S.forwardDistance_self,← S.forwardDistance_flip (Ne.symm hj)]
      exact (S.forwardDistance_caps hc hj).1
    · have h := S.forwardDistance_adjacent_split (Ne.symm hj) (Ne.symm hk) hjk
      have hNe : j ≠ k := fun he => hjk.ne (congrArg (S.forwardDistance i) he)
      have hM := (S.forwardDistance_caps hc hNe).1
      linarith only [hM,h]
  have hBackward (j k : Fin n) (hjk : S.forwardDistance j i < S.forwardDistance k i) :
      S.mass j ≤ S.forwardDistance k i - S.forwardDistance j i := by
    have hj : j ≠ i := by
      intro h
      subst j
      rw [S.forwardDistance_self] at hjk
      exact not_lt_of_ge (S.forwardDistance_le_period k i) hjk
    by_cases hk : k = i
    · subst k
      rw [S.forwardDistance_self,← S.forwardDistance_flip hj]
      exact (S.forwardDistance_caps hc (Ne.symm hj)).2
    · have hJ := S.forwardDistance_flip hj
      have hK := S.forwardDistance_flip hk
      have hOrder : S.forwardDistance i k < S.forwardDistance i j := by linarith only [hJ,hK,hjk]
      have h := S.forwardDistance_adjacent_split (Ne.symm hk) (Ne.symm hj) hOrder
      have hNe : k ≠ j := fun he => hOrder.ne (congrArg (S.forwardDistance i) he)
      have hM := (S.forwardDistance_caps hc hNe).2
      linarith only [hM,h,hJ,hK]
  exact ⟨rayWeight_packed_le (by omega) S.period_pos hs S.mass _ S.mass_pos hM
      (S.backwardDistance_injective i) hB (fun j => S.forwardDistance_le_period j i) hBackward,
    rayWeight_packed_le (by omega) S.period_pos hs S.mass _ S.mass_pos hM
      (S.forwardDistance_injective i) hF (S.forwardDistance_le_period i) hForward⟩

end ACS12.Pressure

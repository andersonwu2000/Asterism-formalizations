import CenteredCircle.KernelQuadratureData
import Mathlib.Data.Finset.Max

/-!
Quadrature for arbitrary finite selected sources. No global enumeration, gap
regularity, or source-density conclusion is included among the assumptions.
-/

namespace CenteredCircle.AllN

open Set Filter
open scoped BigOperators Topology

theorem finite_source_head_bound {ι : Type*} [DecidableEq ι]
    {K : ℝ → ℝ} {d : ℝ} (hK : QuadratureData K d) (t q : ι → ℝ) (S : Finset ι) :
    (∀ i ∈ S, d ≤ t i) → Set.InjOn t S →
    (∀ i ∈ S, ∀ j ∈ S, t i < t j → q i ≤ t j - t i ∧ q j ≤ t j - t i) →
    ∀ i ∈ S, ∀ s, 0 < s → (∀ j ∈ S, t i ≤ t j) → q i ≤ s →
      (∑ j ∈ S, q j * K (t j)) ≤ samplingHead K (t i) s := by
  induction S using Finset.strongInductionOn
  rename_i S ih
  intro hdom hinj hpairs i hi s hs hmin hqi
  have hsplit : (∑ j ∈ S, q j * K (t j)) =
      (∑ j ∈ S.erase i, q j * K (t j)) + q i * K (t i) :=
    (Finset.sum_erase_add _ _ hi).symm
  by_cases he : (S.erase i).Nonempty
  · obtain ⟨j, hj, hjmin⟩ := (S.erase i).exists_min_image t he
    have hjS := Finset.mem_of_mem_erase hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    have htij : t i < t j := lt_of_le_of_ne (hmin j hjS)
      (fun h => hji (hinj hjS hi h.symm))
    have hp := hpairs i hi j hjS htij
    have htail := ih (S.erase i) (Finset.erase_ssubset hi)
      (fun k hk => hdom k (Finset.mem_of_mem_erase hk))
      (hinj.mono (by intro k hk; exact Finset.mem_of_mem_erase hk))
      (fun k hk l hl hkl => hpairs k (Finset.mem_of_mem_erase hk)
        l (Finset.mem_of_mem_erase hl) hkl)
      j hj (t j - t i) (sub_pos.mpr htij) hjmin hp.2
    have hstep := sampling_one_step K (t i) s (t j - t i) hs (sub_pos.mpr htij)
      (hK.summable _ _ (hdom i hi) hs)
      (hK.summable _ _ (hdom i hi) (sub_pos.mpr htij))
      (hK.head_mono _ (hdom i hi)) (hK.tail_anti _ (hdom i hi))
    rw [show t i + (t j - t i) = t j by ring] at hstep
    have hpaid := mul_le_mul_of_nonneg_right (le_min hqi hp.1) (hK.nonneg _ (hdom i hi))
    rw [hsplit]
    linarith
  · have hzero : S.erase i = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    rw [hsplit, hzero, Finset.sum_empty, zero_add,
      samplingHead_split K (t i) s (hK.summable _ _ (hdom i hi) hs)]
    have hpaid := mul_le_mul_of_nonneg_right hqi (hK.nonneg _ (hdom i hi))
    have htail : 0 ≤ samplingTail K (t i) s := by
      rw [samplingTail_eq_shift]
      apply samplingHead_nonneg K (t i + s) s hs.le
      intro j
      apply hK.nonneg
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      nlinarith [hdom i hi]
    linarith

theorem finite_source_quadrature {ι : Type*} [DecidableEq ι]
    {K : ℝ → ℝ} {d : ℝ} (hK : QuadratureData K d) (hd : 0 < d)
    (t q : ι → ℝ) (S : Finset ι)
    (hdom : ∀ i ∈ S, d ≤ t i) (hinj : Set.InjOn t S)
    (hmass : ∀ i ∈ S, q i ≤ t i)
    (hpairs : ∀ i ∈ S, ∀ j ∈ S, t i < t j → q i ≤ t j - t i ∧ q j ≤ t j - t i) :
    (∑ i ∈ S, q i * K (t i)) ≤ samplingTail K 0 d := by
  by_cases he : S.Nonempty
  · obtain ⟨i, hi, himin⟩ := S.exists_min_image t he
    have hhead := finite_source_head_bound hK t q S hdom hinj hpairs i hi
      (t i) (lt_of_lt_of_le hd (hdom i hi)) himin (hmass i hi)
    have hb := hK.boundary_anti (by simp) (hdom i hi) (hdom i hi)
    rw [samplingTail_eq_shift, zero_add] at hb
    exact hhead.trans hb
  · have hz : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    rw [hz, Finset.sum_empty, samplingTail_eq_shift, zero_add]
    apply samplingHead_nonneg K d d hd.le
    intro j
    apply hK.nonneg
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg j) hd.le)

theorem countable_source_quadrature {ι : Type*} [Countable ι]
    {K : ℝ → ℝ} {d : ℝ} (hK : QuadratureData K d) (hd : 0 < d)
    (t q : ι → ℝ) (hdom : ∀ i, d ≤ t i) (hinj : Function.Injective t)
    (hmass : ∀ i, q i ≤ t i)
    (hpairs : ∀ i j, t i < t j → q i ≤ t j - t i ∧ q j ≤ t j - t i)
    (hsum : Summable (fun i => q i * K (t i))) :
    (∑' i, q i * K (t i)) ≤ samplingTail K 0 d := by
  classical
  apply le_of_tendsto hsum.hasSum
  exact Eventually.of_forall (fun S => finite_source_quadrature hK hd t q S
    (fun i _ => hdom i) (hinj.injOn) (fun i _ => hmass i)
    (fun i _ j _ => hpairs i j))

end CenteredCircle.AllN

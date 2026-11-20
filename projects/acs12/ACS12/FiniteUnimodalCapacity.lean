import ACS12.HighUnitPacking
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! The finite-atom form of the original interval-capacity, one-height integral estimate. -/
namespace ACS12.HighCurrent

open Finset Set MeasureTheory

theorem finite_unimodal_capacity {ι : Type*} [DecidableEq ι]
    (t w : ι → ℝ) (S : Finset ι) {a b M : ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b) (hM : 0 ≤ M) (hCont : ContinuousOn f (Icc a b))
    (hPos : ∀ x ∈ Icc a b, 0 ≤ f x) (hPeak : ∀ x ∈ Icc a b, f x ≤ M)
    (hMin : ∀ {x y z : ℝ}, x ∈ Icc a b → z ∈ Icc a b →
      x ≤ y → y ≤ z → min (f x) (f z) ≤ f y)
    (hw : ∀ i ∈ S, 0 ≤ w i ∧ w i ≤ 1)
    (hDom : ∀ i ∈ S, t i ∈ Icc a b)
    (hSep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → w i ≤ |t i - t j|) :
    (∑ i ∈ S, w i * f (t i)) ≤ M + ∫ x in a..b, f x := by
  have hInt {c d : ℝ} (hc : c ∈ Icc a b) (hd : d ∈ Icc a b) :
      IntervalIntegrable f volume c d :=
    (hCont.mono (by
      intro x hx
      rcases mem_uIcc.mp hx with hx | hx
      · exact ⟨hc.1.trans hx.1,hx.2.trans hd.2⟩
      · exact ⟨hd.1.trans hx.1,hx.2.trans hc.2⟩)).intervalIntegrable
  have hNon {c d : ℝ} (hc : c ∈ Icc a b) (hd : d ∈ Icc a b) (hcd : c ≤ d) :
      0 ≤ ∫ x in c..d, f x :=
    intervalIntegral.integral_nonneg hcd (fun x hx => hPos x ⟨hc.1.trans hx.1,hx.2.trans hd.2⟩)
  suffices hAll : ∀ T : Finset ι, T ⊆ S → ∀ c d : ℝ,
      c ∈ Icc a b → d ∈ Icc a b → c ≤ d →
      (∀ i ∈ T, t i ∈ Icc c d) →
      (∑ i ∈ T, w i * f (t i)) ≤ M + ∫ x in c..d, f x by
    exact hAll S Finset.Subset.rfl a b ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab hDom
  intro T
  induction T using Finset.strongInductionOn
  rename_i T ih
  intro hTS c d hc hd hcd hBounds
  by_cases hT : T.Nonempty
  · obtain ⟨i,hi,hiMin⟩ := T.exists_min_image t hT
    obtain ⟨k,hk,hkMax⟩ := T.exists_max_image t hT
    by_cases hTail : (T.erase i).Nonempty
    · by_cases hEnds : f (t i) ≤ f (t k)
      · obtain ⟨j,hj,hjMin⟩ := (T.erase i).exists_min_image t hTail
        have hjT := mem_of_mem_erase hj
        have hji := (mem_erase.mp hj).1
        have hij : t i ≤ t j := hiMin j hjT
        have hPay := hSep i (hTS hi) j (hTS hjT) hji.symm
        rw [abs_of_nonpos (sub_nonpos.mpr hij),neg_sub] at hPay
        have hCell : w i * f (t i) ≤ ∫ x in t i..t j, f x := by
          have hLower := intervalIntegral.integral_mono_on hij (intervalIntegrable_const (c := f (t i)))
            (hInt (hDom i (hTS hi)) (hDom j (hTS hjT))) (fun x hx => by
              have h := hMin (hDom i (hTS hi)) (hDom k (hTS hk)) hx.1
                (hx.2.trans (hkMax j hjT))
              simpa only [min_eq_left hEnds] using h)
          rw [intervalIntegral.integral_const,smul_eq_mul] at hLower
          exact (mul_le_mul_of_nonneg_right hPay (hPos _ (hDom i (hTS hi)))).trans hLower
        have hRest := ih (T.erase i) (erase_ssubset hi)
          (fun z hz => hTS (mem_of_mem_erase hz)) (t j) d
          (hDom j (hTS hjT)) hd (hBounds j hjT).2
          (fun z hz => ⟨hjMin z hz,(hBounds z (mem_of_mem_erase hz)).2⟩)
        have hSplit₁ := intervalIntegral.integral_add_adjacent_intervals
          (hInt hc (hDom i (hTS hi))) (hInt (hDom i (hTS hi)) (hDom j (hTS hjT)))
        have hSplit₂ := intervalIntegral.integral_add_adjacent_intervals
          (hInt hc (hDom j (hTS hjT))) (hInt (hDom j (hTS hjT)) hd)
        have hExtra := hNon hc (hDom i (hTS hi)) (hBounds i hi).1
        rw [← sum_erase_add T (fun z => w z * f (t z)) hi]
        linarith only [hCell,hRest,hSplit₁,hSplit₂,hExtra]
      · have hki : k ≠ i := by intro h; exact hEnds (by rw [h])
        have hErase : (T.erase k).Nonempty := ⟨i,mem_erase.mpr ⟨hki.symm,hi⟩⟩
        obtain ⟨j,hj,hjMax⟩ := (T.erase k).exists_max_image t hErase
        have hjT := mem_of_mem_erase hj
        have hjk := (mem_erase.mp hj).1
        have hjk' : t j ≤ t k := hkMax j hjT
        have hPay := hSep k (hTS hk) j (hTS hjT) hjk.symm
        rw [abs_of_nonneg (sub_nonneg.mpr hjk')] at hPay
        have hCell : w k * f (t k) ≤ ∫ x in t j..t k, f x := by
          have hLower := intervalIntegral.integral_mono_on hjk' (intervalIntegrable_const (c := f (t k)))
            (hInt (hDom j (hTS hjT)) (hDom k (hTS hk))) (fun x hx => by
              have h := hMin (hDom i (hTS hi)) (hDom k (hTS hk))
                ((hiMin j hjT).trans hx.1) hx.2
              simpa only [min_eq_right (le_of_not_ge hEnds)] using h)
          rw [intervalIntegral.integral_const,smul_eq_mul] at hLower
          exact (mul_le_mul_of_nonneg_right hPay (hPos _ (hDom k (hTS hk)))).trans hLower
        have hRest := ih (T.erase k) (erase_ssubset hk)
          (fun z hz => hTS (mem_of_mem_erase hz)) c (t j)
          hc (hDom j (hTS hjT)) (hBounds j hjT).1
          (fun z hz => ⟨(hBounds z (mem_of_mem_erase hz)).1,hjMax z hz⟩)
        have hSplit₁ := intervalIntegral.integral_add_adjacent_intervals
          (hInt hc (hDom j (hTS hjT))) (hInt (hDom j (hTS hjT)) (hDom k (hTS hk)))
        have hSplit₂ := intervalIntegral.integral_add_adjacent_intervals
          (hInt hc (hDom k (hTS hk))) (hInt (hDom k (hTS hk)) hd)
        have hExtra := hNon (hDom k (hTS hk)) hd (hBounds k hk).2
        rw [← sum_erase_add T (fun z => w z * f (t z)) hk]
        linarith only [hCell,hRest,hSplit₁,hSplit₂,hExtra]
    · have hEmpty : T.erase i = ∅ := not_nonempty_iff_eq_empty.mp hTail
      rw [← sum_erase_add T (fun z => w z * f (t z)) hi,hEmpty,sum_empty,zero_add]
      have hOne := mul_le_mul_of_nonneg_right (hw i (hTS hi)).2 (hPos _ (hDom i (hTS hi)))
      have hHeight := hPeak _ (hDom i (hTS hi))
      have hExtra := hNon hc hd hcd
      linarith only [hOne,hHeight,hExtra]
  · have hEmpty : T = ∅ := not_nonempty_iff_eq_empty.mp hT
    rw [hEmpty,sum_empty]
    exact add_nonneg hM (hNon hc hd hcd)

end ACS12.HighCurrent

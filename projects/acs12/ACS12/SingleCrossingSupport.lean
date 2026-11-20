import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen

/-! A single change from concavity to convexity returns the positive endpoint to the whole interval. -/
namespace ACS12
open Set
set_option backward.isDefEq.respectTransparency false

theorem single_crossing_support_positive {q d K : ℝ → ℝ} {a c R x : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hc₁ : c < 1) (hR : 1 ≤ R)
    (hFirst : ∀ u ∈ Ioc 0 R, HasDerivAt q (d u) u)
    (hSecond : ∀ u ∈ Ioc 0 R, HasDerivAt d (K u) u)
    (hLow : ∀ u ∈ Ioc 0 c, K u ≤ 0)
    (hHigh : ∀ u ∈ Ioo c R, 0 < K u)
    (hq₁ : q 1 = 0) (hd₁ : d 1 = 0) (hqa : 0 < q a)
    (hx : x ∈ Icc a R) (hx₁ : x ≠ 1) : 0 < q x := by
  have hcR : c ≤ R := hc₁.le.trans hR
  have hdMono : StrictMonoOn d (Icc c R) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · exact fun u hu => (hSecond u ⟨hc.trans_le hu.1,hu.2⟩).continuousAt.continuousWithinAt
    · intro u hu
      have hu' : u ∈ Ioo c R := by simpa only [interior_Icc] using hu
      rw [(hSecond u ⟨hc.trans hu'.1,hu'.2.le⟩).deriv]
      exact hHigh u ⟨hu'.1,hu'.2⟩
  have hBelow : StrictAntiOn q (Icc c 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    · exact fun u hu => (hFirst u ⟨hc.trans_le hu.1,hu.2.trans hR⟩).continuousAt.continuousWithinAt
    · intro u hu
      have hu' : u ∈ Ioo c 1 := by simpa only [interior_Icc] using hu
      rw [(hFirst u ⟨hc.trans hu'.1,hu'.2.le.trans hR⟩).deriv]
      have h := hdMono ⟨hu'.1.le,hu'.2.le.trans hR⟩ ⟨hc₁.le,hR⟩ hu'.2
      rwa [hd₁] at h
  have hAbove : StrictMonoOn q (Icc 1 R) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · exact fun u hu => (hFirst u ⟨zero_lt_one.trans_le hu.1,hu.2⟩).continuousAt.continuousWithinAt
    · intro u hu
      have hu' : u ∈ Ioo 1 R := by simpa only [interior_Icc] using hu
      rw [(hFirst u ⟨zero_lt_one.trans hu'.1,hu'.2.le⟩).deriv]
      have h := hdMono ⟨hc₁.le,hR⟩ ⟨hc₁.le.trans hu'.1.le,hu'.2.le⟩ hu'.1
      rwa [hd₁] at h
  have hTail (u : ℝ) (hu : u ∈ Icc c R) (hu₁ : u ≠ 1) : 0 < q u := by
    rcases lt_or_gt_of_ne hu₁ with h | h
    · have hq := hBelow ⟨hu.1,h.le⟩ ⟨hc₁.le,le_rfl⟩ h
      rwa [hq₁] at hq
    · have hq := hAbove ⟨le_rfl,hR⟩ ⟨h.le,hu.2⟩ h
      rwa [hq₁] at hq
  by_cases hxc : c ≤ x
  · exact hTail x ⟨hxc,hx.2⟩ hx₁
  have hxc' : x < c := lt_of_not_ge hxc
  have hac : a ≤ c := hx.1.trans hxc'.le
  have hConcave : ConcaveOn ℝ (Icc a c) q := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
      (f' := d) (f'' := K)
    · exact fun u hu => (hFirst u ⟨ha.trans_le hu.1,hu.2.trans hcR⟩).continuousAt.continuousWithinAt
    · intro u hu
      have hu' : u ∈ Icc a c := interior_subset hu
      exact (hFirst u ⟨ha.trans_le hu'.1,hu'.2.trans hcR⟩).hasDerivWithinAt
    · intro u hu
      have hu' : u ∈ Icc a c := interior_subset hu
      exact (hSecond u ⟨ha.trans_le hu'.1,hu'.2.trans hcR⟩).hasDerivWithinAt
    · intro u hu
      have hu' : u ∈ Icc a c := interior_subset hu
      exact hLow u ⟨ha.trans_le hu'.1,hu'.2⟩
  have hMin := hConcave.min_le_of_mem_Icc ⟨le_rfl,hac⟩ ⟨hac,le_rfl⟩ ⟨hx.1,hxc'.le⟩
  exact (lt_min hqa (hTail c ⟨le_rfl,hcR⟩ hc₁.ne)).trans_le hMin

theorem double_crossing_support_positive {q d K : ℝ→ℝ} {a c b R x : ℝ}
    (ha : 0<a) (ha₁ : a≤1) (hc : 0<c) (hc₁ : c<1) (hb : 1<b) (hR : 1≤R)
    (hFirst : ∀ u∈Ioc 0 R,HasDerivAt q (d u) u)
    (hSecond : ∀ u∈Ioc 0 R,HasDerivAt d (K u) u)
    (hLow : ∀ u∈Ioc 0 c,K u≤0)
    (hMiddle : ∀ u∈Ioo c (min R b),0<K u)
    (hHigh : ∀ u∈Ioo b R,K u≤0)
    (hq₁ : q 1=0) (hd₁ : d 1=0) (hqa : 0<q a) (hqR : 0<q R)
    (hx : x∈Icc a R) (hx₁ : x≠1) : 0<q x := by
  have hBound : 1≤min R b:=le_min hR hb.le
  have hInner {y : ℝ} (hy : y∈Icc a (min R b)) (hy₁ : y≠1) : 0<q y := by
    apply single_crossing_support_positive ha hc hc₁ hBound
      (fun u hu=>hFirst u ⟨hu.1,hu.2.trans (min_le_left _ _)⟩)
      (fun u hu=>hSecond u ⟨hu.1,hu.2.trans (min_le_left _ _)⟩)
      hLow hMiddle hq₁ hd₁ hqa hy hy₁
  by_cases hxb : x≤min R b
  · exact hInner ⟨hx.1,hxb⟩ hx₁
  have hbR : b≤R := by
    by_contra! h
    rw [min_eq_left h.le] at hxb
    exact hxb hx.2
  have hxB : b<x := by
    rw [min_eq_right hbR] at hxb
    exact lt_of_not_ge hxb
  have hab : a≤b:=ha₁.trans hb.le
  have hqb : 0<q b:=hInner ⟨hab,by rw [min_eq_right hbR]⟩ hb.ne'
  have hConcave : ConcaveOn ℝ (Icc b R) q := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _) (f':=d) (f'':=K)
    · exact fun u hu=>(hFirst u ⟨zero_lt_one.trans (hb.trans_le hu.1),hu.2⟩).continuousAt.continuousWithinAt
    · intro u hu
      have hu' : u∈Ioo b R:=by simpa only [interior_Icc] using hu
      exact (hFirst u ⟨zero_lt_one.trans (hb.trans hu'.1),hu'.2.le⟩).hasDerivWithinAt
    · intro u hu
      have hu' : u∈Ioo b R:=by simpa only [interior_Icc] using hu
      exact (hSecond u ⟨zero_lt_one.trans (hb.trans hu'.1),hu'.2.le⟩).hasDerivWithinAt
    · intro u hu
      have hu' : u∈Ioo b R:=by simpa only [interior_Icc] using hu
      exact hHigh u hu'
  have hMin:=hConcave.min_le_of_mem_Icc ⟨le_rfl,hbR⟩ ⟨hbR,le_rfl⟩ ⟨hxB.le,hx.2⟩
  exact (lt_min hqb hqR).trans_le hMin

end ACS12

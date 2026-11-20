import CenteredCircle.CircularRecenter
import CenteredCircle.ExteriorGeometry

/-!
Construction of the anchored source and all original circular mass caps from
an arbitrary finite positive circular configuration. Force equations are not
assumed here; they must subsequently be transported through this exact chart.
-/

namespace CenteredCircle.AllN

structure NormalizedCircleChart {ι : Type*} [DecidableEq ι]
    (a m : ι → ℝ) (P : ℝ) where
  scale : ℝ
  scale_pos : 0 < scale
  forward : Bool
  source : AnchoredCircleSource ι
  period_eq : source.period = P / scale
  mass_eq : ∀ i, source.mass i = m i / m source.root
  coordinate_eq : ∀ i, source.coordinate i = orientedCircle P (a source.root) forward (a i) / scale
  circular_caps : source.HasCircularMassCaps

theorem exists_normalized_circle_chart {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a m : ι → ℝ) {P : ℝ} (ha0 : ∀ i, 0 ≤ a i) (haP : ∀ i, a i < P)
    (hinj : Function.Injective a) (hm : ∀ i, 0 < m i) (hn : 1 < Fintype.card ι) :
    Nonempty (NormalizedCircleChart a m P) := by
  classical
  obtain ⟨r, b, hrb, hd, hhalf, hmb, hcap⟩ :=
    exists_density_maximal_pair a m ha0 haP hinj hm hn
  obtain ⟨forward, hforward⟩ := exists_short_orientation
    (ha0 r) (haP r) (ha0 b) (haP b) (hinj.ne hrb)
  let d := shortArc P (a r) (a b)
  let σ := fun i => orientedCircle P (a r) forward (a i)
  let x := fun i => σ i / d
  let q := fun i => m i / m r
  have hP : 0 < P := lt_of_le_of_lt (ha0 r) (haP r)
  have hsig (i : ι) : 0 ≤ σ i ∧ σ i < P :=
    orientedCircle_range hP (ha0 r) (haP r) (ha0 i) (haP i) forward
  have hx (i : ι) : 0 ≤ x i ∧ x i < P / d :=
    ⟨div_nonneg (hsig i).1 hd.le, (div_lt_div_iff_of_pos_right hd).mpr (hsig i).2⟩
  have hqp (i : ι) : 0 < q i := div_pos (hm i) (hm r)
  have hqr : q r = 1 := div_self (ne_of_gt (hm r))
  have hxr : x r = 0 := by simp [x, σ, orientedCircle_root]
  have hxb : x b = 1 := by
    dsimp only [x, σ]
    rw [hforward]
    exact div_self (ne_of_gt hd)
  have hshort (i j : ι) : shortArc P (σ i) (σ j) = shortArc P (a i) (a j) :=
    orientedCircle_shortArc hP (ha0 r) (haP r) (ha0 i) (haP i) (ha0 j) (haP j) forward
  have hcaps (i j : ι) (hij : i ≠ j) :
      q i ≤ |x j - x i| ∧ q i ≤ P / d - |x j - x i| := by
    have hc : q i ≤ shortArc P (σ i) (σ j) / d := by
      rw [hshort]
      exact hcap i j hij
    have hfirst : shortArc P (σ i) (σ j) ≤ |σ j - σ i| := min_le_left _ _
    have hsecond : shortArc P (σ i) (σ j) ≤ P - |σ j - σ i| := min_le_right _ _
    have habs : |x j - x i| = |σ j - σ i| / d := by
      change |σ j / d - σ i / d| = _
      rw [← sub_div, abs_div, abs_of_pos hd]
    rw [habs]
    constructor
    · exact hc.trans (div_le_div_of_nonneg_right hfirst hd.le)
    · rw [← sub_div]
      exact hc.trans (div_le_div_of_nonneg_right hsecond hd.le)
  have hxi : Function.Injective x := by
    intro i j he
    by_contra hij
    have h := (hcaps i j hij).1
    rw [he, sub_self, abs_zero] at h
    linarith [hqp i]
  have hnear (i : ι) (hir : i ≠ r) : 1 ≤ x i := by
    have h := (hcaps r i (Ne.symm hir)).1
    simpa only [hqr, hxr, sub_zero, abs_of_nonneg (hx i).1] using h
  let F : AnchoredCircleSource ι := {
    period := P / d
    period_ge_two := density_pair_period_ge_two hd hhalf
    coordinate := x
    mass := q
    root := r
    neighbor := b
    coordinate_root := hxr
    coordinate_neighbor := hxb
    coordinate_nonneg := fun i => (hx i).1
    coordinate_lt_period := fun i => (hx i).2
    other_coordinate := fun i hir hib => lt_of_le_of_ne (hnear i hir)
      (fun he => hib (hxi (he.symm.trans hxb.symm)))
    coordinate_injective := hxi
    mass_pos := hqp
    mass_root := hqr
    mass_neighbor_le_one := (div_le_one (hm r)).mpr hmb
  }
  exact ⟨{
    scale := d
    scale_pos := hd
    forward := forward
    source := F
    period_eq := rfl
    mass_eq := fun _ => rfl
    coordinate_eq := fun _ => rfl
    circular_caps := hcaps
  }⟩

end CenteredCircle.AllN

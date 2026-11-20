import ACS12.NativeCellRow
import ACS12.GammaStrip

/-! Original LOW mass cells and their complete analytic row. -/
namespace ACS12.NativeCells

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaMeasure (gammaDensity gammaDensity_pos gammaDensity_cosh_moment)

private def extendWidth {n : ℕ} (w : Fin n → ℝ) (i : ℕ) : ℝ :=
  if h : i < n then w ⟨i,h⟩ else 0

noncomputable def massCells {n : ℕ} (w : Fin n → ℝ) (j : ℕ) : ℝ :=
  2 * Real.pi * ∑ i ∈ Finset.range j, extendWidth w i

@[simp] theorem massCells_zero {n : ℕ} (w : Fin n → ℝ) : massCells w 0 = 0 := by simp [massCells]

theorem massCells_end {n : ℕ} {w : Fin n → ℝ} (hw : (∑ i, w i) = 1) :
    massCells w n = 2 * Real.pi := by
  unfold massCells
  rw [← Fin.sum_univ_eq_sum_range, show (∑ i : Fin n, extendWidth w i.val) = ∑ i : Fin n, w i by
    apply Finset.sum_congr rfl
    intro i _
    simp only [extendWidth, dif_pos i.isLt], hw, mul_one]

private theorem massCells_step {n : ℕ} {w : Fin n → ℝ} (i : Fin n) :
    massCells w (i.val + 1) = massCells w i.val + 2 * Real.pi * w i := by
  unfold massCells
  rw [Finset.sum_range_succ, extendWidth, dif_pos i.isLt, mul_add]

theorem massCells_strictMonoOn {n : ℕ} {w : Fin n → ℝ} (hw : ∀ i, 0 < w i) :
    StrictMonoOn (massCells w) (Icc (0 : ℕ) n) := by
  apply (strictMonoOn_Iic_of_lt_succ (n := n) (ψ := massCells w) ?_).mono
    (fun i hi => hi.2)
  intro j hj
  let i : Fin n := ⟨j,hj⟩
  change massCells w i.val < massCells w (i.val + 1)
  rw [massCells_step i]
  exact lt_add_of_pos_right _ (mul_pos (mul_pos (by norm_num) Real.pi_pos) (hw i))

theorem massCells_halfWidth {n : ℕ} {w : Fin n → ℝ} (i : Fin n) :
    halfWidth (massCells w) i = Real.pi * w i := by
  unfold halfWidth
  rw [massCells_step i]
  ring

theorem center_mem {n : ℕ} {edge : ℕ → ℝ} (he : StrictMonoOn edge (Icc (0 : ℕ) n))
    (h0 : edge 0 = 0) (hN : edge n = 2 * Real.pi) (i : Fin n) :
    center edge i ∈ Ioo 0 (2 * Real.pi) := by
  have hi : i.val ∈ Icc (0 : ℕ) n := ⟨Nat.zero_le _,i.isLt.le⟩
  have hj : i.val + 1 ∈ Icc (0 : ℕ) n := ⟨Nat.zero_le _,i.isLt⟩
  have hL := he.monotoneOn (show (0 : ℕ) ∈ Icc 0 n from ⟨le_rfl,Nat.zero_le _⟩) hi (Nat.zero_le _)
  have hU := he.monotoneOn hj (show n ∈ Icc (0 : ℕ) n from ⟨Nat.zero_le _,le_rfl⟩) i.isLt
  have hI := he hi hj (Nat.lt_succ_self _)
  rw [h0] at hL
  rw [hN] at hU
  unfold center
  exact ⟨by linarith only [hL,hI], by linarith only [hU,hI]⟩

noncomputable def rowAtFrequency (w s : ℝ) : ℝ :=
  Real.sinh (s * (Real.pi - Real.pi * w)) / Real.sinh (s * (Real.pi * w))

noncomputable def analyticRow (p N : ℝ) : ℝ :=
  ∫ s : ℝ in Ioi 0, 2 * gammaDensity p s * rowAtFrequency N⁻¹ s

private theorem sinh_le_mul_cosh {x : ℝ} (hx : 0 ≤ x) : Real.sinh x ≤ x * Real.cosh x := by
  let f (t : ℝ) := t * Real.cosh t - Real.sinh t
  have hD (t : ℝ) : HasDerivAt f (t * Real.sinh t) t := by
    convert ((hasDerivAt_id t).mul (Real.hasDerivAt_cosh t)).sub (Real.hasDerivAt_sinh t) using 1
    simp only [id_eq, one_mul, add_sub_cancel_left]
  have hM : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · exact fun t _ => (hD t).continuousAt.continuousWithinAt
    · exact fun t _ => (hD t).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : 0 ≤ t := show t ∈ Ici (0 : ℝ) from interior_subset ht
      rw [(hD t).deriv]
      exact mul_nonneg ht' (Real.sinh_nonneg_iff.mpr ht')
  have h := hM (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx) hx
  have h0 : f 0 = 0 := by simp [f]
  exact sub_nonneg.mp (h0 ▸ h)

private theorem rowAtFrequency_bounds {w s : ℝ} (hw : 0 < w) (hw₁ : w < 1) (hs : 0 < s) :
    0 < rowAtFrequency w s ∧ rowAtFrequency w s ≤
      ((1 - w) / w) * Real.cosh (s * (Real.pi - Real.pi * w)) := by
  let a := s * (Real.pi * w)
  let b := s * (Real.pi - Real.pi * w)
  have ha : 0 < a := mul_pos hs (mul_pos Real.pi_pos hw)
  have hb : 0 < b := mul_pos hs (sub_pos.mpr (mul_lt_of_lt_one_right Real.pi_pos hw₁))
  have hA : a ≤ Real.sinh a := (Real.self_lt_sinh_iff.mpr ha).le
  have hB := sinh_le_mul_cosh hb.le
  have hS := Real.sinh_pos_iff.mpr ha
  refine ⟨div_pos (Real.sinh_pos_iff.mpr hb) hS, ?_⟩
  change Real.sinh b / Real.sinh a ≤ ((1 - w) / w) * Real.cosh b
  calc
    _ ≤ (b * Real.cosh b) / a :=
      div_le_div_of_nonneg_left (Real.sinh_pos_iff.mpr hb).le ha hA |>.trans
        (div_le_div_of_nonneg_right hB ha.le)
    _ = _ := by
      dsimp only [a,b]
      field_simp [hs.ne',hw.ne',Real.pi_pos.ne']

theorem gammaCosh_integrable {p y : ℝ} (hp : 0 < p) (hy : |y| < Real.pi) :
    IntegrableOn (fun s => 2 * gammaDensity p s * Real.cosh (s * y)) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [gammaDensity_cosh_moment hp hy]
  exact (Real.rpow_pos_of_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith only [(abs_lt.mp hy).1],
    by linarith only [(abs_lt.mp hy).2]⟩) _).ne'

theorem analyticRow_integrable {p N : ℝ} (hp : 0 < p) (hN : 1 < N) :
    IntegrableOn (fun s => 2 * gammaDensity p s * rowAtFrequency N⁻¹ s) (Ioi 0) := by
  let w := N⁻¹
  have hw : 0 < w := inv_pos.mpr (zero_lt_one.trans hN)
  have hw₁ : w < 1 := inv_lt_one_of_one_lt₀ hN
  have hy₀ : 0 ≤ Real.pi - Real.pi * w := sub_nonneg.mpr (mul_le_of_le_one_right Real.pi_pos.le hw₁.le)
  have hy : |Real.pi - Real.pi * w| < Real.pi := by
    rw [abs_of_nonneg hy₀]
    linarith only [mul_pos Real.pi_pos hw]
  have hC := (gammaCosh_integrable hp hy).const_mul ((1 - w) / w)
  have hM : Measurable (fun s => 2 * gammaDensity p s * rowAtFrequency w s) := by
    exact (measurable_const.mul (GammaMeasure.continuous_gammaDensity hp).measurable).mul
      (by unfold rowAtFrequency; fun_prop)
  apply hC.mono' hM.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs₀ : 0 < s := hs
  obtain ⟨hP,hB⟩ := rowAtFrequency_bounds hw hw₁ hs₀
  have hG := mul_pos (by norm_num : (0 : ℝ) < 2) (gammaDensity_pos hp s)
  rw [Real.norm_of_nonneg (mul_nonneg hG.le hP.le)]
  have h := mul_le_mul_of_nonneg_left hB hG.le
  change 2 * gammaDensity p s * rowAtFrequency w s ≤
    ((1 - w) / w) * (2 * gammaDensity p s * Real.cosh (s * (Real.pi - Real.pi * w)))
  nlinarith only [h]

theorem analyticRow_pos {p N : ℝ} (hp : 0 < p) (hN : 1 < N) : 0 < analyticRow p N := by
  have hw : 0 < N⁻¹ := inv_pos.mpr (zero_lt_one.trans hN)
  have hw₁ : N⁻¹ < 1 := inv_lt_one_of_one_lt₀ hN
  letI : NeZero (volume.restrict (Ioi (0 : ℝ))) := ⟨positiveHalfLine_ne_zero⟩
  have h := integral_strict_of_ae_lt (volume.restrict (Ioi (0 : ℝ))) (integrable_zero ℝ ℝ _)
    (analyticRow_integrable hp hN) ?_
  · simpa only [analyticRow, integral_zero] using h
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_pos (mul_pos (by norm_num) (gammaDensity_pos hp s)) (rowAtFrequency_bounds hw hw₁ hs).1

end ACS12.NativeCells

import ACS12.BoseShape
import ACS12.PressureCurvature

/-! The whole-contrast half-path lower comparison in WC4–7. -/
namespace ACS12.Pressure

open Set

theorem tanh_rational_bounds {v : ℝ} (hv : 0 < v) :
    3 * v / (3 + v ^ 2) < Real.tanh v ∧
    Real.tanh v < v * (15 + v ^ 2) / (15 + 6 * v ^ 2) := by
  let f (t : ℝ) := (3 + t ^ 2) * Real.sinh t - 3 * t * Real.cosh t
  let g (t : ℝ) := t * (15 + t ^ 2) * Real.cosh t - (15 + 6 * t ^ 2) * Real.sinh t
  let h (t : ℝ) := t * Real.cosh t - Real.sinh t
  have hD (t : ℝ) : HasDerivAt h (t * Real.sinh t) t := by
    convert ((hasDerivAt_id t).mul (Real.hasDerivAt_cosh t)).sub (Real.hasDerivAt_sinh t) using 1
    simp only [id_eq,one_mul,add_sub_cancel_left]
  have hfD (t : ℝ) : HasDerivAt f (t * h t) t := by
    have ht := hasDerivAt_id t
    convert (((ht.pow 2).const_add 3).mul (Real.hasDerivAt_sinh t)).sub
      ((ht.const_mul 3).mul (Real.hasDerivAt_cosh t)) using 1
    norm_num [h] <;> ring
  have hgD (t : ℝ) : HasDerivAt g (t * f t) t := by
    have ht := hasDerivAt_id t
    convert ((ht.mul ((ht.pow 2).const_add 15)).mul (Real.hasDerivAt_cosh t)).sub
      ((((ht.pow 2).const_mul 6).const_add 15).mul (Real.hasDerivAt_sinh t)) using 1
    norm_num [f] <;> ring
  have hP (t : ℝ) (ht : 0 < t) : 0 < h t :=
    BoseShape.positive_of_derivative (by norm_num [h]) hD
      (fun x hx => mul_pos hx (Real.sinh_pos_iff.mpr hx)) ht
  have hfP (t : ℝ) (ht : 0 < t) : 0 < f t :=
    BoseShape.positive_of_derivative (by norm_num [f]) hfD (fun x hx => mul_pos hx (hP x hx)) ht
  have hgP : 0 < g v :=
    BoseShape.positive_of_derivative (by norm_num [g]) hgD (fun x hx => mul_pos hx (hfP x hx)) hv
  have hfV := hfP v hv
  rw [Real.tanh_eq_sinh_div_cosh]
  constructor
  · apply (div_lt_div_iff₀ (by positivity : 0 < 3 + v ^ 2) (Real.cosh_pos v)).mpr
    have h := sub_pos.mp hfV
    nlinarith only [h]
  · apply (div_lt_div_iff₀ (Real.cosh_pos v) (by positivity : 0 < 15 + 6 * v ^ 2)).mpr
    have h := sub_pos.mp hgP
    nlinarith only [h]

noncomputable def halfPathComparison (v : ℝ) : ℝ :=
  (8 / 25) * (15 + 6 * v ^ 2) / (105 + 17 * v ^ 2)

noncomputable def debitChord (v : ℝ) : ℝ := 1 / 224 + (3773 / 100000) * v

theorem halfPathComparison_le_tanh {v : ℝ} (hv : 0 < v) :
    halfPathComparison v ≤ (8 / 25) * v / (2 * v + 5 * Real.tanh v) := by
  have hT := tanh_rational_bounds hv
  have hT₀ := (by positivity : 0 < 3 * v / (3 + v ^ 2)).trans hT.1
  have hA : 0 < 105 + 17 * v ^ 2 := by positivity
  have hB : 0 < 2 * v + 5 * Real.tanh v := by positivity
  unfold halfPathComparison
  apply (div_le_div_iff₀ hA hB).mpr
  have h := (lt_div_iff₀ (by positivity : 0 < 15 + 6 * v ^ 2)).mp hT.2
  nlinarith only [h]

theorem halfPathComparison_sub_debit_gt {v : ℝ} (hv : 0 ≤ v) (hV : v ≤ 111 / 80) :
    3 / 1000 < halfPathComparison v - debitChord v := by
  let V : ℝ := 111 / 80
  let d (t : ℝ) := halfPathComparison t - debitChord t
  have hD (t : ℝ) : HasDerivAt d (240 * t / (105 + 17 * t ^ 2) ^ 2 - 3773 / 100000) t := by
    have ht := hasDerivAt_id t
    have hA := (((ht.pow 2).const_mul 6).const_add 15).const_mul (8 / 25)
    have hB := ((ht.pow 2).const_mul 17).const_add 105
    have hC := (ht.const_mul (3773 / 100000)).const_add (1 / 224)
    have h : 105 + 17 * t ^ 2 ≠ 0 := by positivity
    convert (hA.div hB (by simpa only [id_eq] using h)).sub hC using 1
    norm_num
    field_simp [h]
    ring
  have hM : AntitoneOn d (Icc 0 V) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · exact fun t _ => (hD t).continuousAt.continuousWithinAt
    · exact fun t _ => (hD t).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Icc 0 V := interior_subset ht
      have hA : (105 : ℝ) ≤ 105 + 17 * t ^ 2 := le_add_of_nonneg_right (mul_nonneg (by norm_num) (sq_nonneg t))
      have hB := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 105) hA 2
      have hV' : t ≤ 7 / 5 := ht'.2.trans (by norm_num [V])
      rw [(hD t).deriv]
      apply sub_nonpos.mpr
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith only [hB,hV']
  have h := hM ⟨hv,hV⟩ (show V ∈ Icc 0 V from ⟨by norm_num [V],le_rfl⟩) hV
  exact (by norm_num [d,V,halfPathComparison,debitChord] : (3 / 1000 : ℝ) < d V).trans_le h

end ACS12.Pressure

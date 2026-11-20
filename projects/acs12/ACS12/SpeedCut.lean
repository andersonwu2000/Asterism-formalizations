import ACS12.BoseShape

/-! Turning-point comparisons for the two full-ray fourth-source numerators. -/

namespace ACS12.GammaMeasure

open Set
open BoseShape

def NegativePositiveCut (f : ℝ → ℝ) : Prop :=
  ∃ c > 0, (∀ x ∈ Ioo 0 c, f x < 0) ∧ f c = 0 ∧ ∀ x > c, 0 < f x

private theorem cut_of_increasing {f d : ℝ → ℝ} {b : ℝ}
    (hD : ∀ x, HasDerivAt f (d x) x) (hd : ∀ x > 0, 0 < d x)
    (hb : 0 < b) (h0 : f 0 < 0) (hB : 0 < f b) : NegativePositiveCut f := by
  have hm : StrictMonoOn f (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact fun x _ => (hD x).continuousAt.continuousWithinAt
    · intro x hx
      rw [(hD x).deriv]
      exact hd x (by simpa only [interior_Ici, mem_Ioi] using hx)
  have hC : ContinuousOn f (Icc 0 b) := fun x _ => (hD x).continuousAt.continuousWithinAt
  obtain ⟨r, hr, he⟩ := intermediate_value_Icc hb.le hC ⟨h0.le, hB.le⟩
  have hr₀ : 0 < r := lt_of_le_of_ne hr.1 (fun h => h0.ne (h ▸ he))
  refine ⟨r, hr₀, ?_, he, ?_⟩
  · intro x hx
    rw [← he]
    exact hm hx.1.le hr.1 hx.2
  · intro x hx
    rw [← he]
    exact hm hr.1 (hr.1.trans hx.le) hx

private theorem cut_of_derivative_cut {f d : ℝ → ℝ} {b : ℝ}
    (hD : ∀ x, HasDerivAt f (d x) x) (hd : NegativePositiveCut d)
    (hb : 0 < b) (h0 : f 0 ≤ 0) (hB : 0 < f b) : NegativePositiveCut f := by
  obtain ⟨r, hr, hBefore, _, hAfter⟩ := hd
  have hDec : StrictAntiOn f (Icc 0 r) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 r)
    · exact fun x _ => (hD x).continuousAt.continuousWithinAt
    · intro x hx
      rw [(hD x).deriv]
      exact hBefore x (by simpa only [interior_Icc] using hx)
  have hInc : StrictMonoOn f (Ici r) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici r)
    · exact fun x _ => (hD x).continuousAt.continuousWithinAt
    · intro x hx
      rw [(hD x).deriv]
      exact hAfter x (by simpa only [interior_Ici, mem_Ioi] using hx)
  have hNeg (x : ℝ) (hx : 0 < x) (hxr : x ≤ r) : f x < 0 :=
    (hDec ⟨le_rfl, hr.le⟩ ⟨hx.le, hxr⟩ hx).trans_le h0
  have hrb : r < b := lt_of_not_ge fun h => (hNeg b hb h).not_gt hB
  have hC : ContinuousOn f (Icc r b) := fun x _ => (hD x).continuousAt.continuousWithinAt
  obtain ⟨c, hc, he⟩ := intermediate_value_Icc hrb.le hC ⟨(hNeg r hr le_rfl).le, hB.le⟩
  refine ⟨c, hr.trans_le hc.1, ?_, he, ?_⟩
  · intro x hx
    rcases le_total x r with h | h
    · exact hNeg x hx.1 h
    · rw [← he]
      exact hInc h hc.1 hx.2
  · intro x hx
    rw [← he]
    exact hInc hc.1 (hc.1.trans hx.le) hx

noncomputable def diagonalSpeedNumerator (x : ℝ) : ℝ :=
  expQuad 1 1 (-4) 1 x + x ^ 2 + 4 * x - 2 + expQuad (-1) 0 0 1 x

theorem diagonalSpeedNumerator_cut : NegativePositiveCut diagonalSpeedNumerator := by
  let f₁ (x : ℝ) := expQuad 1 1 (-2) (-3) x + 2 * x + 4 + expQuad (-1) 0 0 (-1) x
  let f₂ (x : ℝ) := expQuad 1 1 0 (-5) x + 2 + expQuad (-1) 0 0 1 x
  let f₃ (x : ℝ) := expQuad 1 1 2 (-5) x + expQuad (-1) 0 0 (-1) x
  let f₄ (x : ℝ) := expQuad 1 1 4 (-3) x + expQuad (-1) 0 0 1 x
  let f₅ (x : ℝ) := expQuad 1 1 6 1 x + expQuad (-1) 0 0 (-1) x
  let f₆ (x : ℝ) := expQuad 1 1 8 7 x + expQuad (-1) 0 0 1 x
  have h₁ (x : ℝ) : HasDerivAt diagonalSpeedNumerator (f₁ x) x := by
    have hp := ((((hasDerivAt_id x).pow 2).add ((hasDerivAt_id x).const_mul 4)).sub_const 2)
    convert ((expQuad_deriv 1 1 (-4) 1 x).add hp).add (expQuad_deriv (-1) 0 0 1 x) using 1
    · funext y
      simp only [diagonalSpeedNumerator, Pi.add_apply, Pi.pow_apply, id_eq]
      ring
    · norm_num [f₁, id_eq, show (2 - 1 : ℕ) = 1 by decide] <;> ring
  have h₂ (x : ℝ) : HasDerivAt f₁ (f₂ x) x := by
    convert (((expQuad_deriv 1 1 (-2) (-3) x).add ((hasDerivAt_id x).const_mul 2)).add_const 4).add
      (expQuad_deriv (-1) 0 0 (-1) x) using 1
    norm_num [f₂]
  have h₃ (x : ℝ) : HasDerivAt f₂ (f₃ x) x := by
    convert ((expQuad_deriv 1 1 0 (-5) x).add_const 2).add (expQuad_deriv (-1) 0 0 1 x) using 1
    norm_num [f₃]
  have h₄ (x : ℝ) : HasDerivAt f₃ (f₄ x) x := by
    convert (expQuad_deriv 1 1 2 (-5) x).add (expQuad_deriv (-1) 0 0 (-1) x) using 1
    norm_num [f₄]
  have h₅ (x : ℝ) : HasDerivAt f₄ (f₅ x) x := by
    convert (expQuad_deriv 1 1 4 (-3) x).add (expQuad_deriv (-1) 0 0 1 x) using 1
    norm_num [f₅]
  have h₆ (x : ℝ) : HasDerivAt f₅ (f₆ x) x := by
    convert (expQuad_deriv 1 1 6 1 x).add (expQuad_deriv (-1) 0 0 (-1) x) using 1
    norm_num [f₆]
  have hF (x : ℝ) (hx : 0 < x) : 0 < f₆ x := by
    unfold f₆ expQuad
    positivity
  have h₅pos (x : ℝ) (hx : 0 < x) : 0 < f₅ x :=
    positive_of_derivative (by norm_num [f₅, expQuad]) h₆ hF hx
  have he := Real.one_le_exp_iff.mpr (show (0 : ℝ) ≤ 10 by norm_num)
  have he' := Real.exp_le_one_iff.mpr (show (-10 : ℝ) ≤ 0 by norm_num)
  have hep := Real.exp_pos (-10 : ℝ)
  have c₄ : NegativePositiveCut f₄ := cut_of_increasing h₅ h₅pos
    (by norm_num : (0 : ℝ) < 10) (by norm_num [f₄, expQuad])
    (by norm_num [f₄, expQuad] <;> linarith)
  have c₃ : NegativePositiveCut f₃ := cut_of_derivative_cut h₄ c₄
    (by norm_num : (0 : ℝ) < 10) (by norm_num [f₃, expQuad])
    (by norm_num [f₃, expQuad] <;> linarith)
  have c₂ : NegativePositiveCut f₂ := cut_of_derivative_cut h₃ c₃
    (by norm_num : (0 : ℝ) < 10) (by norm_num [f₂, expQuad])
    (by norm_num [f₂, expQuad] <;> linarith)
  have c₁ : NegativePositiveCut f₁ := cut_of_derivative_cut h₂ c₂
    (by norm_num : (0 : ℝ) < 10) (by norm_num [f₁, expQuad])
    (by norm_num [f₁, expQuad] <;> linarith)
  exact cut_of_derivative_cut h₁ c₁ (by norm_num : (0 : ℝ) < 10)
    (by norm_num [diagonalSpeedNumerator, expQuad])
    (by norm_num [diagonalSpeedNumerator, expQuad] <;> linarith)

noncomputable def fixedMassSpeedNumerator (θ x : ℝ) : ℝ :=
  expQuad 1 0 1 (-3 - θ) x + x + 2 + 2 * θ + expQuad (-1) 0 0 (1 - θ) x

theorem fixedMassSpeedNumerator_cut {θ : ℝ} (hθ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    NegativePositiveCut (fixedMassSpeedNumerator θ) := by
  let f₁ (x : ℝ) := expQuad 1 0 1 (-2 - θ) x + 1 + expQuad (-1) 0 0 (θ - 1) x
  let f₂ (x : ℝ) := expQuad 1 0 1 (-1 - θ) x + expQuad (-1) 0 0 (1 - θ) x
  let f₃ (x : ℝ) := expQuad 1 0 1 (-θ) x + expQuad (-1) 0 0 (θ - 1) x
  let f₄ (x : ℝ) := expQuad 1 0 1 (1 - θ) x + expQuad (-1) 0 0 (1 - θ) x
  have h₁ (x : ℝ) : HasDerivAt (fixedMassSpeedNumerator θ) (f₁ x) x := by
    have h := ((expQuad_deriv 1 0 1 (-3 - θ) x).add (hasDerivAt_id x)).add_const 2
    convert (h.add_const (2 * θ)).add (expQuad_deriv (-1) 0 0 (1 - θ) x) using 1
    norm_num [f₁, expQuad]
    ring
  have h₂ (x : ℝ) : HasDerivAt f₁ (f₂ x) x := by
    convert ((expQuad_deriv 1 0 1 (-2 - θ) x).add_const 1).add
      (expQuad_deriv (-1) 0 0 (θ - 1) x) using 1
    norm_num [f₂, expQuad]
    ring
  have h₃ (x : ℝ) : HasDerivAt f₂ (f₃ x) x := by
    convert (expQuad_deriv 1 0 1 (-1 - θ) x).add (expQuad_deriv (-1) 0 0 (1 - θ) x) using 1
    norm_num [f₃, expQuad]
    ring
  have h₄ (x : ℝ) : HasDerivAt f₃ (f₄ x) x := by
    convert (expQuad_deriv 1 0 1 (-θ) x).add (expQuad_deriv (-1) 0 0 (θ - 1) x) using 1
    norm_num [f₄, expQuad]
    ring
  have hF (x : ℝ) (hx : 0 < x) : 0 < f₄ x := by
    have h : 0 ≤ 1 - θ := sub_nonneg.mpr hθ₁
    simp only [f₄, expQuad, zero_mul, zero_add, one_mul]
    exact add_pos_of_pos_of_nonneg (mul_pos (add_pos_of_pos_of_nonneg hx h) (Real.exp_pos _))
      (mul_nonneg h (Real.exp_pos _).le)
  have he := Real.one_le_exp_iff.mpr (show (0 : ℝ) ≤ 10 by norm_num)
  have he' := Real.exp_le_one_iff.mpr (show (-10 : ℝ) ≤ 0 by norm_num)
  have hep := Real.exp_pos (-10 : ℝ)
  have hneg : 0 ≤ 1 - θ := sub_nonneg.mpr hθ₁
  have hcoef := mul_le_mul_of_nonneg_left he hneg
  have hb (c : ℝ) (hc : 0 < c) : c ≤ c * Real.exp 10 := le_mul_of_one_le_right hc.le he
  have c₃ : NegativePositiveCut f₃ := cut_of_increasing h₄ hF
    (by norm_num : (0 : ℝ) < 10) (by norm_num [f₃, expQuad] <;> linarith) (by
      norm_num [f₃, expQuad]
      have h₁ := hb (10 - θ) (by linarith)
      have h₂ := mul_le_of_le_one_right hneg he'
      nlinarith only [h₁, h₂])
  have c₂ : NegativePositiveCut f₂ := cut_of_derivative_cut h₃ c₃
    (by norm_num : (0 : ℝ) < 10) (by norm_num [f₂, expQuad] <;> linarith) (by
      norm_num [f₂, expQuad]
      have h₁ := hb (9 - θ) (by linarith)
      have h₂ := mul_nonneg hneg hep.le
      nlinarith only [h₁, h₂, hθ₁])
  have c₁ : NegativePositiveCut f₁ := cut_of_derivative_cut h₂ c₂
    (by norm_num : (0 : ℝ) < 10) (by norm_num [f₁, expQuad] <;> linarith) (by
      norm_num [f₁, expQuad]
      have h₁ := hb (8 - θ) (by linarith)
      have h₂ := mul_le_of_le_one_right hneg he'
      nlinarith only [h₁, h₂])
  exact cut_of_derivative_cut h₁ c₁ (by norm_num : (0 : ℝ) < 10)
    (by norm_num [fixedMassSpeedNumerator, expQuad] <;> linarith) (by
      norm_num [fixedMassSpeedNumerator, expQuad]
      have h₁ := hb (7 - θ) (by linarith)
      have h₂ := mul_nonneg hneg hep.le
      nlinarith only [h₁, h₂, hθ, hθ₁])

end ACS12.GammaMeasure


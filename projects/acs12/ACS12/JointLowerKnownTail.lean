import ACS12.JointLowerKnownPrice
import ACS12.JointRightResponsePrice

/-! The complete known source tail and its third response in W32. -/
namespace ACS12.GammaMeasure

open Set CenteredCircle.AllN

private noncomputable def lowerKnownAtom (k : ℕ) (p j u : ℝ) : ℝ :=
  match k with
  | 0 => purePeanoB p u j
  | 1 => p * (j ^ (-p - 1) - (j + u) ^ (-p - 1))
  | 2 => p * (p + 1) * (j + u) ^ (-p - 2)
  | _ => -(p * (p + 1) * (p + 2)) * (j + u) ^ (-p - 3)

private theorem lowerKnownAtom_deriv {k : ℕ} (hk : k < 3) (p j u : ℝ) (h : 0 < j + u) :
    HasDerivAt (lowerKnownAtom k p j) (lowerKnownAtom (k + 1) p j u) u := by
  have hPow (r : ℝ) : HasDerivAt (fun x => (j + x) ^ r) (r * (j + u) ^ (r - 1)) u := by
    simpa only [id_eq,one_mul,mul_one] using
      (((hasDerivAt_id u).const_add j).rpow_const (p := r) (Or.inl h.ne'))
  interval_cases k
  · convert ((((hasDerivAt_id u).mul_const (p * j ^ (-(p + 1)))).sub_const (j ^ (-p))).add (hPow (-p))) using 1
    · funext x; unfold lowerKnownAtom purePeanoB; simp only [id_eq,Pi.add_apply,add_comm x j]; ring
    · unfold lowerKnownAtom; simp only [id_eq,one_mul,show -(p + 1) = -p - 1 by ring]; ring
  · convert ((hasDerivAt_const u (j ^ (-p - 1))).sub (hPow (-p - 1))).const_mul p using 1
    simp only [lowerKnownAtom,show -p - 1 - 1 = -p - 2 by ring]
    ring
  · convert (hPow (-p - 2)).const_mul (p * (p + 1)) using 1
    simp only [lowerKnownAtom,show -p - 2 - 1 = -p - 3 by ring]
    ring

private theorem lowerKnownAtom_deriv_bound {p j u : ℝ} (hp : 1 ≤ p) (hP : p ≤ 2)
    (hj : 1 ≤ j) (hu : 0 ≤ u) {k : ℕ} (hk : 1 ≤ k) (hK : k ≤ 3) :
    ‖lowerKnownAtom k p j u‖ ≤ 30 * j ^ (-2 : ℝ) := by
  let q := j ^ (-2 : ℝ)
  have hj₀ := zero_lt_one.trans_le hj
  have hp₀ := zero_lt_one.trans_le hp
  have hJ : j ≤ j + u := le_add_of_nonneg_right hu
  have hJ₀ := hj₀.trans_le hJ
  have hq : 0 ≤ q := Real.rpow_nonneg hj₀.le _
  have hR (r : ℝ) (hr : r ≤ -2) : 0 ≤ (j + u) ^ r ∧ (j + u) ^ r ≤ q :=
    ⟨Real.rpow_nonneg hJ₀.le _,(Real.rpow_le_rpow_of_nonpos hj₀ hJ (hr.trans (by norm_num))).trans
      (Real.rpow_le_rpow_of_exponent_le hj hr)⟩
  have h₁ := hR (-p - 1) (by linarith only [hp])
  have h₂ := hR (-p - 2) (by linarith only [hp])
  have h₃ := hR (-p - 3) (by linarith only [hp])
  have hJ₁ : j ^ (-p - 1) ≤ q := Real.rpow_le_rpow_of_exponent_le hj (by linarith only [hp])
  have hJ₁₀ : 0 ≤ j ^ (-p - 1) := Real.rpow_nonneg hj₀.le _
  have hB : p * (p + 1) ≤ 6 := by
    have h := mul_le_mul hP (show p + 1 ≤ 3 by linarith only [hP]) (by positivity) (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at h
    exact h
  have hB' : p * (p + 1) * (p + 2) ≤ 24 := by
    have h := mul_le_mul hB (show p + 2 ≤ 4 by linarith only [hP]) (by positivity) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num at h
    exact h
  rw [Real.norm_eq_abs]
  interval_cases k
  · unfold lowerKnownAtom
    rw [abs_mul,abs_of_nonneg hp₀.le]
    have h : |j ^ (-p - 1) - (j + u) ^ (-p - 1)| ≤ q + q := by
      apply (abs_sub_le (j ^ (-p - 1)) 0 ((j + u) ^ (-p - 1))).trans
      simp only [sub_zero,zero_sub,abs_neg,abs_of_nonneg hJ₁₀,abs_of_nonneg h₁.1]
      exact add_le_add hJ₁ h₁.2
    have h' := mul_le_mul hP h (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    change _ ≤ 30 * q
    nlinarith only [h',hq]
  · unfold lowerKnownAtom
    rw [abs_of_nonneg (by positivity)]
    have h := mul_le_mul hB h₂.2 h₂.1 (by norm_num)
    change _ ≤ 30 * q
    nlinarith only [h,hq]
  · unfold lowerKnownAtom
    rw [neg_mul,abs_neg,abs_of_nonneg (by positivity)]
    have h := mul_le_mul hB' h₃.2 h₃.1 (by norm_num)
    change _ ≤ 30 * q
    nlinarith only [h,hq]

private theorem lowerKnownAtom_bound {p j u : ℝ} (hp : 1 ≤ p) (hP : p ≤ 2)
    (hj : 1 ≤ j) (hu : u ∈ Ioo 0 2) {k : ℕ} (hk : k ≤ 3) :
    ‖lowerKnownAtom k p j u‖ ≤ 60 * j ^ (-2 : ℝ) := by
  have hJ := zero_lt_one.trans_le hj
  have hQ : 0 ≤ 30 * j ^ (-2 : ℝ) := mul_nonneg (by norm_num) (Real.rpow_nonneg hJ.le _)
  by_cases h₀ : k = 0
  · subst k
    have hC : ContinuousOn (lowerKnownAtom 0 p j) (Icc 0 u) := by
      intro y hy
      exact (lowerKnownAtom_deriv (by decide : (0 : ℕ) < 3) p j y
        (add_pos_of_pos_of_nonneg hJ hy.1)).continuousAt.continuousWithinAt
    have hD : DifferentiableOn ℝ (lowerKnownAtom 0 p j) (Ioo 0 u) := by
      intro y hy
      exact (lowerKnownAtom_deriv (by decide : (0 : ℕ) < 3) p j y
        (add_pos hJ hy.1)).differentiableAt.differentiableWithinAt
    obtain ⟨y,hy,h⟩ := exists_deriv_eq_slope (lowerKnownAtom 0 p j) hu.1 hC hD
    rw [(lowerKnownAtom_deriv (by decide : (0 : ℕ) < 3) p j y (add_pos hJ hy.1)).deriv,
      show lowerKnownAtom 0 p j 0 = 0 by simp [lowerKnownAtom,purePeanoB],sub_zero,sub_zero] at h
    have h' := (eq_div_iff hu.1.ne').mp h
    rw [← h',norm_mul,Real.norm_of_nonneg hu.1.le]
    have hP := lowerKnownAtom_deriv_bound hp hP hj hy.1.le (k := 1) (by decide) (by decide)
    exact (mul_le_mul hP hu.2.le hu.1.le hQ).trans_eq (by ring)
  · exact (lowerKnownAtom_deriv_bound hp hP hj hu.1.le (by omega) hk).trans
      (mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg hJ.le _))

private theorem lowerKnown_dominator : Summable (fun j : ℕ => (60 : ℝ) * (1 + (j : ℝ)) ^ (-2 : ℝ)) := by
  have h := (powerTail_summable (q := (2 : ℝ)) (by norm_num) (1 : ℕ)).mul_left (60 : ℝ)
  simpa only [Nat.cast_one] using h

private theorem lowerKnown_summable {p u : ℝ} (hp : 1 ≤ p) (hP : p ≤ 2) (hu : u ∈ Ioo 0 2)
    {k : ℕ} (hk : k ≤ 3) : Summable (fun j : ℕ => lowerKnownAtom k p ((1 : ℝ) + j) u) :=
  Summable.of_norm_bounded lowerKnown_dominator fun j =>
    lowerKnownAtom_bound hp hP (le_add_of_nonneg_right (Nat.cast_nonneg j)) hu hk

noncomputable def lowerKnownSum (k : ℕ) (p u : ℝ) : ℝ :=
  ∑' j : ℕ, lowerKnownAtom k p ((1 : ℝ) + j) u

theorem lowerKnownSum_hasDerivAt {p u : ℝ} (hp : 1 ≤ p) (hP : p ≤ 2) (hu : u ∈ Ioo 0 2)
    {k : ℕ} (hk : k < 3) : HasDerivAt (lowerKnownSum k p) (lowerKnownSum (k + 1) p u) u := by
  exact hasDerivAt_tsum_of_isPreconnected lowerKnown_dominator isOpen_Ioo (convex_Ioo 0 2).isPreconnected
    (fun j x hx => lowerKnownAtom_deriv hk p ((1 : ℝ) + j) x (by have : 0 < x := hx.1; positivity))
    (fun j x hx => lowerKnownAtom_bound hp hP (le_add_of_nonneg_right (Nat.cast_nonneg j)) hx (by omega))
    hu (lowerKnown_summable hp hP hu (by omega)) hu

private theorem lowerKnownSum_third_nonpos {p u : ℝ} (hp : 1 ≤ p) (hu : 0 < u) :
    lowerKnownSum 3 p u ≤ 0 := by
  have hp₀ := zero_lt_one.trans_le hp
  unfold lowerKnownSum
  apply tsum_nonpos
  intro j
  unfold lowerKnownAtom
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (Real.rpow_nonneg (by positivity) _)

noncomputable def lowerDiagonalKnown (p δ : ℝ) : ℝ :=
  lowerKnownFinite p δ + lowerKnownSum 0 p (1 - δ)

noncomputable def lowerDiagonalKnownD1 (p δ : ℝ) : ℝ :=
  lowerKnownFiniteD1 p δ - lowerKnownSum 1 p (1 - δ)

noncomputable def lowerDiagonalKnownD2 (p δ : ℝ) : ℝ :=
  lowerKnownFiniteD2 p δ + lowerKnownSum 2 p (1 - δ)

private theorem lowerDiagonalKnown_atom_deriv {p δ : ℝ} (hp : 1 ≤ p) (hP : p ≤ 2)
    (hδ : 0 ≤ δ) (hD : δ ≤ 1 / 8) {k : ℕ} (hk : k < 3) :
    HasDerivAt (fun d => lowerKnownSum k p (1 - d)) (-lowerKnownSum (k + 1) p (1 - δ)) δ := by
  have hu : 1 - δ ∈ Ioo (0 : ℝ) 2 := ⟨by linarith only [hD],by linarith only [hδ]⟩
  simpa only [mul_neg,mul_one] using
    (lowerKnownSum_hasDerivAt hp hP hu hk).comp δ ((hasDerivAt_id δ).const_sub 1)

theorem lowerDiagonalKnown_deriv1 {p δ : ℝ} (hp : 1 ≤ p) (hP : p ≤ 2) (hδ : 0 ≤ δ) (hD : δ ≤ 1 / 8) :
    HasDerivAt (lowerDiagonalKnown p) (lowerDiagonalKnownD1 p δ) δ := by
  simpa only [lowerDiagonalKnown,lowerDiagonalKnownD1,sub_eq_add_neg] using
    (lowerKnownFinite_deriv1 p δ (by linarith only [hD])).add
      (lowerDiagonalKnown_atom_deriv hp hP hδ hD (k := 0) (by decide))

theorem lowerDiagonalKnown_deriv2 {p δ : ℝ} (hp : 1 ≤ p) (hP : p ≤ 2) (hδ : 0 ≤ δ) (hD : δ ≤ 1 / 8) :
    HasDerivAt (lowerDiagonalKnownD1 p) (lowerDiagonalKnownD2 p δ) δ := by
  simpa only [lowerDiagonalKnownD1,lowerDiagonalKnownD2,sub_neg_eq_add] using
    (lowerKnownFinite_deriv2 p δ (by linarith only [hD])).sub
      (lowerDiagonalKnown_atom_deriv hp hP hδ hD (k := 1) (by decide))

theorem lowerDiagonalKnown_deriv3 {p δ : ℝ} (hp : 1 ≤ p) (hP : p ≤ 2) (hδ : 0 ≤ δ) (hD : δ ≤ 1 / 8) :
    HasDerivAt (lowerDiagonalKnownD2 p) (lowerKnownFiniteD3 p δ - lowerKnownSum 3 p (1 - δ)) δ := by
  simpa only [lowerDiagonalKnownD2,sub_eq_add_neg] using
    (lowerKnownFinite_deriv3 p δ (by linarith only [hD])).add
      (lowerDiagonalKnown_atom_deriv hp hP hδ hD (k := 2) (by decide))

theorem lowerDiagonal_adjacent_third_gt {p δ : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hδ : 0 ≤ δ) (hD : δ ≤ 1 / 8) :
    (803 / 100 + 5 * (p - 1)) * (p * (p + 1) * lowerDiagonalMass δ ^ (-p - 2)) <
      lowerKnownFiniteD3 p δ - lowerKnownSum 3 p (1 - δ) +
        (p * (p + 1) * lowerDiagonalMass δ ^ (-p - 2)) *
          lowerRightResponseTotal p (lowerDiagonalRatio δ) := by
  let m := lowerDiagonalMass δ
  have hm : 0 < m := by unfold m lowerDiagonalMass; linarith only [hD]
  have hp₀ := zero_lt_one.trans_le hp
  have hN : 0 < p * (p + 1) * m ^ (-p - 2) := by positivity
  have hK := lowerKnownFinite_normalized_gt hp hP hδ hD
  have hR := mul_lt_mul_of_pos_left
    (lowerRightResponseTotal_gt hp hP (lowerDiagonalRatio_mem hδ hD)) hN
  have hTail := lowerKnownSum_third_nonpos hp (show 0 < 1 - δ by linarith only [hD])
  change (423 / 100 : ℝ) * (p * (p + 1) * m ^ (-p - 2)) < _ at hK
  change _ * (p * (p + 1) * m ^ (-p - 2)) < _ + _ * lowerRightResponseTotal p (lowerDiagonalRatio δ)
  nlinarith only [hK,hR,hTail]

theorem lowerKnownSum_zero_eq (p U : ℝ) :
    lowerKnownSum 0 p U = ∑' j : ℕ, purePeanoB p U (1 + (j : ℝ)) := rfl

end ACS12.GammaMeasure

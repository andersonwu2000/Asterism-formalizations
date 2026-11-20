import ACS12.NativeCellAnalytic

/-! The complete LOW cell energy inequality after integrating the exact frequency rows. -/
namespace ACS12.NativeCells

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaMeasure (gammaDensity gammaDensity_pos gammaDensity_cosh_moment)

theorem cellEntry_integral {n : ℕ} {edge : ℕ → ℝ} (he : StrictMonoOn edge (Icc (0 : ℕ) n))
    (h0 : edge 0 = 0) (hN : edge n = 2 * Real.pi) {p : ℝ} (hp : 0 < p) (i j : Fin n) :
    let a (i : Fin n) := center edge i
    IntegrableOn (fun s => 2 * gammaDensity p s * cellEntry s edge i j) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, 2 * gammaDensity p s * cellEntry s edge i j) = angularCost p (halfArc a i j) := by
  let a (i : Fin n) := center edge i
  by_cases h : i = j
  · subst j
    simp only [cellEntry, if_true, mul_zero, halfArc_self, angularCost, Real.sin_zero,
      Real.zero_rpow hp.ne', div_zero, integral_zero]
    exact ⟨integrable_zero ℝ ℝ _, trivial⟩
  have hn : i.val ≠ j.val := fun e => h (Fin.ext e)
  have hMono : StrictMono a := center_strictMono he
  have hi := center_mem he h0 hN i
  have hj := center_mem he h0 hN j
  change a i ∈ Ioo 0 (2 * Real.pi) at hi
  change a j ∈ Ioo 0 (2 * Real.pi) at hj
  have hD : 0 < |a j - a i| := abs_pos.mpr (sub_ne_zero.mpr (hMono.injective.ne (Ne.symm h)))
  have hU : |a j - a i| < 2 * Real.pi := by
    apply abs_lt.mpr
    constructor
    · linarith only [hi.2,hj.1]
    · linarith only [hj.2,hi.1]
  have hy : |Real.pi - abs (a j - a i)| < Real.pi := by
    exact abs_lt.mpr ⟨by linarith only [hU], by linarith only [hD]⟩
  have hArc : Real.sin (halfArc a i j) = Real.cos ((Real.pi - |a j - a i|) / 2) := by
    rw [show (Real.pi - |a j - a i|) / 2 = Real.pi / 2 - |a j - a i| / 2 by ring,
      Real.cos_pi_div_two_sub]
    rcases lt_or_gt_of_ne h with hlt | hlt
    · rw [abs_of_pos (sub_pos.mpr (hMono hlt)), halfArc, if_neg (not_lt_of_gt hlt), add_zero]
    · rw [abs_of_neg (sub_neg.mpr (hMono hlt)), halfArc, if_pos hlt]
      have hA : (a j - a i + 2 * Real.pi) / 2 = Real.pi - (-(a j - a i)) / 2 := by ring
      rw [hA, Real.sin_pi_sub]
  have hs : 0 < Real.sin (halfArc a i j) := by
    have hP := halfArc_mem hMono (fun k => (center_mem he h0 hN k).1.le)
      (fun k => (center_mem he h0 hN k).2) (Ne.symm h)
    exact Real.sin_pos_of_pos_of_lt_pi hP.1 hP.2
  simp only [cellEntry, if_neg hn]
  refine ⟨gammaCosh_integrable hp hy, ?_⟩
  rw [gammaDensity_cosh_moment hp hy, ← hArc, angularCost, Real.rpow_neg hs.le, one_div]

theorem cellEnergy_le {n : ℕ} {w : Fin n → ℝ} (hw : ∀ i, 0 < w i) (hw₁ : ∀ i, w i < 1)
    (hW : (∑ i, w i) = 1) {p : ℝ} (hp : 0 < p) (v : Fin n → ℝ) :
    angularEnergy p v (fun i => center (massCells w) i) ≤ ∑ i, v i ^ 2 * analyticRow p (w i)⁻¹ := by
  let edge := massCells w
  let a (i : Fin n) := center edge i
  let f (i j : Fin n) (s : ℝ) := v i * v j * (2 * gammaDensity p s * cellEntry s edge i j)
  let g (i : Fin n) (s : ℝ) := v i ^ 2 * (2 * gammaDensity p s * rowAtFrequency (w i) s)
  have he := massCells_strictMonoOn hw
  have h0 := massCells_zero w
  have hN := massCells_end hW
  have hF (i j : Fin n) : IntegrableOn (f i j) (Ioi 0) :=
    (cellEntry_integral he h0 hN hp i j).1.const_mul _
  have hG (i : Fin n) : IntegrableOn (g i) (Ioi 0) := by
    have h := (analyticRow_integrable hp ((one_lt_inv₀ (hw i)).mpr (hw₁ i))).const_mul (v i ^ 2)
    simpa only [g, inv_inv] using h
  have hF' (i : Fin n) : IntegrableOn (fun s => ∑ j : Fin n, f i j s) (Ioi 0) :=
    integrable_finsetSum _ (fun j _ => hF i j)
  have hFI : IntegrableOn (fun s => ∑ i : Fin n, ∑ j : Fin n, f i j s) (Ioi 0) :=
    integrable_finsetSum _ (fun i _ => hF' i)
  have hGI : IntegrableOn (fun s => ∑ i : Fin n, g i s) (Ioi 0) :=
    integrable_finsetSum _ (fun i _ => hG i)
  have h := integral_mono_ae hFI hGI (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0 < s := hs
    have h := cellEnergy_frequency_le he h0 hN v hs₀
    simp only [massCells_halfWidth] at h
    have h' := mul_le_mul_of_nonneg_left h (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (gammaDensity_pos hp s).le)
    simp only [Finset.mul_sum] at h'
    convert h' using 1 <;> apply Finset.sum_congr rfl <;> intro i _
    · apply Finset.sum_congr rfl
      intro j _
      unfold f
      ring
    · unfold g rowAtFrequency
      ring)
  have hFE : (∫ s : ℝ in Ioi 0, ∑ i : Fin n, ∑ j : Fin n, f i j s) = angularEnergy p v a := by
    rw [integral_finsetSum _ (fun i _ => hF' i)]
    unfold angularEnergy
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => hF i j)]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [f]
    rw [integral_const_mul, (cellEntry_integral he h0 hN hp i j).2]
  have hGE : (∫ s : ℝ in Ioi 0, ∑ i : Fin n, g i s) = ∑ i, v i ^ 2 * analyticRow p (w i)⁻¹ := by
    rw [integral_finsetSum _ (fun i _ => hG i)]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [g]
    rw [integral_const_mul, analyticRow, inv_inv]
  rwa [hFE,hGE] at h

end ACS12.NativeCells

import ACS12.EndpointEscortPositivity

/-! The whole finite mean-one law follows directly from its single affine escort. -/
namespace ACS12.NativeCells
open Finset
set_option backward.isDefEq.respectTransparency false

theorem nativeFiniteLaw_box_lower {ι : Type*} [Fintype ι] (w u : ι → ℝ)
    (hw : ∀ i, 0 < w i) (hw₁ : ∑ i, w i = 1)
    (hu : ∀ i, 0 < u i) (hu₁ : ∑ i, w i * u i = 1)
    {P : ℝ} (hP : 3 ≤ P) (hP₅ : P ≤ 5) :
    (∑ i, w i * endpointEscortAtom P (u i)) ≤ nativeFiniteFunctional P w u := by
  apply escort_entropy_lower w u (by linarith only [hP]) hw hw₁ hu hu₁
  intro i
  change 0 < endpointEscortDensity P (u i)
  have h := endpointEscortDensity_lower hP hP₅ (hu i).le
  linarith only [h]

theorem nativeFiniteLaw_box_nonneg {ι : Type*} [Fintype ι] (w u : ι → ℝ)
    (hw : ∀ i, 0 < w i) (hw₁ : ∑ i, w i = 1)
    (hu : ∀ i, 0 < u i) (hu₁ : ∑ i, w i * u i = 1)
    {P : ℝ} (hP : 3 ≤ P) (hP₅ : P ≤ 5)
    (hBox : ∀ i, u i ∈ Set.Icc (1/nativeSupportRatio P) (nativeSupportRatio P)) :
    0 ≤ nativeFiniteFunctional P w u :=
  (sum_nonneg (fun i _ => mul_nonneg (hw i).le (endpointEscortAtom_nonneg hP hP₅ (hBox i)))).trans
    (nativeFiniteLaw_box_lower w u hw hw₁ hu hu₁ hP hP₅)

theorem nativeFiniteLaw_box_pos {ι : Type*} [Fintype ι] (w u : ι → ℝ)
    (hw : ∀ i, 0 < w i) (hw₁ : ∑ i, w i = 1)
    (hu : ∀ i, 0 < u i) (hu₁ : ∑ i, w i * u i = 1)
    {P : ℝ} (hP : 3 ≤ P) (hP₅ : P ≤ 5)
    (hBox : ∀ i, u i ∈ Set.Icc (1/nativeSupportRatio P) (nativeSupportRatio P))
    (hNonconstant : ∃ i, u i ≠ 1) : 0 < nativeFiniteFunctional P w u := by
  have hSum : 0 < ∑ i, w i * endpointEscortAtom P (u i) := by
    apply sum_pos' (fun i _ => mul_nonneg (hw i).le (endpointEscortAtom_nonneg hP hP₅ (hBox i)))
    obtain ⟨i,hi⟩ := hNonconstant
    exact ⟨i,mem_univ i,mul_pos (hw i) (endpointEscortAtom_pos hP hP₅ (hBox i) hi)⟩
  exact hSum.trans_le (nativeFiniteLaw_box_lower w u hw hw₁ hu hu₁ hP hP₅)

theorem nativeFiniteLaw_nonneg {ι : Type*} [Fintype ι] (w u : ι → ℝ)
    (hw : ∀ i, 0 < w i) (hw₁ : ∑ i, w i = 1)
    (hu : ∀ i, 0 < u i) (hu₁ : ∑ i, w i * u i = 1)
    {P : ℝ} (hP : 3 ≤ P) (hP₅ : P ≤ 5)
    (hRatio : ∀ i j, u i ≤ nativeSupportRatio P * u j) :
    0 ≤ nativeFiniteFunctional P w u :=
  nativeFiniteLaw_box_nonneg w u hw hw₁ hu hu₁ hP hP₅
    (fun i => mean_one_ratio_support w u (nativeSupportRatio_pos hP) (fun i => (hw i).le) hw₁ hu₁ hRatio i)

theorem nativeFiniteLaw_pos {ι : Type*} [Fintype ι] (w u : ι → ℝ)
    (hw : ∀ i, 0 < w i) (hw₁ : ∑ i, w i = 1)
    (hu : ∀ i, 0 < u i) (hu₁ : ∑ i, w i * u i = 1)
    {P : ℝ} (hP : 3 ≤ P) (hP₅ : P ≤ 5)
    (hRatio : ∀ i j, u i ≤ nativeSupportRatio P * u j)
    (hNonconstant : ∃ i, u i ≠ 1) : 0 < nativeFiniteFunctional P w u :=
  nativeFiniteLaw_box_pos w u hw hw₁ hu hu₁ hP hP₅
    (fun i => mean_one_ratio_support w u (nativeSupportRatio_pos hP) (fun i => (hw i).le) hw₁ hu₁ hRatio i)
    hNonconstant

theorem nativeFiniteLaw_constant {ι : Type*} [Fintype ι] (w u : ι → ℝ)
    (hw₁ : ∑ i, w i = 1) (hConstant : ∀ i, u i = 1) (P : ℝ) :
    nativeFiniteFunctional P w u = 0 := by
  simp [nativeFiniteFunctional,hConstant,hw₁,nativeEntropyCost_unit]

end ACS12.NativeCells

import ACS12.NativeEntropyCore
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! One affine probability escort gives the common finite-law entropy account. -/
namespace ACS12.NativeCells

open Finset
set_option backward.isDefEq.respectTransparency false

noncomputable def escortDensity (c u : ℝ) : ℝ := c * u + (1 - c)

noncomputable def escortAtom (P c : ℝ) (j : ℝ → ℝ) (u : ℝ) : ℝ :=
  j u + escortDensity c u * Real.log u -
    P * escortDensity c u * Real.log (escortDensity c u) -
    (1 - P * c) * (u - 1)

theorem escortDensity_mean {ι : Type*} [Fintype ι] (w u : ι → ℝ)
    (hw : ∑ i, w i = 1) (hu : ∑ i, w i * u i = 1) (c : ℝ) :
    ∑ i, w i * escortDensity c (u i) = 1 := by
  have hTerm (i : ι) : w i * escortDensity c (u i) =
      c * (w i * u i) + (1 - c) * w i := by
    unfold escortDensity
    ring
  simp only [hTerm,sum_add_distrib,← mul_sum,hw,hu,mul_one]
  ring

theorem escortDensity_pos {c u : ℝ} (hc : 0 ≤ c) (hc₁ : c < 1) (hu : 0 ≤ u) :
    0 < escortDensity c u :=
  add_pos_of_nonneg_of_pos (mul_nonneg hc hu) (sub_pos.mpr hc₁)

theorem escort_root_moment_pos {ι : Type*} [Fintype ι] {P : ℝ} (w u : ι → ℝ)
    (hw : ∀ i, 0 < w i) (hw₁ : ∑ i, w i = 1) (hu : ∀ i, 0 < u i) :
    0 < ∑ i, w i * u i ^ (1 / P) := by
  have hNon : (univ : Finset ι).Nonempty := by
    by_contra h
    have hEmpty := Finset.not_nonempty_iff_eq_empty.mp h
    have h := hw₁
    rw [hEmpty,sum_empty] at h
    norm_num at h
  exact sum_pos (fun i _ => mul_pos (hw i) (Real.rpow_pos_of_pos (hu i) _)) hNon

theorem escort_log_mean_lower {ι : Type*} [Fintype ι] (w u : ι → ℝ)
    {P c : ℝ} (hP : 0 < P) (hw : ∀ i, 0 < w i) (hw₁ : ∑ i, w i = 1)
    (hu : ∀ i, 0 < u i) (hu₁ : ∑ i, w i * u i = 1)
    (hDensity : ∀ i, 0 < escortDensity c (u i)) :
    (∑ i, w i * (escortDensity c (u i) * Real.log (u i) -
      P * escortDensity c (u i) * Real.log (escortDensity c (u i)))) ≤
      P * Real.log (∑ i, w i * u i ^ (1 / P)) := by
  let q (i : ι) := w i * escortDensity c (u i)
  let X (i : ι) := u i ^ (1 / P) / escortDensity c (u i)
  have hq (i : ι) (_ : i ∈ univ) : 0 ≤ q i := (mul_pos (hw i) (hDensity i)).le
  have hq₁ : ∑ i, q i = 1 := escortDensity_mean w u hw₁ hu₁ c
  have hX (i : ι) (_ : i ∈ univ) : X i ∈ Set.Ioi (0 : ℝ) :=
    div_pos (Real.rpow_pos_of_pos (hu i) _) (hDensity i)
  have hJ := strictConcaveOn_log_Ioi.concaveOn.le_map_sum hq hq₁ hX
  simp only [smul_eq_mul] at hJ
  have hMoment : (∑ i, q i * X i) = ∑ i, w i * u i ^ (1 / P) := by
    apply sum_congr rfl
    intro i _
    dsimp only [q,X]
    field_simp [(hDensity i).ne']
  rw [hMoment] at hJ
  have hScaled := mul_le_mul_of_nonneg_left hJ hP.le
  rw [mul_sum] at hScaled
  have hTerm (i : ι) : P * (q i * Real.log (X i)) =
      w i * (escortDensity c (u i) * Real.log (u i) -
        P * escortDensity c (u i) * Real.log (escortDensity c (u i))) := by
    dsimp only [q,X]
    rw [Real.log_div (Real.rpow_pos_of_pos (hu i) _).ne' (hDensity i).ne',Real.log_rpow (hu i)]
    field_simp [hP.ne']
    <;> ring
  simpa only [hTerm] using hScaled

theorem escort_atom_mean {ι : Type*} [Fintype ι] (w u : ι → ℝ)
    (hw₁ : ∑ i, w i = 1) (hu₁ : ∑ i, w i * u i = 1)
    (P c : ℝ) (j : ℝ → ℝ) :
    (∑ i, w i * escortAtom P c j (u i)) =
      (∑ i, w i * j (u i)) +
      ∑ i, w i * (escortDensity c (u i) * Real.log (u i) -
        P * escortDensity c (u i) * Real.log (escortDensity c (u i))) := by
  have hLinear : ∑ i, w i * (u i - 1) = 0 := by
    simp only [mul_sub,mul_one,sum_sub_distrib,hu₁,hw₁,sub_self]
  have hTerm (i : ι) : w i * escortAtom P c j (u i) =
      w i * j (u i) +
        w i * (escortDensity c (u i) * Real.log (u i) -
          P * escortDensity c (u i) * Real.log (escortDensity c (u i))) -
        (1 - P * c) * (w i * (u i - 1)) := by
    unfold escortAtom
    ring
  simp only [hTerm,sum_sub_distrib,sum_add_distrib,← mul_sum,hLinear,mul_zero,sub_zero]

theorem escort_entropy_identity {ι : Type*} [Fintype ι] (w u : ι → ℝ)
    {P c : ℝ} (hP : 0 < P) (hw : ∀ i, 0 < w i) (hw₁ : ∑ i, w i = 1)
    (hu : ∀ i, 0 < u i) (hu₁ : ∑ i, w i * u i = 1)
    (hDensity : ∀ i, 0 < escortDensity c (u i)) (j : ℝ → ℝ) :
    P * Real.log (∑ i, w i * u i ^ (1 / P)) + (∑ i, w i * j (u i)) =
      (∑ i, w i * escortAtom P c j (u i)) +
        P * ∑ i, w i * escortDensity c (u i) *
          Real.log (escortDensity c (u i) * (∑ k, w k * u k ^ (1 / P)) / u i ^ (1 / P)) := by
  let M := ∑ i, w i * u i ^ (1 / P)
  have hM : 0 < M := escort_root_moment_pos w u hw hw₁ hu
  have hMean := escortDensity_mean w u hw₁ hu₁ c
  have hAtomMean := escort_atom_mean w u hw₁ hu₁ P c j
  have hTerm (i : ι) :
      P * (w i * escortDensity c (u i) * Real.log (escortDensity c (u i) * M / u i ^ (1 / P))) =
        (P * Real.log M) * (w i * escortDensity c (u i)) -
          w i * (escortDensity c (u i) * Real.log (u i) -
            P * escortDensity c (u i) * Real.log (escortDensity c (u i))) := by
    rw [Real.log_div (mul_pos (hDensity i) hM).ne' (Real.rpow_pos_of_pos (hu i) _).ne',
      Real.log_mul (hDensity i).ne' hM.ne',Real.log_rpow (hu i)]
    field_simp [hP.ne']
    <;> ring
  have hRemainder :
      P * (∑ i, w i * escortDensity c (u i) * Real.log (escortDensity c (u i) * M / u i ^ (1 / P))) =
        P * Real.log M -
          ∑ i, w i * (escortDensity c (u i) * Real.log (u i) -
            P * escortDensity c (u i) * Real.log (escortDensity c (u i))) := by
    rw [mul_sum]
    simp only [hTerm,sum_sub_distrib,← mul_sum,hMean,mul_one]
  change P * Real.log M + (∑ i, w i * j (u i)) = _
  change P * Real.log M + (∑ i, w i * j (u i)) =
    (∑ i, w i * escortAtom P c j (u i)) +
      P * (∑ i, w i * escortDensity c (u i) * Real.log (escortDensity c (u i) * M / u i ^ (1 / P)))
  rw [hRemainder,hAtomMean]
  ring

theorem escort_entropy_lower {ι : Type*} [Fintype ι] (w u : ι → ℝ)
    {P c : ℝ} (hP : 0 < P) (hw : ∀ i, 0 < w i) (hw₁ : ∑ i, w i = 1)
    (hu : ∀ i, 0 < u i) (hu₁ : ∑ i, w i * u i = 1)
    (hDensity : ∀ i, 0 < escortDensity c (u i)) (j : ℝ → ℝ) :
    (∑ i, w i * escortAtom P c j (u i)) ≤
      P * Real.log (∑ i, w i * u i ^ (1 / P)) + ∑ i, w i * j (u i) := by
  rw [escort_atom_mean w u hw₁ hu₁ P c j]
  have h := escort_log_mean_lower w u hP hw hw₁ hu hu₁ hDensity
  linarith only [h]

theorem mean_one_ratio_support {ι : Type*} [Fintype ι] (w u : ι → ℝ)
    {R : ℝ} (hR : 0 < R) (hw : ∀ i, 0 ≤ w i) (hw₁ : ∑ i, w i = 1)
    (hu₁ : ∑ i, w i * u i = 1) (hRatio : ∀ i j, u i ≤ R * u j) (i : ι) :
    1 / R ≤ u i ∧ u i ≤ R := by
  have hLower := sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
    mul_le_mul_of_nonneg_left (hRatio j i) (hw j))
  have hUpper := sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
    mul_le_mul_of_nonneg_left (hRatio i j) (hw j))
  have hConst : (∑ j, w j * (R * u i)) = R * u i := by
    rw [← sum_mul,hw₁,one_mul]
  have hVariable : (∑ j, w j * (R * u j)) = R := by
    calc
      _ = R * ∑ j, w j * u j := by rw [mul_sum]; apply sum_congr rfl; intro j _; ring
      _ = R := by rw [hu₁,mul_one]
  rw [hu₁,hConst] at hLower
  rw [← sum_mul,hw₁,one_mul,hVariable] at hUpper
  exact ⟨(div_le_iff₀ hR).mpr (by nlinarith only [hLower]),hUpper⟩

end ACS12.NativeCells

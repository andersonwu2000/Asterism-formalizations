import ACS12.Angular
import Mathlib.Analysis.Complex.Basic

/-! The two- and three-site controllers used before the occupied fourth edge. -/

namespace ACS12.Configuration

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem chord_coefficients_zero {n : ℕ} {p : ℝ} (F : Configuration n p)
    {i j k : Fin n} (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j)
    {a b : ℝ} (h : a • (F.position j - F.position i) + b • (F.position k - F.position i) = 0) :
    a = 0 ∧ b = 0 := by
  let d := F.position j - F.position i
  let e := F.position k - F.position i
  have hd : d ≠ 0 := sub_ne_zero.mpr (F.distinct.ne hji)
  have he : e ≠ 0 := sub_ne_zero.mpr (F.distinct.ne hki)
  change a • d + b • e = 0 at h
  have hb : b = 0 := by
    by_contra hn
    let t := -a / b
    have hc : b • e = (-a) • d := by
      rw [neg_smul, eq_neg_iff_add_eq_zero, add_comm]
      exact h
    have hline : e = t • d := by
      calc
        e = b⁻¹ • (b • e) := by rw [smul_smul, inv_mul_cancel₀ hn, one_smul]
        _ = t • d := by rw [hc, smul_smul]; congr 1; dsimp [t]; ring
    have hj := F.radial_chord i j
    have hk := F.radial_chord i k
    change (d * star (F.position i - F.center)).re = -‖d‖ ^ 2 / 2 at hj
    change (e * star (F.position i - F.center)).re = -‖e‖ ^ 2 / 2 at hk
    rw [hline, smul_mul_assoc, Complex.smul_re, smul_eq_mul, Complex.real_smul (x := t) (z := d), norm_mul, Complex.norm_real, hj, mul_pow,
      Real.norm_eq_abs, sq_abs] at hk
    have ht : t * (t - 1) = 0 := by
      apply (mul_eq_zero.mp (show (t * (t - 1)) * ‖d‖ ^ 2 = 0 by linarith)).resolve_right
      exact pow_ne_zero _ (norm_ne_zero_iff.mpr hd)
    rcases mul_eq_zero.mp ht with hzero | hone
    · exact he (by rw [hline, hzero, zero_smul])
    · have h1 : t = 1 := by linarith
      rw [h1, one_smul] at hline
      change F.position k - F.position i = F.position j - F.position i at hline
      exact hkj (F.distinct ((sub_left_inj).mp hline))
  rw [hb, zero_smul, add_zero, smul_eq_zero] at h
  exact ⟨h.resolve_right hd, hb⟩

private theorem weighted_displacements {n : ℕ} {p : ℝ} (F : Configuration n p) (i : Fin n) :
    (∑ j ∈ Finset.univ.erase i, F.mass j • (F.position j - F.position i)) =
      -(∑ j, F.mass j) • (F.position i - F.center) := by
  have hfull (j : Fin n) : F.mass j • (F.position j - F.position i) =
      F.mass j • (F.position j - F.center) - F.mass j • (F.position i - F.center) := by
    rw [← smul_sub, sub_sub_sub_cancel_right]
  calc
    _ = ∑ j, F.mass j • (F.position j - F.position i) := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      simp only [sub_self, smul_zero, add_zero]
    _ = _ := by
      simp only [hfull, Finset.sum_sub_distrib, F.centered, ← Finset.sum_smul, zero_sub, neg_smul]

private theorem coefficient_equation {n : ℕ} {p : ℝ} (F : Configuration n p)
    [Nonempty (Fin n)] (i : Fin n) :
    let c := F.coefficient / ∑ j, F.mass j
    (∑ j ∈ Finset.univ.erase i,
      (F.mass j / ‖F.position j - F.position i‖ ^ (p + 2) - c * F.mass j) •
        (F.position j - F.position i)) = 0 := by
  dsimp only
  let M := ∑ j, F.mass j
  let c := F.coefficient / M
  have hM : 0 < M := Finset.sum_pos (fun j _ => F.mass_pos j) Finset.univ_nonempty
  have hc : c * (-M) = -F.coefficient := by dsimp [c]; field_simp [hM.ne']
  simp only [sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum]
  change (∑ j ∈ Finset.univ.erase i, forceTerm p (F.mass j) (F.position j - F.position i)) -
    c • (∑ j ∈ Finset.univ.erase i, F.mass j • (F.position j - F.position i)) = 0
  rw [F.central, F.weighted_displacements, smul_smul, hc, sub_self]

private theorem two_sites_equal_mass {p : ℝ} (F : Configuration 2 p) :
    F.mass 0 = F.mass 1 := by
  have h₀ := F.radial_row 0
  have h₁ := F.radial_row 1
  have E₀ : (Finset.univ.erase (0 : Fin 2)) = {1} := by decide
  have E₁ : (Finset.univ.erase (1 : Fin 2)) = {0} := by decide
  rw [E₀, Finset.sum_singleton] at h₀
  rw [E₁, Finset.sum_singleton, norm_sub_rev] at h₁
  have hD := (Real.rpow_pos_of_pos (F.chord_pos (by decide : (1 : Fin 2) ≠ 0)) p).ne'
  exact (div_left_inj' hD).mp (h₁.trans h₀.symm)

theorem two_sites_regular {p : ℝ} (F : Configuration 2 p) (hp : 0 ≤ p) : IsEqualMassRegular F := by
  apply F.equal_mass_regular (by omega) hp (F.mass_pos 0)
  intro i
  fin_cases i
  · rfl
  · exact F.two_sites_equal_mass.symm

private theorem three_sites_same_chord {p : ℝ} (F : Configuration 3 p) (hp : 0 ≤ p)
    (i j k : Fin 3) (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j) :
    ‖F.position j - F.position i‖ = ‖F.position k - F.position i‖ := by
  have hE : Finset.univ.erase i = {j,k} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl
      · exact Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩
      · exact Finset.mem_erase.mpr ⟨hki, Finset.mem_univ _⟩
    · simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin, Finset.card_pair hkj.symm]
      decide
  have h := F.coefficient_equation i
  dsimp only at h
  rw [hE, Finset.sum_pair hkj.symm] at h
  obtain ⟨ha, hb⟩ := F.chord_coefficients_zero hji hki hkj h
  have hd := F.chord_pos hji
  have he := F.chord_pos hki
  have hc₁ : (‖F.position j - F.position i‖ ^ (p + 2))⁻¹ =
      F.coefficient / ∑ l, F.mass l := by
    apply mul_left_cancel₀ (F.mass_pos j).ne'
    rw [← div_eq_mul_inv]
    linarith [ha]
  have hc₂ : (‖F.position k - F.position i‖ ^ (p + 2))⁻¹ =
      F.coefficient / ∑ l, F.mass l := by
    apply mul_left_cancel₀ (F.mass_pos k).ne'
    rw [← div_eq_mul_inv]
    linarith [hb]
  exact (Real.rpow_left_inj hd.le he.le (by linarith : p + 2 ≠ 0)).mp
    (inv_inj.mp (hc₁.trans hc₂.symm))

theorem three_sites_regular {p : ℝ} (F : Configuration 3 p) (hp : 0 ≤ p) : IsEqualMassRegular F := by
  let d := ‖F.position 1 - F.position 0‖
  have hd : 0 < d := F.chord_pos (by decide : (1 : Fin 3) ≠ 0)
  have h01 : ‖F.position 0 - F.position 1‖ = d := norm_sub_rev _ _
  have h20 : ‖F.position 2 - F.position 0‖ = d :=
    (F.three_sites_same_chord hp 0 1 2 (by decide) (by decide) (by decide)).symm
  have h21 : ‖F.position 2 - F.position 1‖ = d :=
    (F.three_sites_same_chord hp 1 2 0 (by decide) (by decide) (by decide)).trans h01
  have h02 : ‖F.position 0 - F.position 2‖ = d := (norm_sub_rev _ _).trans h20
  have h12 : ‖F.position 1 - F.position 2‖ = d := (norm_sub_rev _ _).trans h21
  have h₀ := F.radial_row 0
  have h₁ := F.radial_row 1
  have h₂ := F.radial_row 2
  have E₀ : (Finset.univ.erase (0 : Fin 3)) = {1,2} := by decide
  have E₁ : (Finset.univ.erase (1 : Fin 3)) = {0,2} := by decide
  have E₂ : (Finset.univ.erase (2 : Fin 3)) = {0,1} := by decide
  rw [E₀, Finset.sum_pair (by decide), h20] at h₀
  rw [E₁, Finset.sum_pair (by decide), h01, h21] at h₁
  rw [E₂, Finset.sum_pair (by decide), h02, h12] at h₂
  change F.mass 1 / d ^ p + F.mass 2 / d ^ p = _ at h₀
  have hD := (Real.rpow_pos_of_pos hd p).ne'
  apply F.equal_mass_regular (by omega) hp (F.mass_pos 0)
  intro i
  fin_cases i
  · rfl
  · change F.mass 1 = F.mass 0
    apply (div_left_inj' hD).mp
    linarith
  · change F.mass 2 = F.mass 0
    apply (div_left_inj' hD).mp
    linarith

end ACS12.Configuration

import ACS12.Physical
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Exact mass and length rescaling of the original force equations to the high-source unit rows. -/
namespace ACS12
set_option backward.isDefEq.respectTransparency false

theorem forceTerm_rescale {α s r m : ℝ} (hr : 0 < r) {d : ℂ} (hd : 0 < ‖d‖) :
    forceTerm α (s * m) (r • d) = (s * r / r ^ (α + 2)) • forceTerm α m d := by
  unfold forceTerm
  rw [norm_smul,Real.norm_of_nonneg hr.le,Real.mul_rpow hr.le hd.le,smul_smul,smul_smul]
  congr 1
  field_simp [(Real.rpow_pos_of_pos hr (α + 2)).ne',(Real.rpow_pos_of_pos hd (α + 2)).ne']
  <;> ring

namespace Configuration

variable {n : ℕ} {α : ℝ}

noncomputable def rescale (F : Configuration n α) (s r : ℝ) (hs : 0 < s) (hr : 0 < r) :
    Configuration n α where
  mass i := s * F.mass i
  position i := r • (F.position i - F.center)
  center := 0
  radius := r * F.radius
  coefficient := s * F.coefficient / r ^ (α + 2)
  mass_pos i := mul_pos hs (F.mass_pos i)
  radius_pos := mul_pos hr F.radius_pos
  distinct := by
    intro i j h
    have hCancel := congrArg (fun z : ℂ => r⁻¹ • z) h
    simp only [smul_smul,inv_mul_cancel₀ hr.ne',one_smul] at hCancel
    exact F.distinct (sub_left_inj.mp hCancel)
  on_circle i := by
    simp only [sub_zero,norm_smul,Real.norm_of_nonneg hr.le,F.on_circle]
  centered := by
    simp only [sub_zero]
    have hTerm (i : Fin n) : (s * F.mass i) • (r • (F.position i - F.center)) =
        (s * r) • (F.mass i • (F.position i - F.center)) := by
      simp only [smul_smul]
      congr 1
      ring
    simp_rw [hTerm]
    rw [← Finset.smul_sum,F.centered,smul_zero]
  central i := by
    simp only [sub_zero,← smul_sub,sub_sub_sub_cancel_right]
    have hTerm (j : Fin n) (hj : j ∈ Finset.univ.erase i) :
        forceTerm α (s * F.mass j) (r • (F.position j - F.position i)) =
          (s * r / r ^ (α + 2)) • forceTerm α (F.mass j) (F.position j - F.position i) :=
      forceTerm_rescale hr (F.chord_pos (Finset.mem_erase.mp hj).1)
    rw [Finset.sum_congr rfl hTerm,← Finset.smul_sum,F.central,smul_smul,smul_smul]
    congr 1
    ring

noncomputable def radialUnitScale (F : Configuration n α) (o : Fin n) : ℝ :=
  (2 * F.coefficient * F.radius ^ 2 / F.mass o) ^ (1 / α)

noncomputable def radialUnitSource (F : Configuration n α) (hn : 2 ≤ n) (o : Fin n) :
    Configuration n α :=
  F.rescale (F.mass o)⁻¹ (F.radialUnitScale o) (inv_pos.mpr (F.mass_pos o))
    (Real.rpow_pos_of_pos (div_pos
      (mul_pos (mul_pos (by norm_num) (F.coefficient_pos hn)) (sq_pos_of_pos F.radius_pos))
      (F.mass_pos o)) _)

theorem radialUnitScale_pow (F : Configuration n α) (hn : 2 ≤ n) (hα : 0 < α) (o : Fin n) :
    F.radialUnitScale o ^ α = 2 * F.coefficient * F.radius ^ 2 / F.mass o := by
  have hBase : 0 < 2 * F.coefficient * F.radius ^ 2 / F.mass o := div_pos
    (mul_pos (mul_pos (by norm_num) (F.coefficient_pos hn)) (sq_pos_of_pos F.radius_pos)) (F.mass_pos o)
  unfold radialUnitScale
  rw [← Real.rpow_mul hBase.le,one_div_mul_cancel hα.ne',Real.rpow_one]

theorem radialUnitSource_mass (F : Configuration n α) (hn : 2 ≤ n) (o i : Fin n) :
    (F.radialUnitSource hn o).mass i = F.mass i / F.mass o := by
  unfold radialUnitSource rescale
  ring

theorem radialUnitSource_root (F : Configuration n α) (hn : 2 ≤ n) (o : Fin n) :
    (F.radialUnitSource hn o).mass o = 1 := by
  rw [radialUnitSource_mass,div_self (F.mass_pos o).ne']

theorem radialUnitSource_maximum (F : Configuration n α) (hn : 2 ≤ n) (o : Fin n)
    (hMax : ∀ i, F.mass i ≤ F.mass o) (i : Fin n) :
    (F.radialUnitSource hn o).mass i ≤ 1 := by
  rw [radialUnitSource_mass]
  exact (div_le_one (F.mass_pos o)).mpr (hMax i)

theorem radialUnitSource_radial (F : Configuration n α) (hn : 2 ≤ n) (hα : 0 < α) (o i : Fin n) :
    (∑ j ∈ Finset.univ.erase i, (F.radialUnitSource hn o).mass j /
      ‖(F.radialUnitSource hn o).position j - (F.radialUnitSource hn o).position i‖ ^ α) = 1 := by
  let r := F.radialUnitScale o
  have hr : 0 < r := Real.rpow_pos_of_pos (div_pos
    (mul_pos (mul_pos (by norm_num) (F.coefficient_pos hn)) (sq_pos_of_pos F.radius_pos)) (F.mass_pos o)) _
  rw [(F.radialUnitSource hn o).radial_row]
  change 2 * ((F.mass o)⁻¹ * F.coefficient / r ^ (α + 2)) * (r * F.radius) ^ 2 = 1
  rw [Real.rpow_add hr,Real.rpow_two,F.radialUnitScale_pow hn hα o]
  field_simp [(F.mass_pos o).ne',hr.ne',(F.coefficient_pos hn).ne',F.radius_pos.ne']
  <;> ring

theorem radialUnitSource_upper_chord (F : Configuration n α) (hn : 2 ≤ n) (hα : 0 < α)
    (o i j : Fin n) (hji : j ≠ i) :
    (F.radialUnitSource hn o).mass j ≤
      ‖(F.radialUnitSource hn o).position j - (F.radialUnitSource hn o).position i‖ ^ α := by
  let G := F.radialUnitSource hn o
  have hPos := Real.rpow_pos_of_pos (G.chord_pos hji) α
  have hTerm : G.mass j / ‖G.position j - G.position i‖ ^ α ≤ 1 := by
    have h := Finset.single_le_sum
      (f := fun k => G.mass k / ‖G.position k - G.position i‖ ^ α)
      (fun k hk => div_nonneg (G.mass_pos k).le
        (Real.rpow_nonneg (norm_nonneg _) _)) (Finset.mem_erase.mpr ⟨hji,Finset.mem_univ j⟩)
    rw [F.radialUnitSource_radial hn hα o i] at h
    exact h
  exact (div_le_one hPos).mp hTerm

end Configuration
end ACS12



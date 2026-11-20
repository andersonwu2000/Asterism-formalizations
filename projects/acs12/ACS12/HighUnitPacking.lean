import ACS12.HighUnitGeometry
import ACS12.Angular
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Unit-row physical chord exclusion and the complete finite interval capacity. -/
namespace ACS12

open Finset Set CenteredCircle.AllN
set_option backward.isDefEq.respectTransparency false

theorem unitRay_chord_le (x y : ℝ) : ‖unitRay x - unitRay y‖ ≤ |x - y| := by
  have hId : (unitRay (x - y) - 1) * unitRay y = unitRay x - unitRay y := by
    rw [sub_mul,one_mul,← unitRay_add,sub_add_cancel]
  have hE := Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y)
  have hExp : Complex.exp (Complex.I * ((x - y : ℝ) : ℂ)) = unitRay (x - y) := by
    unfold unitRay
    rw [mul_comm]
  rw [hExp,Real.norm_eq_abs] at hE
  rw [← hId,norm_mul,norm_unitRay,mul_one]
  exact hE

namespace Configuration

variable {n : ℕ} {α : ℝ} (F : Configuration n α)

theorem chord_le_phase_arc (i j : Fin n) :
    ‖F.position j - F.position i‖ ≤ F.radius * |F.phase j - F.phase i| := by
  rw [F.phase_eq i,F.phase_eq j,add_sub_add_left_eq_sub,← mul_sub,norm_mul,
    Complex.norm_real,Real.norm_of_nonneg F.radius_pos.le]
  exact mul_le_mul_of_nonneg_left (unitRay_chord_le _ _) F.radius_pos.le

theorem radialUnitSource_mass_le_chord (hn : 2 ≤ n) (hα : 1 ≤ α) (o : Fin n)
    (hMax : ∀ i, F.mass i ≤ F.mass o) (i j : Fin n) (hji : j ≠ i) :
    (F.radialUnitSource hn o).mass j ≤
      ‖(F.radialUnitSource hn o).position j - (F.radialUnitSource hn o).position i‖ := by
  let G := F.radialUnitSource hn o
  have hα₀ : 0 < α := zero_lt_one.trans_le hα
  have hUpper := F.radialUnitSource_upper_chord hn hα₀ o i j hji
  have hMax₁ := F.radialUnitSource_maximum hn o hMax j
  by_cases hd : ‖G.position j - G.position i‖ ≤ 1
  · have hPow : ‖G.position j - G.position i‖ ^ α ≤ ‖G.position j - G.position i‖ := by
      have h := Real.rpow_le_rpow_of_exponent_ge (G.chord_pos hji) hd hα
      simpa only [Real.rpow_one] using h
    exact hUpper.trans hPow
  · exact hMax₁.trans (le_of_not_ge hd)

theorem radialUnitSource_mass_le_phase_arc (hn : 2 ≤ n) (hα : 1 ≤ α) (o : Fin n)
    (hMax : ∀ i, F.mass i ≤ F.mass o) (i j : Fin n) (hji : j ≠ i) :
    (F.radialUnitSource hn o).mass j ≤ (F.radialUnitSource hn o).radius *
      |(F.radialUnitSource hn o).phase j - (F.radialUnitSource hn o).phase i| :=
  (F.radialUnitSource_mass_le_chord hn hα o hMax i j hji).trans
    ((F.radialUnitSource hn o).chord_le_phase_arc i j)

end Configuration

theorem finite_interval_capacity {ι : Type*} [DecidableEq ι]
    (t m : ι → ℝ) (S : Finset ι) {a b : ℝ} (hab : a ≤ b)
    (hm : ∀ i ∈ S, m i ≤ 1) (hDom : ∀ i ∈ S, t i ∈ Icc a b)
    (hSep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → m j ≤ |t j - t i|) :
    ∑ i ∈ S, m i ≤ 1 + b - a := by
  suffices hStrong : ∀ (T : Finset ι), T ⊆ S → ∀ c : ℝ, c ≤ b →
      (∀ i ∈ T, c ≤ t i) → (∑ i ∈ T, m i) ≤ 1 + b - c by
    exact hStrong S Finset.Subset.rfl a hab (fun i hi => (hDom i hi).1)
  intro T
  induction T using Finset.strongInductionOn
  rename_i T ih
  intro hTS c hc hLower
  by_cases hT : T.Nonempty
  · obtain ⟨i,hi,hiMin⟩ := T.exists_min_image t hT
    by_cases hTail : (T.erase i).Nonempty
    · obtain ⟨j,hj,hjMin⟩ := (T.erase i).exists_min_image t hTail
      have hji : j ≠ i := (mem_erase.mp hj).1
      have hjT := mem_of_mem_erase hj
      have hPaid := hSep j (hTS hjT) i (hTS hi) hji
      rw [abs_of_nonpos (sub_nonpos.mpr (hiMin j hjT)),neg_sub] at hPaid
      have hRest := ih (T.erase i) (erase_ssubset hi)
        (fun k hk => hTS (mem_of_mem_erase hk)) (t j) (hDom j (hTS hjT)).2 hjMin
      rw [← sum_erase_add T m hi]
      linarith only [hPaid,hRest,hLower i hi]
    · have hEmpty : T.erase i = ∅ := not_nonempty_iff_eq_empty.mp hTail
      rw [← sum_erase_add T m hi,hEmpty,sum_empty,zero_add]
      have hBounds := hDom i (hTS hi)
      linarith only [hm i (hTS hi),hBounds.2,hLower i hi]
  · have hEmpty : T = ∅ := not_nonempty_iff_eq_empty.mp hT
    rw [hEmpty,sum_empty]
    linarith only [hc]

namespace Configuration

theorem radialUnitSource_interval_capacity {n : ℕ} {α : ℝ} (F : Configuration n α)
    (hn : 2 ≤ n) (hα : 1 ≤ α) (o : Fin n) (hMax : ∀ i, F.mass i ≤ F.mass o)
    (S : Finset (Fin n)) {a b : ℝ} (hab : a ≤ b)
    (hDom : ∀ i ∈ S, (F.radialUnitSource hn o).radius * (F.radialUnitSource hn o).phase i ∈ Icc a b) :
    (∑ i ∈ S, (F.radialUnitSource hn o).mass i) ≤ 1 + b - a := by
  let G := F.radialUnitSource hn o
  apply finite_interval_capacity (fun i => G.radius * G.phase i) G.mass S hab
    (fun i _ => F.radialUnitSource_maximum hn o hMax i) hDom
  intro i _ j _ hji
  have h := F.radialUnitSource_mass_le_phase_arc hn hα o hMax i j hji.symm
  rw [← mul_sub,abs_mul,abs_of_pos G.radius_pos]
  exact h

end Configuration

end ACS12

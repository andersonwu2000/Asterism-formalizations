import ACS12.HighPhysicalReweight

/-! The original unit row supplies the full fourth-kernel reweighted mass moment. -/
namespace ACS12.Configuration

open Finset HighCurrent Pressure
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {p : ℝ} (F : ACS12.Configuration n p)

theorem radialUnitSource_reweightedTotal_holder (hn : 2 ≤ n) (hp : 4 ≤ p) (o : Fin n) :
    let G := F.radialUnitSource hn o
    G.currentReweightedTotal (G.currentOrder.symm o) ≤ (massTotal G.mass - 1) ^ (4 / p) := by
  let G := F.radialUnitSource hn o
  let r := G.currentOrder.symm o
  have hp₀ : 0 < p := by linarith only [hp]
  have hRoot : G.currentMasses r = 1 := by
    simp only [currentMasses,Function.comp_apply,r,Equiv.apply_symm_apply]
    exact F.radialUnitSource_root hn o
  have hU : (∑ j ∈ univ.erase r, G.currentMasses j) = massTotal G.mass - 1 := by
    rw [sum_erase_eq_sub (mem_univ r),hRoot]
    exact congrArg (fun v : ℝ => v - 1) (Equiv.sum_comp G.currentOrder G.mass)
  have hM := F.radialUnitSource_totalMass_ge_two hn o
  have hU₀ : 0 < ∑ j ∈ univ.erase r, G.currentMasses j := by
    rw [hU]
    linarith only [hM]
  have hLevel : 2 * G.coefficient * G.radius ^ (2 : ℕ) = 1 := by
    rw [← G.radial_row o]
    exact F.radialUnitSource_radial hn hp₀ o o
  have hC : (∑ j ∈ univ.erase r, G.currentMasses j * G.currentChord r j ^ (-p)) = 1 := by
    calc
      _ = ∑ j ∈ univ.erase r, G.currentReweightedMass r j / G.currentChord r j ^ (4 : ℕ) := by
        apply sum_congr rfl
        intro j hj
        rw [G.currentReweighted_row_identity (mem_erase.mp hj).1,Real.rpow_neg (G.currentChord_pos (mem_erase.mp hj).1).le]
        ring
      _ = 1 := by rw [G.currentReweighted_radial,hLevel]
  have h := reweighted_total_mass_bound (univ.erase r) G.currentMasses (G.currentChord r)
    (fun j _ => G.mass_pos (G.currentOrder j)) (fun j hj => G.currentChord_pos (mem_erase.mp hj).1) hU₀ hp
  rw [hU,hC,Real.one_rpow,mul_one] at h
  exact h

end ACS12.Configuration

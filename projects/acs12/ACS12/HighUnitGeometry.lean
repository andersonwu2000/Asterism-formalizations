import ACS12.HighUnitNormalization
import ACS12.SourceMassMoment

/-! Original centered geometry supplies the exact unit-root chord and total-mass entrances. -/
namespace ACS12.Configuration

open Finset Pressure

variable {n : ℕ} {α : ℝ} (F : Configuration n α)

theorem radialUnitSource_root_chord (hn : 2 ≤ n) (hα : 0 < α) (o j : Fin n) (hjo : j ≠ o) :
    1 ≤ ‖(F.radialUnitSource hn o).position j - (F.radialUnitSource hn o).position o‖ := by
  let G := F.radialUnitSource hn o
  have h := F.radialUnitSource_upper_chord hn hα o j o hjo.symm
  rw [F.radialUnitSource_root hn o,norm_sub_rev] at h
  change 1 ≤ ‖G.position j - G.position o‖ ^ α at h
  by_contra! hBad
  have hPow : ‖G.position j - G.position o‖ ^ α < 1 :=
    Real.rpow_lt_one (G.chord_pos hjo).le hBad hα
  exact (not_lt_of_ge h) hPow

theorem radialUnitSource_totalMass_ge_two (hn : 2 ≤ n) (o : Fin n) :
    2 ≤ massTotal (F.radialUnitSource hn o).mass := by
  let G := F.radialUnitSource hn o
  have hRoot : G.mass o = 1 := F.radialUnitSource_root hn o
  have hMoment := G.diameterChordSq_centered_sum o o
  rw [hRoot,div_one] at hMoment
  simp only [div_one] at hMoment
  have hBound : (∑ j ∈ univ.erase o, G.mass j * G.diameterChordSq o j) ≤ ∑ j ∈ univ.erase o, G.mass j :=
    sum_le_sum (fun j _ => mul_le_of_le_one_right (G.mass_pos j).le (G.diameterChordSq_le_one o j))
  rw [hMoment,sum_erase_eq_sub (mem_univ o),hRoot] at hBound
  change massTotal G.mass / 2 ≤ massTotal G.mass - 1 at hBound
  linarith only [hBound]

theorem radialUnitSource_diameter_ge_one (hn : 2 ≤ n) (hα : 0 < α) (o : Fin n) :
    1 ≤ 2 * (F.radialUnitSource hn o).radius := by
  let G := F.radialUnitSource hn o
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨j,hjo⟩ := exists_ne o
  have hLow := F.radialUnitSource_root_chord hn hα o j hjo
  have hUpper := norm_sub_le (G.position j - G.center) (G.position o - G.center)
  rw [sub_sub_sub_cancel_right,G.on_circle,G.on_circle] at hUpper
  change 1 ≤ 2 * G.radius
  linarith only [hLow,hUpper]

end ACS12.Configuration

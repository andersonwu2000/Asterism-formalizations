import ACS12.HighCurrentIncident
import ACS12.HighCurrentReweight

/-! The same original physical atoms retain their exact radial and incident rows after fourth-kernel reweighting. -/
namespace ACS12.HighCurrent

theorem reweighted_row_div_identity {p m d : ℝ} (hd : 0 < d) :
    reweightedMass p m d / d ^ (4 : ℕ) = m / d ^ p := by
  have h := reweighted_row_identity (p := p) (m := m) hd
  rw [Real.rpow_neg hd.le,Real.rpow_ofNat,Real.rpow_neg hd.le] at h
  simpa only [div_eq_mul_inv] using h

end ACS12.HighCurrent

namespace ACS12.Configuration

open Finset HighCurrent
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {α : ℝ} (F : ACS12.Configuration n α)

noncomputable def currentChord (o j : Fin n) : ℝ :=
  ‖F.position (F.currentOrder j) - F.position (F.currentOrder o)‖

noncomputable def currentReweightedMass (o j : Fin n) : ℝ :=
  reweightedMass α (F.currentMasses j) (F.currentChord o j)

noncomputable def currentReweightedTotal (o : Fin n) : ℝ :=
  ∑ j ∈ univ.erase o, F.currentReweightedMass o j

theorem currentChord_pos {o j : Fin n} (hjo : j ≠ o) : 0 < F.currentChord o j :=
  F.chord_pos (F.currentOrder.injective.ne hjo)

theorem currentReweighted_row_identity {o j : Fin n} (hjo : j ≠ o) :
    F.currentReweightedMass o j / F.currentChord o j ^ (4 : ℕ) =
      F.currentMasses j / F.currentChord o j ^ α :=
  reweighted_row_div_identity (F.currentChord_pos hjo)

theorem currentReweighted_radial (o : Fin n) :
    (∑ j ∈ univ.erase o, F.currentReweightedMass o j / F.currentChord o j ^ (4 : ℕ)) =
      2 * F.coefficient * F.radius ^ 2 := by
  have hSum : (∑ j ∈ univ.erase o, F.currentMasses j / F.currentChord o j ^ α) =
      ∑ j ∈ univ.erase (F.currentOrder o),
        F.mass j / ‖F.position j - F.position (F.currentOrder o)‖ ^ α := by
    unfold currentMasses currentChord
    rw [sum_erase_eq_sub (mem_univ o),sum_erase_eq_sub (mem_univ (F.currentOrder o))]
    exact congrArg (fun v : ℝ => v -
      F.mass (F.currentOrder o) / ‖F.position (F.currentOrder o) - F.position (F.currentOrder o)‖ ^ α)
      (Equiv.sum_comp F.currentOrder (fun j => F.mass j / ‖F.position j - F.position (F.currentOrder o)‖ ^ α))
  rw [sum_congr rfl (fun j hj => F.currentReweighted_row_identity (mem_erase.mp hj).1),hSum,F.radial_row]

theorem currentReweighted_incident (o : Fin n) :
    F.currentMasses o *
      (∑ j ∈ univ.erase o, (F.currentReweightedMass o j / F.currentChord o j ^ (4 : ℕ)) * F.currentZeta o j) ≤
      2 * F.commonCurrent := by
  have hEq : F.currentMasses o *
      (∑ j ∈ univ.erase o, (F.currentReweightedMass o j / F.currentChord o j ^ (4 : ℕ)) * F.currentZeta o j) =
      ∑ j ∈ univ.erase o,
        (F.currentMasses o * F.currentMasses j / F.currentChord o j ^ α) * F.currentZeta o j := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    rw [F.currentReweighted_row_identity (mem_erase.mp hj).1]
    ring
  rw [hEq]
  exact F.current_incident_radial_bound o

end ACS12.Configuration

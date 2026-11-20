import ACS12.AngularEnergy

/-! The original full radial equations in the same angular coordinates. -/
namespace ACS12.Configuration
open Set
open CenteredCircle.AllN (unitRay)
variable {n : ℕ} {α : ℝ} (F : Configuration n α)

theorem weighted_radial_row (hα : 0 < α) (a : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (ha : StrictMono a) (ha0 : ∀ i, 0 ≤ a i) (ha2π : ∀ i, a i < 2 * Real.pi)
    (hphase : ∀ i, F.position (σ i) = F.center + (F.radius : ℂ) * unitRay (a i)) (i : Fin n) :
    (∑ j, F.mass (σ j) * angularCost α (halfArc a i j)) =
      (2 * F.radius) ^ α * (2 * F.coefficient * F.radius ^ 2) := by
  let g : Fin n → ℝ := fun j => F.mass j / ‖F.position j - F.position (σ i)‖ ^ α
  have hR := F.radius_pos
  have hterm (j : Fin n) (hj : j ∈ Finset.univ.erase i) :
      F.mass (σ j) * angularCost α (halfArc a i j) = (2 * F.radius) ^ α * g (σ j) := by
    have ht := halfArc_mem ha ha0 ha2π (Finset.mem_erase.mp hj).1
    have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
    dsimp only [g]
    rw [F.chord_eq_halfArc a σ hphase ht, angularCost, Real.mul_rpow (by positivity) hs.le]
    field_simp [(Real.rpow_pos_of_pos (show 0 < 2 * F.radius by positivity) α).ne']
  have hsum : (∑ j ∈ Finset.univ.erase i, g (σ j)) = ∑ j ∈ Finset.univ.erase (σ i), g j := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), Equiv.sum_comp σ g,
      Finset.sum_erase_eq_sub (Finset.mem_univ (σ i))]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), halfArc_self, angularCost, Real.sin_zero,
    Real.zero_rpow hα.ne', div_zero, mul_zero, add_zero, Finset.sum_congr rfl hterm, ← Finset.mul_sum, hsum]
  exact congrArg (fun x => (2 * F.radius) ^ α * x) (F.radial_row (σ i))

end ACS12.Configuration

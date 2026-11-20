import ACS12.QuarticCurrentBarycenter

/-! The physical radial and centered moments are retained in the same maximum-source measure. -/
namespace ACS12.Configuration

open Finset HighCurrent Pressure
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {p : ℝ} (F : Configuration n p)

/-- At a normalized unit-mass root the weighted mean controls the entire incident
current. The inverse moment comes from the original center-of-mass equation. -/
theorem radialUnitSource_quartic_barycenter (hn : 2 ≤ n) (hp : 4 ≤ p) (o : Fin n)
    (hH : let G := F.radialUnitSource hn o
      0 < 1 - (1 / (2 * G.radius) ^ 2) ^ 2 * G.currentReweightedTotal (G.currentOrder.symm o)) :
    let G := F.radialUnitSource hn o
    let r := G.currentOrder.symm o
    let x := 1 / (2 * G.radius) ^ 2
    let H := 1 - x ^ 2 * G.currentReweightedTotal r
    let D := ∑ j ∈ univ.erase r, G.currentReweightedMass r j * G.currentZeta r j ^ 2
    ∃ β : ℝ, x < β ∧ D * (β + x) = H ∧
      D ≤ β * ((massTotal G.mass - 2) / 2) ∧
      D * β ^ 2 / Real.sqrt (β - x) ≤ 2 * G.commonCurrent := by
  let G := F.radialUnitSource hn o
  let r := G.currentOrder.symm o
  let S := (univ : Finset (Fin n)).erase r
  let x := 1 / (2 * G.radius) ^ 2
  let ν := G.currentReweightedMass r
  let z := G.currentZeta r
  let y (j : Fin n) := x + z j ^ 2
  let H := 1 - x ^ 2 * G.currentReweightedTotal r
  have hx : 0 < x := one_div_pos.mpr (sq_pos_of_pos (mul_pos zero_lt_two G.radius_pos))
  have hp₀ : 0 < p := by linarith only [hp]
  have hRoot : G.currentMasses r = 1 := by
    simp only [currentMasses, Function.comp_apply, r, Equiv.apply_symm_apply]
    exact F.radialUnitSource_root hn o
  have hLevel : 2 * G.coefficient * G.radius ^ 2 = 1 := by
    rw [← G.radial_row o]
    exact F.radialUnitSource_radial hn hp₀ o o
  have hν (j : Fin n) (hj : j ∈ S) : 0 ≤ ν j :=
    reweightedMass_nonneg (G.mass_pos _).le (G.currentChord_pos (mem_erase.mp hj).1).le
  have hz (j : Fin n) (hj : j ∈ S) : 0 ≤ z j := G.currentZeta_nonneg (mem_erase.mp hj).1.symm
  have hy (j : Fin n) (hj : j ∈ S) : y j = 1 / G.currentChord r j ^ 2 :=
    G.currentZeta_chord_identity (mem_erase.mp hj).1.symm
  have hTerm (j : Fin n) (hj : j ∈ S) : ν j * (y j) ^ 2 = ν j / G.currentChord r j ^ 4 := by
    rw [hy j hj]
    ring
  have hMoment : (∑ j ∈ S, ν j * (y j ^ 2 - x ^ 2)) = H := by
    simp_rw [mul_sub, sum_sub_distrib, ← sum_mul]
    rw [sum_congr rfl hTerm, G.currentReweighted_radial, hLevel]
    unfold H currentReweightedTotal
    ring
  have hJ : (∑ j ∈ S, ν j * y j ^ 2 * z j) ≤ 2 * G.commonCurrent := by
    have h := G.currentReweighted_incident r
    rw [hRoot, one_mul] at h
    rw [sum_congr rfl (fun j hj => by rw [hTerm j hj])]
    exact h
  obtain ⟨β, hβ, hMomentβ, hHarm, hJβ⟩ :=
    quarticCurrent_barycenter S ν z hx.le hH hν hz hMoment hJ
  have hCap : (∑ j ∈ S, ν j * z j ^ 2 / y j) ≤ (massTotal G.mass - 2) / 2 := by
    have hPoint (j : Fin n) (hj : j ∈ S) :
        ν j * z j ^ 2 / y j ≤ G.currentMasses j * (1 - G.diameterChordSq o (G.currentOrder j)) := by
      have hjo : G.currentOrder j ≠ o := by
        intro hEq
        apply (mem_erase.mp hj).1
        apply G.currentOrder.injective
        simpa only [r, Equiv.apply_symm_apply] using hEq
      have hd := G.currentChord_pos (mem_erase.mp hj).1
      have hRootChord : 1 ≤ G.currentChord r j := by
        simpa only [currentChord, r, Equiv.apply_symm_apply] using
          F.radialUnitSource_root_chord hn hp₀ o (G.currentOrder j) hjo
      have hBound : ν j ≤ G.currentMasses j := reweightedMass_le hp (G.mass_pos _).le hRootChord
      have hScale : x * G.currentChord r j ^ 2 = G.diameterChordSq o (G.currentOrder j) := by
        simp only [x, currentChord, r, Equiv.apply_symm_apply, diameterChordSq, div_pow]
        ring
      have hQ : z j ^ 2 / y j = 1 - G.diameterChordSq o (G.currentOrder j) := by
        have hY : z j ^ 2 = y j - x := by dsimp [y]; ring
        rw [hY, hy j hj, ← hScale]
        field_simp [hd.ne']
      rw [mul_div_assoc, hQ]
      exact mul_le_mul_of_nonneg_right hBound (sub_nonneg.mpr (G.diameterChordSq_le_one _ _))
    apply (sum_le_sum hPoint).trans
    have hTotal : (∑ j ∈ S, G.currentMasses j) = massTotal G.mass - 1 := by
      unfold S
      rw [sum_erase_eq_sub (mem_univ r), hRoot]
      exact congrArg (· - 1) (Equiv.sum_comp G.currentOrder G.mass)
    have hCenter : (∑ j ∈ S, G.currentMasses j * G.diameterChordSq o (G.currentOrder j)) =
        massTotal G.mass / 2 := by
      let g (j : Fin n) := G.mass j * G.diameterChordSq o j
      have hSum : (∑ j ∈ S, g (G.currentOrder j)) = ∑ j ∈ univ.erase o, g j := by
        unfold S
        rw [sum_erase_eq_sub (mem_univ r), sum_erase_eq_sub (mem_univ o)]
        dsimp only [r]
        rw [Equiv.apply_symm_apply]
        exact congrArg (· - g o) (Equiv.sum_comp G.currentOrder g)
      rw [show (∑ j ∈ S, G.currentMasses j * G.diameterChordSq o (G.currentOrder j)) =
        ∑ j ∈ S, g (G.currentOrder j) from rfl, hSum]
      have h := G.diameterChordSq_centered_sum o o
      rw [F.radialUnitSource_root hn o, div_one] at h
      simpa only [g, div_one] using h
    simp_rw [mul_sub, mul_one, sum_sub_distrib, hTotal, hCenter]
    linarith
  exact ⟨β, hβ, hMomentβ, hHarm.trans (mul_le_mul_of_nonneg_left hCap (hx.trans hβ).le), hJβ⟩

end ACS12.Configuration

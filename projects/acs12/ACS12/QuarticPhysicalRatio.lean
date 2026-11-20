import ACS12.QuarticPhysicalHump
import ACS12.QuarticMinimumCurrent
import ACS12.QuarticRatioScalar
import ACS12.HighDirectRowRadius
import ACS12.HighPhysicalReweightedMoment

/-! The one-fifth mass ratio uses one actual minimum cut and one maximum barycenter. -/
namespace ACS12.Configuration

open Finset HighCurrent Pressure
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000

variable {n : ℕ} {p : ℝ} (F : Configuration n p)

private theorem radialUnitSource_quartic_hump_barycenter (hn : 2 ≤ n) (hp : 4 ≤ p)
    (o : Fin n) (hMax : ∀ j, F.mass j ≤ F.mass o) {β : ℝ}
    (hβ : 1 / (2 * (F.radialUnitSource hn o).radius)^2 < β)
    (hId : let G := F.radialUnitSource hn o
      let r := G.currentOrder.symm o
      let x := 1 / (2 * G.radius)^2
      (∑ j ∈ univ.erase r, G.currentReweightedMass r j * G.currentZeta r j ^ 2) * (β + x) =
        1 - x ^ 2 * G.currentReweightedTotal r) :
    let G := F.radialUnitSource hn o
    let r := G.currentOrder.symm o
    let x := 1 / (2 * G.radius)^2
    (∑ j ∈ univ.erase r, G.currentReweightedMass r j * G.currentZeta r j ^ 2) ≤
      (3 * β - x) ^ 2 / (4 * β) + 2 * Real.sqrt (3 * β) - 3 * Real.sqrt x +
        x * Real.sqrt x / (3 * β) := by
  let G := F.radialUnitSource hn o
  let r := G.currentOrder.symm o
  let S := (univ : Finset (Fin n)).erase r
  let x := 1 / (2 * G.radius)^2
  let ν := G.currentReweightedMass r
  let z := G.currentZeta r
  let y (j : Fin n) := x + z j ^ 2
  let D := ∑ j ∈ S, ν j * z j ^ 2
  let H := 1 - x ^ 2 * G.currentReweightedTotal r
  let B := 3 * β
  have hp₀ : 0 < p := by linarith only [hp]
  have hx : 0 < x := one_div_pos.mpr (sq_pos_of_pos (mul_pos zero_lt_two G.radius_pos))
  have hβ₀ : 0 < β := hx.trans hβ
  have hB : x < B := by dsimp only [B]; linarith only [hβ, hβ₀]
  have hLevel : 2 * G.coefficient * G.radius ^ 2 = 1 := by
    rw [← G.radial_row o]
    exact F.radialUnitSource_radial hn hp₀ o o
  have hTerm (j : Fin n) (hj : j ∈ S) : ν j * y j ^ 2 = ν j / G.currentChord r j ^ 4 := by
    have h := G.currentZeta_chord_identity (mem_erase.mp hj).1.symm
    change y j = 1 / G.currentChord r j ^ 2 at h
    rw [h]
    ring
  have hMoment : (∑ j ∈ S, ν j * (y j ^ 2 - x ^ 2)) = H := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul]
    rw [sum_congr rfl hTerm, G.currentReweighted_radial, hLevel]
    unfold H currentReweightedTotal
    ring
  have hDβ : (∑ j ∈ S, ν j * z j ^ 2 * y j) = D * β := by
    have hE : (∑ j ∈ S, ν j * (y j ^ 2 - x ^ 2)) =
        (∑ j ∈ S, ν j * z j ^ 2 * y j) + D * x := by
      unfold D
      rw [sum_mul, ← sum_add_distrib]
      apply sum_congr rfl
      intro j _
      dsimp only [y]
      ring
    rw [hE] at hMoment
    change D * (β + x) = H at hId
    linarith only [hId, hMoment]
  have hBase : (∑ j ∈ S, ν j * (z j ^ 2 * (1 - y j / B))) = (2 / 3) * D := by
    calc
      _ = D - (∑ j ∈ S, ν j * z j ^ 2 * y j) / B := by
        unfold D
        rw [sum_div, ← sum_sub_distrib]
        apply sum_congr rfl
        intro j _
        ring
      _ = _ := by
        rw [hDβ]
        dsimp only [B]
        field_simp [hβ₀.ne']
        ring
  have hHump := F.radialUnitSource_quartic_hump hn hp o hMax hB
  change (∑ j ∈ S, ν j * quarticHump x B (z j)) ≤ _ at hHump
  have hLo : (2 / 3) * D ≤ ∑ j ∈ S, ν j * quarticHump x B (z j) := by
    rw [← hBase]
    exact sum_le_sum (fun j hj =>
      mul_le_mul_of_nonneg_left (le_max_right _ _)
        (reweightedMass_nonneg (G.mass_pos _).le (G.currentChord_pos (mem_erase.mp hj).1).le))
  have hU := hLo.trans hHump
  change D ≤ _
  have hEq : 3 * ((B - x) ^ 2 / (4 * B)) = (3 * β - x) ^ 2 / (4 * β) := by
    dsimp only [B]
    field_simp [hβ₀.ne']
  linear_combination (3 / 2) * hU + hEq

/-- One actual maximum and one actual minimum give the strict 1/5 floor. -/
theorem quartic_mass_ratio_five {n : ℕ} {p : ℝ} (F : Configuration n p)
    (hn : 5 ≤ n) (hp : 4 ≤ p) (i j : Fin n) : F.mass i < 5*F.mass j := by
  obtain ⟨o,_,ho⟩ := (univ : Finset (Fin n)).exists_max_image F.mass ⟨⟨0,by omega⟩,mem_univ _⟩
  obtain ⟨m,_,hm⟩ := (univ : Finset (Fin n)).exists_min_image F.mass ⟨⟨0,by omega⟩,mem_univ _⟩
  have hn₂ : 2 ≤ n := by omega
  have hp₀ : 0 < p := by linarith
  let G := F.radialUnitSource hn₂ o
  let x := 1/(2*G.radius)^2
  let U := massTotal G.mass-1
  let q := G.mass m
  let W := G.currentReweightedTotal (G.currentOrder.symm o)
  have hoMax : ∀ k, F.mass k ≤ F.mass o := fun k => ho k (mem_univ k)
  have hmMin : ∀ k, F.mass m ≤ F.mass k := fun k => hm k (mem_univ k)
  by_contra! hBad
  have hq : 0 < q := G.mass_pos m
  have hqEq : q = F.mass m/F.mass o := F.radialUnitSource_mass hn₂ o m
  have hqSmall : q ≤ 1/5 := by
    rw [hqEq]
    apply (div_le_iff₀ (F.mass_pos o)).mpr
    linarith only [hBad,hoMax i,hmMin j]
  have hx : 0 < x := one_div_pos.mpr (sq_pos_of_pos (mul_pos zero_lt_two G.radius_pos))
  have hU : 1 ≤ U := by have h := F.radialUnitSource_totalMass_ge_two hn₂ o; dsimp [U]; linarith
  have hU₀ : 0 < U := by linarith
  have hT : U+4/5 ≤ massTotal G.mass-q := by dsimp [U]; linarith only [hqSmall]
  have hT₀ : 0 < U+4/5 := by linarith
  have hW : W ≤ U^(4/p) := F.radialUnitSource_reweightedTotal_holder hn₂ hp o
  have hR := F.radialUnitSource_row_moment_radius hn₂ hp₀ o m
  change 2*x ≤ massTotal G.mass/(massTotal G.mass-q)^(1+2/p) at hR
  rw [show massTotal G.mass=U+1 by unfold U; ring] at hR
  have hPow := Real.rpow_le_rpow hT₀.le hT (show 0 ≤ 1+2/p by positivity)
  rw [show massTotal G.mass=U+1 by unfold U; ring] at hPow
  have hR' := hR.trans (div_le_div_of_nonneg_left (show 0 ≤ U+1 by positivity [hU₀])
    (Real.rpow_pos_of_pos hT₀ _) hPow)
  have hScale : x*(U+4/5)^(2/p) ≤ 5/9 := by
    rw [Real.rpow_add hT₀,Real.rpow_one] at hR'
    have h := (le_div_iff₀ (mul_pos hT₀ (Real.rpow_pos_of_pos hT₀ _))).mp hR'
    apply (le_div_iff₀ (show (0:ℝ)<9 by norm_num)).mpr
    have h₁ : 0 ≤ (U+4/5)*(5/9-x*(U+4/5)^(2/p)) := by
      nlinarith only [h,hU]
    exact (le_of_not_gt fun hx => not_lt_of_ge h₁ (mul_neg_of_pos_of_neg hT₀ (by linarith)))
  have hUupper : U^(2/p) ≤ (U+4/5)^(2/p) := Real.rpow_le_rpow hU₀.le (by linarith) (by positivity)
  have hSqu := pow_le_pow_left₀ (show 0 ≤ x*U^(2/p) by positivity) ((mul_le_mul_of_nonneg_left hUupper hx.le).trans hScale) 2
  have hU4 : (U^(2/p))^2=U^(4/p) := by rw [← Real.rpow_mul_natCast hU₀.le]; congr 1; norm_num; ring
  rw [mul_pow,hU4] at hSqu
  have hBound : x^2*W ≤ 25/81 := by
    have h := mul_le_mul_of_nonneg_left hW (sq_nonneg x)
    nlinarith only [h,hSqu]
  let r := G.currentOrder.symm o
  let rm := G.currentOrder.symm m
  let H := 1 - x ^ 2 * W
  have hH : 0 < H := by dsimp only [H]; linarith only [hBound]
  have hHlower : 56 / 81 ≤ H := by dsimp only [H]; linarith only [hBound]
  obtain ⟨β, hβ, hId, _, hLower⟩ := F.radialUnitSource_quartic_barycenter hn₂ hp o hH
  have hMass : G.currentMasses rm = q := by
    simp only [currentMasses, Function.comp_apply, rm, Equiv.apply_symm_apply, q]
  have hMin (k : Fin n) : G.currentMasses rm ≤ G.currentMasses k := by
    rw [hMass]
    change G.mass m ≤ G.mass (G.currentOrder k)
    rw [F.radialUnitSource_mass, F.radialUnitSource_mass]
    exact div_le_div_of_nonneg_right (hmMin _) (F.mass_pos o).le
  have hUpper := F.radialUnitSource_quartic_ratio_current_upper hn₂ hp o hoMax rm hMin (hMass.symm ▸ hqSmall)
  have hHump := F.radialUnitSource_quartic_hump_barycenter hn₂ hp o hoMax hβ hId
  exact quarticRatio_contradiction hx.le hβ hHlower hId hLower hUpper hHump

end ACS12.Configuration


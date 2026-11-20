import ACS12.QuarticMaximumHump
import ACS12.HighPhysicalReweight

/-! The actual maximum-root measure occupies the two full semicircles. -/
namespace ACS12.Configuration

open Finset HighCurrent
set_option backward.isDefEq.respectTransparency false

theorem radialUnitSource_quartic_hump {n : ℕ} {p : ℝ} (F : Configuration n p)
    (hn : 2 ≤ n) (hp : 4 ≤ p) (o : Fin n) (hMax : ∀ i, F.mass i ≤ F.mass o)
    {B : ℝ} (hB : 1 / (2 * (F.radialUnitSource hn o).radius) ^ 2 < B) :
    let G := F.radialUnitSource hn o
    let r := G.currentOrder.symm o
    let x := 1 / (2 * G.radius) ^ 2
    (∑ j ∈ univ.erase r, G.currentReweightedMass r j * quarticHump x B (G.currentZeta r j)) ≤
      2 * ((B - x) ^ 2 / (4 * B) + (2 / 3) * Real.sqrt B - Real.sqrt x + x * Real.sqrt x / (3 * B)) := by
  let G := F.radialUnitSource hn o
  let r := G.currentOrder.symm o
  let D := 2 * G.radius
  let x := 1 / D ^ 2
  let L := Real.pi * D / 2
  let S := (univ : Finset (Fin n)).erase r
  let ν := G.currentReweightedMass r
  let f (z : ℝ) := quarticHump x B z
  have hD : 0 < D := mul_pos zero_lt_two G.radius_pos
  have hx : 0 < x := one_div_pos.mpr (sq_pos_of_pos hD)
  have hB₀ := hx.trans hB
  have hp₀ : 0 < p := by linarith only [hp]
  have hp₁ : 1 ≤ p := by linarith only [hp]
  have hDiam : 1 ≤ D := F.radialUnitSource_diameter_ge_one hn hp₀ o
  have hL : 1 ≤ L := by
    have h := mul_le_mul_of_nonneg_left hDiam Real.pi_pos.le
    dsimp only [L]
    linarith only [h, Real.pi_gt_three]
  have hRoot (j : Fin n) (hj : j ∈ S) : 1 ≤ G.currentChord r j := by
    have hjr : G.currentOrder j ≠ o := by
      intro h
      apply (mem_erase.mp hj).1
      exact G.currentOrder.injective (by simpa only [r, Equiv.apply_symm_apply] using h)
    simpa only [currentChord, r, Equiv.apply_symm_apply] using
      F.radialUnitSource_root_chord hn hp₀ o (G.currentOrder j) hjr
  have hWeight (j : Fin n) (hj : j ∈ S) : ν j ≤ G.currentMasses j :=
    reweightedMass_le hp (G.mass_pos _).le (hRoot j hj)
  have hw (j : Fin n) (hj : j ∈ S) : 0 ≤ ν j ∧ ν j ≤ 1 :=
    ⟨reweightedMass_nonneg (G.mass_pos _).le (norm_nonneg _),
      (hWeight j hj).trans (F.radialUnitSource_maximum hn o hMax (G.currentOrder j))⟩
  have hPack {i j : Fin n} (hi : i ∈ S) (hij : i ≠ j) :
      ν i ≤ ‖G.position (G.currentOrder i) - G.position (G.currentOrder j)‖ :=
    (hWeight i hi).trans (F.radialUnitSource_mass_le_chord hn hp₁ o hMax _ _
      (G.currentOrder.injective.ne hij))
  have hHalf (t : Fin n → ℝ) (T : Finset (Fin n)) (hT : T ⊆ S)
      (hDom : ∀ j ∈ T, t j ∈ Set.Icc 1 L)
      (hSep : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → ν i ≤ |t i - t j|)
      (hEq : ∀ j ∈ T, G.currentZeta r j = circleCurrentZeta D (t j)) :
      (∑ j ∈ T, ν j * f (G.currentZeta r j)) ≤
        (B - x) ^ 2 / (4 * B) + (2 / 3) * Real.sqrt B - Real.sqrt x + x * Real.sqrt x / (3 * B) := by
    let z := circleCurrentZeta D
    have hC : ContinuousOn z (Set.Icc 1 L) := circleCurrentZeta_continuousOn hD (by norm_num)
    have hAnti : AntitoneOn z (Set.Icc 1 L) := circleCurrentZeta_antitone hD (by norm_num)
    have hz (y : ℝ) (hy : y ∈ Set.Icc 1 L) : 0 ≤ z y :=
      circleCurrentZeta_nonneg hD (zero_lt_one.trans_le hy.1) hy.2
    have hCap := finite_unimodal_capacity t ν T hL (by positivity : 0 ≤ (B-x)^2/(4*B))
      ((quarticHump_continuous x B).comp_continuousOn hC)
      (fun y _ => quarticHump_nonneg x B (z y))
      (fun y _ => quarticHump_height hB₀ (z y))
      (fun {u v w} hu hw' huv hvw => by
        let hv : v ∈ Set.Icc 1 L := ⟨hu.1.trans huv, hvw.trans hw'.2⟩
        simp only [Function.comp_apply]
        rw [min_comm]
        exact quarticHump_min hB₀ (hz w hw') (hAnti hv hw' hvw) (hAnti hu hv huv))
      (fun j hj => hw j (hT hj)) hDom hSep
    have hInt := quarticHump_arc_integral hx hB hL hC
      (fun y hy => circleCurrentZeta_deriv hD (zero_lt_one.trans_le hy.1) hy.2)
      (hz 1 ⟨le_rfl, hL⟩) (circleCurrentZeta_end hD)
    simp only [Function.comp_apply] at hCap
    rw [sum_congr rfl (fun j hj => by rw [hEq j hj])]
    unfold f
    linarith only [hCap, hInt]
  let front := S.filter (fun j => halfArc G.currentAngles r j ≤ Real.pi / 2)
  let back := S.filter (fun j => ¬halfArc G.currentAngles r j ≤ Real.pi / 2)
  have hFront := hHalf (G.currentForwardArc r) front (fun _ hj => (mem_filter.mp hj).1)
    (fun j hj => G.currentForwardArc_half_bounds (mem_erase.mp (mem_filter.mp hj).1).1
      (hRoot j (mem_filter.mp hj).1) (mem_filter.mp hj).2)
    (fun i hi j hj hij => (hPack (mem_filter.mp hi).1 hij).trans (G.currentForwardArc_pair_chord r i j))
    (fun j hj => G.currentZeta_forward (mem_erase.mp (mem_filter.mp hj).1).1 (mem_filter.mp hj).2)
  have hBack := hHalf (G.currentBackwardArc r) back (fun _ hj => (mem_filter.mp hj).1)
    (fun j hj => G.currentBackwardArc_half_bounds (mem_erase.mp (mem_filter.mp hj).1).1
      (hRoot j (mem_filter.mp hj).1) (le_of_not_ge (mem_filter.mp hj).2))
    (fun i hi j hj hij => (hPack (mem_filter.mp hi).1 hij).trans (G.currentBackwardArc_pair_chord r i j))
    (fun j hj => G.currentZeta_backward (mem_erase.mp (mem_filter.mp hj).1).1 (le_of_not_ge (mem_filter.mp hj).2))
  have hPartition : (∑ j ∈ front, ν j * f (G.currentZeta r j)) +
      (∑ j ∈ back, ν j * f (G.currentZeta r j)) = ∑ j ∈ S, ν j * f (G.currentZeta r j) :=
    sum_filter_add_sum_filter_not S _ _
  change (∑ j ∈ S, ν j * f (G.currentZeta r j)) ≤ _
  linarith only [hFront, hBack, hPartition]

end ACS12.Configuration

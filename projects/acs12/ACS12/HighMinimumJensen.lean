import ACS12.HighUnitGeometry
import ACS12.PowerConvex
import ACS12.PressurePairCalibration

/-! The same original minimum-row Jensen moment is retained before any numerical radius receiving. -/
namespace ACS12.Configuration

open Finset Pressure
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {p : ℝ} (F : ACS12.Configuration n p)

theorem radialUnitSource_minimum_Jensen (hn : 2 ≤ n) (hp : 0 < p) (o i : Fin n) :
    let G := F.radialUnitSource hn o
    let M := massTotal G.mass
    let t := M - G.mass i
    t * (2 * t / M) ^ (p / 2) ≤ (2 * G.radius) ^ p := by
  let G := F.radialUnitSource hn o
  let M := massTotal G.mass
  let t := M - G.mass i
  let s := p / 2
  have hM : 0 < M := massTotal_pos (by omega) G.mass_pos
  have ht : 0 < t := sub_pos.mpr (massTotal_gt_mass hn G.mass_pos i)
  have hs : 0 < s := by unfold s; positivity
  have hRoot : G.mass o = 1 := F.radialUnitSource_root hn o
  have hOutside : ∑ j ∈ univ.erase i, G.mass j = t := sum_erase_eq_sub (mem_univ i)
  have hMoment : ∑ j ∈ univ.erase i, G.mass j * G.diameterChordSq i j = M / 2 := by
    have h := G.diameterChordSq_centered_sum o i
    simpa only [hRoot,div_one] using h
  have hLevel : 2 * G.coefficient * G.radius ^ 2 = 1 := by
    rw [← G.radial_row i]
    exact F.radialUnitSource_radial hn hp o i
  have hRadial : ∑ j ∈ univ.erase i, G.mass j * G.diameterChordSq i j ^ (-s) = (2 * G.radius) ^ p := by
    have h := G.diameterChordSq_radial_sum o i
    simpa only [hRoot,div_one,hLevel,mul_one,s] using h
  let w (j : Fin n) := G.mass j / t
  have hW : ∑ j ∈ univ.erase i, w j = 1 := by
    unfold w
    rw [← sum_div,hOutside,div_self ht.ne']
  have hJ := (negativePower_convex hs).map_sum_le (t := univ.erase i)
    (fun j _ => div_nonneg (G.mass_pos j).le ht.le) hW
    (fun j hj => G.diameterChordSq_pos (mem_erase.mp hj).1)
  simp only [smul_eq_mul] at hJ
  have hMean : (∑ j ∈ univ.erase i, w j * G.diameterChordSq i j) = M / 2 / t := by
    have hE (j : Fin n) : w j * G.diameterChordSq i j = (G.mass j * G.diameterChordSq i j) / t := by
      unfold w
      ring
    simp_rw [hE,← sum_div,hMoment]
  have hValue : (∑ j ∈ univ.erase i, w j * G.diameterChordSq i j ^ (-s)) = (2 * G.radius) ^ p / t := by
    have hE (j : Fin n) : w j * G.diameterChordSq i j ^ (-s) =
        (G.mass j * G.diameterChordSq i j ^ (-s)) / t := by unfold w; ring
    simp_rw [hE,← sum_div,hRadial]
  rw [hMean,hValue,Real.rpow_neg (by positivity),← Real.inv_rpow (by positivity),
    show (M / 2 / t)⁻¹ = 2 * t / M by field_simp [hM.ne',ht.ne']] at hJ
  have h := (le_div_iff₀ ht).mp hJ
  nlinarith only [h]

end ACS12.Configuration

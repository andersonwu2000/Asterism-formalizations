import ACS12.HighUnitGeometry
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Jensen

/-! The same physical atomic measure under the complete fourth-kernel reweighting. -/
namespace ACS12.HighCurrent

open Finset

noncomputable def reweightedMass (p m d : ℝ) : ℝ := m * d ^ (4 - p)

theorem reweighted_row_identity {p m d : ℝ} (hd : 0 < d) :
    reweightedMass p m d * d ^ (-4 : ℝ) = m * d ^ (-p) := by
  unfold reweightedMass
  rw [mul_assoc,← Real.rpow_add hd,show 4 - p + -4 = -p by ring]

theorem reweighted_current_identity {p m d z : ℝ} (hd : 0 < d) :
    reweightedMass p m d * d ^ (-4 : ℝ) * z = m * d ^ (-p) * z := by
  rw [reweighted_row_identity hd]

theorem reweightedMass_le {p m d : ℝ} (hp : 4 ≤ p) (hm : 0 ≤ m) (hd : 1 ≤ d) :
    reweightedMass p m d ≤ m := by
  unfold reweightedMass
  apply mul_le_of_le_one_right hm
  exact Real.rpow_le_one_of_one_le_of_nonpos hd (by linarith only [hp])

theorem reweightedMass_nonneg {p m d : ℝ} (hm : 0 ≤ m) (hd : 0 ≤ d) :
    0 ≤ reweightedMass p m d := mul_nonneg hm (Real.rpow_nonneg hd _)

theorem reweighted_total_mass_bound {ι : Type*} (s : Finset ι) (m d : ι → ℝ)
    (hm : ∀ i ∈ s, 0 < m i) (hd : ∀ i ∈ s, 0 < d i)
    (hU : 0 < ∑ i ∈ s, m i) {p : ℝ} (hp : 4 ≤ p) :
    (∑ i ∈ s, reweightedMass p (m i) (d i)) ≤
      (∑ i ∈ s, m i) ^ (4 / p) * (∑ i ∈ s, m i * (d i) ^ (-p)) ^ (1 - 4 / p) := by
  let U := ∑ i ∈ s, m i
  let C := ∑ i ∈ s, m i * (d i) ^ (-p)
  let β := 1 - 4 / p
  let w (i : ι) := m i / U
  let X (i : ι) := (d i) ^ (-p)
  have hp₀ : 0 < p := by linarith only [hp]
  have hβ : 0 ≤ β := by
    unfold β
    have h := (div_le_one hp₀).mpr hp
    linarith only [h]
  have hβ₁ : β ≤ 1 := by
    unfold β
    have h := div_pos (by norm_num : (0 : ℝ) < 4) hp₀
    linarith only [h]
  have hw (i : ι) (hi : i ∈ s) : 0 ≤ w i := div_nonneg (hm i hi).le hU.le
  have hw₁ : ∑ i ∈ s, w i = 1 := by
    unfold w
    rw [← sum_div,div_self hU.ne']
  have hX (i : ι) (hi : i ∈ s) : 0 ≤ X i := (Real.rpow_pos_of_pos (hd i hi) _).le
  have hJ := (Real.concaveOn_rpow hβ hβ₁).le_map_sum hw hw₁ hX
  simp only [smul_eq_mul] at hJ
  have hPower (i : ι) (hi : i ∈ s) : X i ^ β = (d i) ^ (4 - p) := by
    unfold X β
    rw [← Real.rpow_mul (hd i hi).le]
    congr 1
    field_simp [hp₀.ne']
    <;> ring
  have hLeft : (∑ i ∈ s, w i * X i ^ β) =
      (∑ i ∈ s, reweightedMass p (m i) (d i)) / U := by
    unfold w reweightedMass
    simp_rw [sum_div]
    apply sum_congr rfl
    intro i hi
    rw [hPower i hi]
    ring
  have hRight : (∑ i ∈ s, w i * X i) = C / U := by
    unfold w C X
    rw [sum_div]
    apply sum_congr rfl
    intro i _
    ring
  rw [hLeft,hRight] at hJ
  have hC : 0 ≤ C := sum_nonneg fun i hi => mul_nonneg (hm i hi).le (hX i hi)
  have hNormalize : (C / U) ^ β * U = U ^ (4 / p) * C ^ β := by
    rw [Real.div_rpow hC hU.le]
    have hPowers : U ^ (4 / p) * U ^ β = U := by
      rw [← Real.rpow_add hU,show 4 / p + β = 1 by unfold β; ring,Real.rpow_one]
    calc
      _ = (C ^ β / U ^ β) * (U ^ (4 / p) * U ^ β) := by rw [hPowers]
      _ = U ^ (4 / p) * ((C ^ β / U ^ β) * U ^ β) := by ring
      _ = U ^ (4 / p) * C ^ β := by
        rw [div_mul_cancel₀ _ (Real.rpow_pos_of_pos hU β).ne']
  have h := (div_le_iff₀ hU).mp hJ
  rw [hNormalize] at h
  exact h

end ACS12.HighCurrent

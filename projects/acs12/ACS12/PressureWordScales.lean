import ACS12.PressureSourceRow

/-! The complete range of the normalized real-count row and its exact word scales. -/
namespace ACS12.Pressure

open Set MeasureTheory Filter CenteredCircle.AllN
open NativeCells (analyticRow analyticRow_pos analyticRow_two_eq meanMass rootRow_le_commonRow)
open GammaMeasure (powerTail powerTail_pos signedDensity_pos)

theorem pressureNormalizedRow_pos {p N : ℝ} (hp : 1 < p) (hN : 1 < N) :
    0 < pressureNormalizedRow p N := by
  have hP := powerTail_pos hp (m := 1) (by decide)
  unfold pressureNormalizedRow
  exact div_pos (analyticRow_pos (zero_lt_one.trans hp) hN) (by positivity)

noncomputable def pressureRankE {n : ℕ} {p : ℝ} (F : Configuration n p) : ℝ :=
  originalPressureRow F / analyticRow p (n : ℝ)

noncomputable def pressureW {n : ℕ} {p : ℝ} (F : Configuration n p) : ℝ :=
  (geometricPressureRow F / analyticRow p (n : ℝ)) ^ (1 / (p + 1))

noncomputable def pressureWFlat {n : ℕ} {p : ℝ} (F : Configuration n p) : ℝ :=
  let m := sortedPressureMass F
  massGeometricMean m ^ (1 / (p + 1)) / centeredMoment m 1 ^ (p / (p + 1))

noncomputable def pressureRho {n : ℕ} {p : ℝ} (F : Configuration n p) : ℝ :=
  let m := sortedPressureMass F
  pressureNormalizedRow p (massTotal m / massGeometricMean m)

theorem pressureW_pos {n : ℕ} {p : ℝ} (hp : 0 < p) (hn : 2 ≤ n) (F : Configuration n p) :
    0 < pressureW F := by
  unfold pressureW
  exact Real.rpow_pos_of_pos (div_pos (geometricPressureRow_pos hp hn F)
    (analyticRow_pos hp (Nat.one_lt_cast.mpr (by omega)))) _

theorem pressureW_eq_flat {n : ℕ} {p : ℝ} (hp : 1 < p) (hn : 2 ≤ n) (F : Configuration n p) :
    pressureW F = pressureWFlat F * (pressureRho F / pressureNormalizedRow p (n : ℝ)) ^ (1 / (p + 1)) := by
  let m := sortedPressureMass F
  let g := massGeometricMean m
  let M := massTotal m
  let t := centeredMoment m 1
  let N := M / g
  let a : ℝ := 1 / (p + 1)
  let ρ := pressureRho F
  let A := pressureNormalizedRow p (n : ℝ)
  have hm (i : Fin n) : 0 < m i := F.mass_pos (Tuple.sort F.phase i)
  have hp₀ := zero_lt_one.trans hp
  have hg : 0 < g := Real.exp_pos _
  have hM : 0 < M := massTotal_pos (by omega) hm
  have hN : 1 < N := (one_lt_div hg).mpr (massGeometricMean_lt_total hn hm)
  have ht : 0 < t := zero_lt_one.trans_le (centeredMoment_ge_one (by omega) hm 1)
  have hρ : 0 < ρ := pressureNormalizedRow_pos hp hN
  have hn₀ : (1 : ℝ) < (n : ℝ) := Nat.one_lt_cast.mpr (by omega)
  have hA : 0 < A := pressureNormalizedRow_pos hp hn₀
  have htN : t * N = (n : ℝ) := by
    unfold N
    rw [show t = g * (n : ℝ) / M from centeredMoment_one_eq (by omega) hm]
    field_simp [hM.ne',hg.ne']
  have hScale : (n : ℝ) ^ p = t ^ p * N ^ p := by rw [← htN,Real.mul_rpow ht.le (zero_lt_one.trans hN).le]
  have hG : geometricPressureRow F / analyticRow p (n : ℝ) = (g * (ρ / A)) / t ^ p := by
    change g * analyticRow p N / analyticRow p (n : ℝ) =
      (g * (pressureNormalizedRow p N / pressureNormalizedRow p (n : ℝ))) / t ^ p
    unfold pressureNormalizedRow
    rw [hScale]
    have hZ := powerTail_pos hp (m := 1) (by decide)
    field_simp [(analyticRow_pos hp₀ hn₀).ne',hZ.ne',(Real.rpow_pos_of_pos Real.pi_pos p).ne',
      (Real.rpow_pos_of_pos ht p).ne',(Real.rpow_pos_of_pos (zero_lt_one.trans hN) p).ne']
  change (geometricPressureRow F / analyticRow p (n : ℝ)) ^ a =
    (g ^ a / t ^ (p / (p + 1))) * (ρ / A) ^ a
  rw [hG,Real.div_rpow (by positivity) (Real.rpow_nonneg ht.le _),
    Real.mul_rpow hg.le (div_nonneg hρ.le hA.le),← Real.rpow_mul ht.le]
  unfold a
  ring

theorem pressureW_le_flat {n : ℕ} {p : ℝ} (hp : 1 < p) (hp₂ : p ≤ 2) (hn : 2 ≤ n) (F : Configuration n p) :
    pressureW F ≤ pressureWFlat F := by
  let m := sortedPressureMass F
  let t := centeredMoment m 1
  let N := massTotal m / massGeometricMean m
  have hm (i : Fin n) : 0 < m i := F.mass_pos (Tuple.sort F.phase i)
  have hg : 0 < massGeometricMean m := Real.exp_pos _
  have hM := massTotal_pos (by omega) hm
  have hN : 1 < N := (one_lt_div hg).mpr (massGeometricMean_lt_total hn hm)
  have hn₀ : (1 : ℝ) < (n : ℝ) := Nat.one_lt_cast.mpr (by omega)
  have ht : 1 ≤ t := centeredMoment_ge_one (by omega) hm 1
  have hTN : t * N = (n : ℝ) := by
    unfold N
    rw [show t = massGeometricMean m * (n : ℝ) / massTotal m from centeredMoment_one_eq (by omega) hm]
    field_simp [hg.ne',hM.ne']
  have hN' : N ≤ (n : ℝ) := by
    rw [← hTN]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ht (zero_lt_one.trans hN).le
  have hρ : pressureRho F ≤ pressureNormalizedRow p (n : ℝ) :=
    pressureNormalizedRow_mono hp hp₂ hN hn₀ hN'
  have hA : 0 < pressureNormalizedRow p (n : ℝ) := pressureNormalizedRow_pos hp hn₀
  have hR : pressureRho F / pressureNormalizedRow p (n : ℝ) ≤ 1 := (div_le_one hA).mpr hρ
  have hQ : 0 ≤ pressureRho F / pressureNormalizedRow p (n : ℝ) :=
    div_nonneg (pressureNormalizedRow_pos hp hN).le hA.le
  have hF : 0 ≤ pressureWFlat F := by
    change 0 ≤ massGeometricMean m ^ (1 / (p + 1)) / t ^ (p / (p + 1))
    have ht₀ : 0 < t := zero_lt_one.trans_le ht
    positivity
  rw [pressureW_eq_flat hp hn]
  exact mul_le_of_le_one_right hF (Real.rpow_le_one hQ hR (by positivity))

end ACS12.Pressure


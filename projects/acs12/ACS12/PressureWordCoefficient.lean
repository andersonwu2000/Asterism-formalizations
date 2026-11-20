import ACS12.PressureWordScales

/-! The original same-word coefficient, with the two factors kept correlated. -/
namespace ACS12.Pressure

open NativeCells (meanMass)

noncomputable def pressureMeanPower {n : ℕ} (p : ℝ) (m : Fin n → ℝ) : ℝ :=
  (∑ i, m i ^ (1 / p)) / (n : ℝ)

theorem massGeometricMean_le_one {n : ℕ} (hn : 0 < n) {m : Fin n → ℝ}
    (hm : ∀ i, 0 < m i) (hCap : ∀ i, m i ≤ 1) : massGeometricMean m ≤ 1 := by
  unfold massGeometricMean
  apply Real.exp_le_one_iff.mpr
  exact Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos
    (div_nonneg (hm i).le (massTotal_pos hn hm).le) (Real.log_nonpos (hm i).le (hCap i))

theorem pressureMeanPower_eq_moment {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 0 < p)
    {m : Fin n → ℝ} (hm : ∀ i, 0 < m i) :
    pressureMeanPower p m = massGeometricMean m ^ (1 / p) *
      centeredMoment m ((p - 1) / p) / centeredMoment m 1 := by
  let g := massGeometricMean m
  let B := meanMass m
  let b : ℝ := (p - 1) / p
  let u : ℝ := 1 / p
  have hg : 0 < g := Real.exp_pos _
  have hM := massTotal_pos hn hm
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hB : 0 < B := div_pos hM hn₀
  have hExp : 1 - b = u := by unfold b u; field_simp [hp.ne']; ring
  have hExp' : u + b = 1 := by linarith only [hExp]
  have h := centeredMoment_mass_power hn hm b
  rw [hExp] at h
  change pressureMeanPower p m = g ^ u * centeredMoment m b / centeredMoment m 1
  rw [h,centeredMoment_one_eq hn hm]
  unfold pressureMeanPower
  change (∑ i, m i ^ u) / (n : ℝ) = g ^ u * (g ^ b / massTotal m * ∑ i, m i ^ u) /
    (g * (n : ℝ) / massTotal m)
  rw [show g ^ u * (g ^ b / massTotal m * ∑ i, m i ^ u) =
    (g ^ u * g ^ b) / massTotal m * ∑ i, m i ^ u by ring,
    ← Real.rpow_add hg,hExp',Real.rpow_one]
  field_simp [hg.ne',hM.ne',hn₀.ne']

end ACS12.Pressure

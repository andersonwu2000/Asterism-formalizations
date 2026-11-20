import ACS12.PressurePristine
import ACS12.PressureTriangleRow

/-! The actual row value from pristine pressure and the centered moment. -/
namespace ACS12.Pressure

open Set
open NativeCells (analyticRow rootRow rootRow_le_commonRow)
open GammaMeasure (powerTail powerTail_pos)

theorem centeredMoment_one_eq {n : ℕ} (hn : 0 < n) {m : Fin n → ℝ} (hm : ∀ i, 0 < m i) :
    centeredMoment m 1 = massGeometricMean m * (n : ℝ) / massTotal m := by
  have h := centeredMoment_mass_power hn hm 1
  simp only [Real.rpow_one,sub_self,Real.rpow_zero,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one] at h
  exact h.trans (by ring)

theorem meanRoot_centered_eq {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 0 < p)
    {m : Fin n → ℝ} (hm : ∀ i, 0 < m i) :
    Rank.meanRoot p m = massGeometricMean m ^ (1 / (p + 1)) *
      centeredMoment m (p / (p + 1)) / centeredMoment m 1 := by
  let g := massGeometricMean m
  let M := massTotal m
  let a : ℝ := 1 / (p + 1)
  let β : ℝ := p / (p + 1)
  have hg : 0 < g := Real.exp_pos _
  have hM : 0 < M := massTotal_pos hn hm
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hExp : 1 - β = a := by
    unfold a β
    field_simp [show p + 1 ≠ 0 by positivity]
    ring
  have hExp' : a + β = 1 := by linarith only [hExp]
  have h := centeredMoment_mass_power hn hm β
  rw [hExp] at h
  change Rank.meanRoot p m = g ^ a * centeredMoment m β / centeredMoment m 1
  rw [h,centeredMoment_one_eq hn hm]
  unfold Rank.meanRoot
  change (∑ i, m i ^ a) / (n : ℝ) = g ^ a * (g ^ β / M * ∑ i, m i ^ a) / (g * (n : ℝ) / M)
  rw [show g ^ a * (g ^ β / M * ∑ i, m i ^ a) = (g ^ a * g ^ β) / M * ∑ i, m i ^ a by ring,
    ← Real.rpow_add hg,hExp',Real.rpow_one]
  field_simp [hg.ne',hM.ne',hn₀.ne']

end ACS12.Pressure

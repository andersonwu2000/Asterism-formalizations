import ACS12.QuarticTrial
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen

/-! Exact logarithmic normalization of the original root lower bound against the quartic trial. -/
namespace ACS12.NativeCells

open Finset Set
open Pressure (massTotal massTotal_pos massWeight massWeight_sum_one)

noncomputable def quarticRegularRatio (p N : ℝ) : ℝ :=
  analyticRow p N / analyticRow 4 N * (Real.sin (Real.pi / N)) ^ (p - 4)

noncomputable def quarticBase {n : ℕ} (w : Fin n → ℝ) : ℝ :=
  Real.log (analyticRow 4 n) + (∑ i, Real.log (w i)) / n -
    ∑ i, w i * (Real.log (w i) + Real.log (analyticRow 4 (w i)⁻¹))

noncomputable def quarticSineDeficit {n : ℕ} (w : Fin n → ℝ) : ℝ :=
  (∑ i, w i * Real.log (Real.sin (Real.pi * w i))) -
    Real.log (Real.sin (Real.pi / n))

private theorem regular_sin_pos {N : ℝ} (hN : 1 < N) : 0 < Real.sin (Real.pi / N) :=
  Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos (zero_lt_one.trans hN))
    ((div_lt_iff₀ (zero_lt_one.trans hN)).mpr (by nlinarith only [mul_pos Real.pi_pos (sub_pos.mpr hN)]))

theorem quarticRegularRatio_pos {p N : ℝ} (hp : 0 < p) (hN : 1 < N) :
    0 < quarticRegularRatio p N :=
  mul_pos (div_pos (analyticRow_pos hp hN) (analyticRow_pos (by norm_num) hN))
    (Real.rpow_pos_of_pos (regular_sin_pos hN) _)

theorem quarticRegularRatio_four {N : ℝ} (hN : 1 < N) : quarticRegularRatio 4 N = 1 := by
  have hR := analyticRow_pos (by norm_num : (0 : ℝ) < 4) hN
  simp [quarticRegularRatio, hR.ne']

/-- The finite geometric mean for the exact power in the original root,
before any estimates on the mass word. -/
private theorem log_rootRow_lower {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 0 < p)
    {m : Fin n → ℝ} (hm : ∀ i, 0 < m i) :
    0 < rootRow p m ∧
      Real.log (analyticRow p n) + (∑ i, Real.log (m i)) / n ≤ Real.log (rootRow p m) := by
  have hN₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hN : (1 : ℝ) < n := Nat.one_lt_cast.mpr (by omega)
  have hP : 0 < p + 1 := by positivity
  have hRow := analyticRow_pos hp hN
  let X (i : Fin n) := m i ^ (1 / (p + 1))
  have hX (i : Fin n) : 0 < X i := Real.rpow_pos_of_pos (hm i) _
  have hSum : (∑ _i : Fin n, (n : ℝ)⁻¹) = 1 := by
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_inv_cancel₀ hN₀.ne']
  have hJ := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (t := (univ : Finset (Fin n))) (w := fun _ : Fin n => (n : ℝ)⁻¹) (p := X)
    (fun _ _ => (inv_pos.mpr hN₀).le) hSum (fun i _ => hX i)
  simp only [smul_eq_mul, ← mul_sum] at hJ
  have hMean : 0 < Rank.meanRoot p m := by
    unfold Rank.meanRoot
    exact div_pos (sum_pos (fun i _ => hX i) ⟨⟨0, by omega⟩, mem_univ _⟩) hN₀
  have h := mul_le_mul_of_nonneg_left hJ hP.le
  have hL : (∑ x, Real.log (X x)) = (1 / (p + 1)) * ∑ x, Real.log (m x) := by
    simp only [X, Real.log_rpow (hm _), mul_sum]
  rw [hL, show (n : ℝ)⁻¹ * (∑ x, X x) = Rank.meanRoot p m by
    unfold Rank.meanRoot; rw [div_eq_inv_mul]] at h
  have hRoot : 0 < rootRow p m := mul_pos hRow (Real.rpow_pos_of_pos hMean _)
  refine ⟨hRoot, ?_⟩
  have hNorm : (p + 1) * ((n : ℝ)⁻¹ * ((1 / (p + 1)) * ∑ x, Real.log (m x))) =
      (∑ x, Real.log (m x)) / n := by
    field_simp [hN₀.ne', hP.ne']
  rw [hNorm] at h
  rw [rootRow, Real.log_mul hRow.ne' (Real.rpow_pos_of_pos hMean _).ne', Real.log_rpow hMean]
  exact add_le_add_right h _

private theorem log_quarticUpper {n : ℕ} (hn : 0 < n) {p : ℝ} {m : Fin n → ℝ}
    (hm : ∀ i, 0 < m i) (hw₁ : ∀ i, massWeight m i < 1)
    (hZ : 0 < quarticZ p (massWeight m)) :
    Real.log (quarticUpper p m) = Real.log (quarticZ p (massWeight m)) + Real.log (massTotal m) +
      (∑ i, massWeight m i * (Real.log (massWeight m i) +
        Real.log (analyticRow 4 (massWeight m i)⁻¹))) -
      (p - 4) * (∑ i, massWeight m i * Real.log (Real.sin (Real.pi * massWeight m i))) := by
  let M := massTotal m
  let w := massWeight m
  have hM : 0 < M := massTotal_pos hn hm
  have hw (i : Fin n) : 0 < w i := div_pos (hm i) hM
  have hW : ∑ i, w i = 1 := massWeight_sum_one hn hm
  have hMass (i : Fin n) : Real.log (m i) = Real.log M + Real.log (w i) := by
    rw [← Real.log_mul hM.ne' (hw i).ne']
    congr 1
    change m i = M * (m i / M)
    field_simp [hM.ne']
  have hE (i : Fin n) :
      2 * (w i * Real.log (m i / quarticGauge p (w i))) =
        w i * (2 * Real.log M) + w i * (Real.log (w i) + Real.log (analyticRow 4 (w i)⁻¹)) -
        (p - 4) * (w i * Real.log (Real.sin (Real.pi * w i))) := by
    rw [Real.log_div (hm i).ne' (quarticGauge_pos (hw i) (hw₁ i)).ne', hMass i]
    have h := congrArg (w i * ·) (quarticGauge_log (p := p) (hw i) (hw₁ i))
    linear_combination -h
  change Real.log (quarticZ p w / M * Real.exp (2 * ∑ i, w i * Real.log (m i / quarticGauge p (w i)))) = _
  rw [Real.log_mul (div_pos hZ hM).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_div hZ.ne' hM.ne',
    mul_sum, sum_congr rfl (fun i _ => hE i), sum_sub_distrib, sum_add_distrib, ← sum_mul,
    ← mul_sum, hW, one_mul]
  ring

theorem quartic_log_rootComparison {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 0 < p)
    {m : Fin n → ℝ} (hm : ∀ i, 0 < m i) (hw₁ : ∀ i, massWeight m i < 1)
    (hZ : 0 < quarticZ p (massWeight m)) :
    quarticBase (massWeight m) + (p - 4) * quarticSineDeficit (massWeight m) -
      Real.log (quarticZ p (massWeight m) / quarticRegularRatio p n) ≤
      Real.log (rootRow p m / quarticUpper p m) := by
  let M := massTotal m
  let w := massWeight m
  have hM : 0 < M := massTotal_pos (by omega) hm
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hN : (1 : ℝ) < n := Nat.one_lt_cast.mpr (by omega)
  have hReg := quarticRegularRatio_pos hp hN
  have hR := log_rootRow_lower hn hp hm
  have hU : 0 < quarticUpper p m := mul_pos (div_pos hZ hM) (Real.exp_pos _)
  have hLogR : Real.log (quarticRegularRatio p n) =
      Real.log (analyticRow p n) - Real.log (analyticRow 4 n) +
        (p - 4) * Real.log (Real.sin (Real.pi / n)) := by
    have hA := analyticRow_pos hp hN
    have h₄ := analyticRow_pos (by norm_num : 0 < (4 : ℝ)) hN
    have hS := regular_sin_pos hN
    rw [quarticRegularRatio, Real.log_mul (div_pos hA h₄).ne' (Real.rpow_pos_of_pos hS _).ne',
      Real.log_div hA.ne' h₄.ne', Real.log_rpow hS]
  have hLogMass : (∑ i, Real.log (m i)) / n = Real.log M + (∑ i, Real.log (w i)) / n := by
    have hTerm (i : Fin n) : Real.log (m i) = Real.log M + Real.log (w i) := by
      have hi : 0 < w i := div_pos (hm i) hM
      rw [← Real.log_mul hM.ne' hi.ne']
      congr 1
      change m i = M * (m i / M)
      field_simp [hM.ne']
    simp only [hTerm, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hn₀.ne']
  rw [hLogMass] at hR
  rw [Real.log_div hR.1.ne' hU.ne', log_quarticUpper (by omega) hm hw₁ hZ,
    Real.log_div hZ.ne' hReg.ne', hLogR]
  change quarticBase w + (p - 4) * quarticSineDeficit w - _ ≤ _
  unfold quarticBase quarticSineDeficit
  linarith only [hR.2]

end ACS12.NativeCells

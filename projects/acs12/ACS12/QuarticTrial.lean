import ACS12.NativeLiteralRows
import ACS12.NativeNormalization

/-! One quartic cell square calibrates the trial on the entire exponent ray. -/
namespace ACS12.NativeCells

open Finset Set
open CenteredCircle.AllN (positiveAngle_range)
open Pressure (massTotal massTotal_pos massWeight massWeight_sum_one)

noncomputable def quarticGauge (p w : ℝ) : ℝ :=
  Real.sqrt (w / analyticRow 4 w⁻¹) * Real.sin (Real.pi * w) ^ ((p - 4) / 2)

noncomputable def quarticCellAngle {n : ℕ} (w : Fin n → ℝ) (i : Fin n) : ℝ :=
  center (massCells w) i

noncomputable def quarticZ {n : ℕ} (p : ℝ) (w : Fin n → ℝ) : ℝ :=
  angularEnergy p (fun i => quarticGauge p (w i)) (quarticCellAngle w)

noncomputable def quarticUpper {n : ℕ} (p : ℝ) (m : Fin n → ℝ) : ℝ :=
  quarticZ p (massWeight m) / massTotal m *
    Real.exp (2 * ∑ i, massWeight m i *
      Real.log (m i / quarticGauge p (massWeight m i)))

theorem quarticGauge_pos {p w : ℝ} (hw : 0 < w) (hw₁ : w < 1) :
    0 < quarticGauge p w := by
  have hS := analyticRow_pos (by norm_num : (0 : ℝ) < 4) ((one_lt_inv₀ hw).mpr hw₁)
  have hSin := Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hw)
    (by nlinarith only [Real.pi_pos, mul_pos Real.pi_pos (sub_pos.mpr hw₁)])
  exact mul_pos (Real.sqrt_pos.mpr (div_pos hw hS)) (Real.rpow_pos_of_pos hSin _)

theorem quarticGauge_log {p w : ℝ} (hw : 0 < w) (hw₁ : w < 1) :
    2 * Real.log (quarticGauge p w) =
      Real.log w - Real.log (analyticRow 4 w⁻¹) + (p - 4) * Real.log (Real.sin (Real.pi * w)) := by
  have hS := analyticRow_pos (by norm_num : (0 : ℝ) < 4) ((one_lt_inv₀ hw).mpr hw₁)
  have hSin := Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hw)
    (by nlinarith only [Real.pi_pos, mul_pos Real.pi_pos (sub_pos.mpr hw₁)])
  have hQ := div_pos hw hS
  rw [quarticGauge, Real.log_mul (Real.sqrt_pos.mpr hQ).ne' (Real.rpow_pos_of_pos hSin _).ne',
    Real.log_sqrt hQ.le, Real.log_div hw.ne' hS.ne', Real.log_rpow hSin]
  ring

theorem quartic_anchor {n : ℕ} {w : Fin n → ℝ} (hw : ∀ i, 0 < w i)
    (hw₁ : ∀ i, w i < 1) (hW : (∑ i, w i) = 1) :
    quarticZ 4 w ≤ 1 := by
  have h := cellEnergy_le hw hw₁ hW (by norm_num : (0 : ℝ) < 4) (fun i => quarticGauge 4 (w i))
  change quarticZ 4 w ≤ _ at h
  have hTerm (i : Fin n) : quarticGauge 4 (w i) ^ 2 * analyticRow 4 (w i)⁻¹ = w i := by
    have hS := analyticRow_pos (by norm_num : (0 : ℝ) < 4) ((one_lt_inv₀ (hw i)).mpr (hw₁ i))
    simp only [quarticGauge, sub_self, zero_div, Real.rpow_zero, mul_one,
      Real.sq_sqrt (div_nonneg (hw i).le hS.le), div_mul_cancel₀ _ hS.ne']
  rwa [sum_congr rfl (fun i _ => hTerm i), hW] at h

private theorem angularEnergy_scale {n : ℕ} (p c : ℝ) (m a : Fin n → ℝ) :
    angularEnergy p (fun i => c * m i) a = c ^ 2 * angularEnergy p m a := by
  unfold angularEnergy
  simp only [mul_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

/-- The original torque and radial rows constrain the unconstrained quartic gauge
by balancing with one common scalar. -/
theorem commonRow_le_quarticUpper {n : ℕ} {p : ℝ} (F : Configuration n p)
    (hn : 2 ≤ n) (hp : 0 < p)
    (hw₁ : ∀ i, massWeight (F.mass ∘ Tuple.sort F.phase) i < 1) :
    (2 * F.radius) ^ p * (2 * F.coefficient * F.radius ^ 2) ≤
      quarticUpper p (F.mass ∘ Tuple.sort F.phase) := by
  let σ := Tuple.sort F.phase
  let a := F.phase ∘ σ
  let m := F.mass ∘ σ
  let w := massWeight m
  let b := quarticCellAngle w
  let v (i : Fin n) := quarticGauge p (w i)
  let ell := ∑ i, w i * Real.log (m i / v i)
  let c := Real.exp ell
  have hm (i : Fin n) : 0 < m i := F.mass_pos _
  have hM := massTotal_pos (by omega) hm
  have hw (i : Fin n) : 0 < w i := div_pos (hm i) hM
  have hW := massWeight_sum_one (by omega) hm
  have hv (i : Fin n) : 0 < v i := quarticGauge_pos (hw i) (hw₁ i)
  have hc : 0 < c := Real.exp_pos _
  have ha : StrictMono a := (Tuple.monotone_sort F.phase).strictMono_of_injective
    (F.phase_injective.comp σ.injective)
  have ha₀ (i : Fin n) : 0 ≤ a i := (positiveAngle_range _).1
  have haU (i : Fin n) : a i < 2 * Real.pi := (positiveAngle_range _).2
  have he := massCells_strictMonoOn hw
  have hb (i : Fin n) : b i ∈ Ioo 0 (2 * Real.pi) :=
    center_mem he (massCells_zero w) (massCells_end hW) i
  have hBalanced : (∑ i, F.mass (σ i) * Real.log ((c * v i) / F.mass (σ i))) = 0 := by
    have hTerm (i : Fin n) :
        m i * Real.log ((c * v i) / m i) =
          massTotal m * (w i * ell - w i * Real.log (m i / v i)) := by
      rw [mul_div_assoc, Real.log_mul hc.ne' (div_pos (hv i) (hm i)).ne', Real.log_div (hv i).ne' (hm i).ne',
        Real.log_div (hm i).ne' (hv i).ne']
      change m i * (Real.log (Real.exp ell) + (Real.log (v i) - Real.log (m i))) = _
      rw [Real.log_exp]
      dsimp only [w, massWeight]
      field_simp [hM.ne']
      ring
    change (∑ i, m i * Real.log ((c * v i) / m i)) = _
    rw [sum_congr rfl (fun i _ => hTerm i), ← mul_sum, sum_sub_distrib, ← sum_mul, hW,
      one_mul, show (∑ i, w i * Real.log (m i / v i)) = ell from rfl, sub_self, mul_zero]
  have hTrial := F.joint_trial_energy_le hp a b (fun i => c * v i) σ ha ha₀ haU
    (fun i => F.phase_eq (σ i)) (center_strictMono he) (fun i => (hb i).1.le) (fun i => (hb i).2)
    (fun i => mul_pos hc (hv i)) hBalanced
  have hInitial :
      angularEnergy p m a = massTotal m * ((2 * F.radius) ^ p * (2 * F.coefficient * F.radius ^ 2)) := by
    unfold angularEnergy
    have hRow (i : Fin n) : (∑ j, m i * m j * angularCost p (halfArc a i j)) =
        m i * ((2 * F.radius) ^ p * (2 * F.coefficient * F.radius ^ 2)) := by
      simp only [mul_assoc, ← mul_sum]
      change m i * (∑ j, F.mass (σ j) * angularCost p (halfArc a i j)) = _
      rw [F.weighted_radial_row hp a σ ha ha₀ haU (fun i => F.phase_eq (σ i)) i]
      ring
    simp only [hRow, ← sum_mul]
    rfl
  rw [hInitial, angularEnergy_scale] at hTrial
  have hExp : c ^ 2 = Real.exp (2 * ell) := by
    rw [← Real.exp_nat_mul]
    norm_num
  change _ ≤ quarticZ p w / massTotal m * Real.exp (2 * ell)
  rw [← hExp, div_mul_eq_mul_div, mul_comm (quarticZ p w)]
  exact (le_div_iff₀ hM).mpr (by simpa only [mul_comm _ (massTotal m)] using hTrial)

end ACS12.NativeCells

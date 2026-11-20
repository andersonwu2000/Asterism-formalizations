import ACS12.PressurePairCalibration
import ACS12.PressurePairHolder

/-! Original balanced trial and pristine source necessity before the signed receiver. -/
namespace ACS12.Pressure

open Set CenteredCircle.AllN
open NativeCells (analyticRow analyticRow_pos logRowMean logRowMean_pos massCells massCells_zero
  massCells_end massCells_strictMonoOn center center_mem center_strictMono cellEnergy_le)

private noncomputable def massRow (p M x : ℝ) : ℝ := x * analyticRow p (M / x)

private theorem massRow_pos {p M x : ℝ} (hp : 0 < p) (hx : 0 < x) (hM : x < M) :
    0 < massRow p M x := mul_pos hx (analyticRow_pos hp ((one_lt_div hx).mpr hM))

private theorem log_massRow {p M x : ℝ} (hp : 0 < p) (hx : 0 < x) (hM : x < M) :
    Real.log (massRow p M x) =
      Real.log (pressureLogCountRow p (Real.log (M / x))) + p * Real.log M + (1 - p) * Real.log x := by
  have hM₀ := hx.trans hM
  have hD := div_pos hM₀ hx
  have hR := analyticRow_pos hp ((one_lt_div hx).mpr hM)
  unfold pressureLogCountRow massRow
  rw [Real.exp_log hD,Real.log_mul (Real.exp_ne_zero _) hR.ne',Real.log_exp,
    Real.log_div hM₀.ne' hx.ne',Real.log_mul hx.ne' hR.ne']
  ring

noncomputable def geometricPressureRow {n : ℕ} {p : ℝ} (F : Configuration n p) : ℝ :=
  let m := sortedPressureMass F
  massRow p (massTotal m) (massGeometricMean m)

theorem geometricPressureRow_pos {n : ℕ} {p : ℝ} (hp : 0 < p) (hn : 2 ≤ n) (F : Configuration n p) :
    0 < geometricPressureRow F :=
  massRow_pos hp (Real.exp_pos _) (massGeometricMean_lt_total hn (fun i => F.mass_pos (Tuple.sort F.phase i)))

noncomputable def pressureTrialMass {n : ℕ} {p : ℝ} (F : Configuration n p) (i : Fin n) : ℝ :=
  let m := sortedPressureMass F
  let V := logRowMean p m
  m i * Real.exp ((Real.log V - Real.log (massRow p (massTotal m) (m i))) / 2)

theorem pressureTrialMass_pos {n : ℕ} {p : ℝ} (F : Configuration n p) (i : Fin n) :
    0 < pressureTrialMass F i := by
  unfold pressureTrialMass
  exact mul_pos (F.mass_pos (Tuple.sort F.phase i)) (Real.exp_pos _)

private theorem pressureTrial_cell_le {n : ℕ} {p : ℝ} (hp : 0 < p) (hn : 2 ≤ n) (F : Configuration n p) :
    let m := sortedPressureMass F
    let w := massWeight m
    angularEnergy p (pressureTrialMass F) (fun i => center (massCells w) i) ≤
      massTotal m * logRowMean p m := by
  dsimp only
  let m := sortedPressureMass F
  let w := massWeight m
  let V := logRowMean p m
  let v := pressureTrialMass F
  have hm (i : Fin n) : 0 < m i := F.mass_pos _
  have hM := massTotal_pos (by omega) hm
  have hw (i : Fin n) : 0 < w i := div_pos (hm i) hM
  have hw' (i : Fin n) : w i < 1 := (div_lt_one hM).mpr (massTotal_gt_mass hn hm i)
  have hW := massWeight_sum_one (by omega) hm
  have h := cellEnergy_le hw hw' hW hp v
  have hT (i : Fin n) : v i ^ 2 * analyticRow p (w i)⁻¹ = m i * V := by
    let Z := massRow p (massTotal m) (m i)
    have hZ : 0 < Z := massRow_pos hp (hm i) (massTotal_gt_mass hn hm i)
    have hS : analyticRow p (w i)⁻¹ = analyticRow p (massTotal m / m i) := by
      unfold w massWeight
      rw [inv_div]
    change (m i * Real.exp ((Real.log V - Real.log Z) / 2)) ^ 2 * analyticRow p (w i)⁻¹ = _
    rw [hS,mul_pow,← Real.exp_nat_mul,Nat.cast_ofNat,
      show (2 : ℝ) * ((Real.log V - Real.log Z) / 2) = Real.log V - Real.log Z by ring,
      Real.exp_sub,Real.exp_log (logRowMean_pos _ _),Real.exp_log hZ]
    have hZ' : analyticRow p (massTotal m / m i) ≠ 0 := (analyticRow_pos hp
      ((one_lt_div (hm i)).mpr (massTotal_gt_mass hn hm i))).ne'
    unfold Z massRow
    field_simp [(hm i).ne',hZ']
    rfl
  simp only [hT,← Finset.sum_mul] at h
  exact h

theorem pressureTrial_pairMoment {n : ℕ} {p : ℝ} (hp : 0 < p) (hn : 2 ≤ n)
    (F : Configuration n p) (i j : Fin n) :
    let m := sortedPressureMass F
    let v := pressureTrialMass F
    let V := logRowMean p m
    let a := 1 / (p + 1)
    originalPairLaw F i j * ((v i / m i) * (v j / m j)) ^ a =
      (V / geometricPressureRow F) ^ a * (pairFlatWeight F i j * Real.exp (pairRowLog F i j)) := by
  dsimp only
  let m := sortedPressureMass F
  let v := pressureTrialMass F
  let V := logRowMean p m
  let G := geometricPressureRow F
  let a : ℝ := 1 / (p + 1)
  let c : ℝ := (p - 1) / (2 * (p + 1))
  let g := massGeometricMean m
  let Z := massRow p (massTotal m)
  let X := centeredLogMass m
  let φ (s : ℝ) := Real.log (pressureLogCountRow p s)
  let s₀ := pressureRowOrigin F
  have hm (k : Fin n) : 0 < m k := F.mass_pos _
  have hg : 0 < g := Real.exp_pos _
  have hG : 0 < G := geometricPressureRow_pos hp hn F
  have hV : 0 < V := logRowMean_pos _ _
  have hX (k : Fin n) : X k = Real.log g - Real.log (m k) := Real.log_div hg.ne' (hm k).ne'
  have hΔ (k : Fin n) : Real.log G - Real.log (Z (m k)) = φ s₀ - φ (s₀ + X k) - (p - 1) * X k := by
    change Real.log (Z g) - Real.log (Z (m k)) = _
    rw [log_massRow hp hg (massGeometricMean_lt_total hn hm),
      log_massRow hp (hm k) (massTotal_gt_mass hn hm k)]
    change φ s₀ + p * Real.log (massTotal m) + (1 - p) * Real.log g -
        (φ (Real.log (massTotal m / m k)) + p * Real.log (massTotal m) + (1 - p) * Real.log (m k)) = _
    rw [show s₀ + X k = Real.log (massTotal m / m k) from pressureRowOrigin_add F hn k,hX]
    ring
  have hRatio (k : Fin n) : v k / m k = Real.exp ((Real.log V - Real.log (Z (m k))) / 2) := by
    unfold v pressureTrialMass
    change m k * _ / m k = _
    rw [mul_div_cancel_left₀ _ (hm k).ne']
  change originalPairLaw F i j * ((v i / m i) * (v j / m j)) ^ a =
    (V / G) ^ a * ((originalPairLaw F i j * Real.exp (-c * (X i + X j))) *
      Real.exp (a * (φ s₀ - (φ (s₀ + X i) + φ (s₀ + X j)) / 2)))
  rw [hRatio,hRatio,← Real.exp_add,← Real.exp_mul,Real.rpow_def_of_pos (div_pos hV hG),Real.log_div hV.ne' hG.ne']
  have hE : ((Real.log V - Real.log (Z (m i))) / 2 + (Real.log V - Real.log (Z (m j))) / 2) * a =
      (Real.log V - Real.log G) * a + (-c) * (X i + X j) +
        a * (φ s₀ - (φ (s₀ + X i) + φ (s₀ + X j)) / 2) := by
    have hC : c = a * (p - 1) / 2 := by
      unfold a c
      field_simp [show p + 1 ≠ 0 by positivity]
    rw [hC]
    linear_combination (a / 2) * hΔ i + (a / 2) * hΔ j
  rw [hE,Real.exp_add,Real.exp_add]
  ring

theorem pressure_pristine_calibrated_le {n : ℕ} {p : ℝ} (hp : 0 < p) (hn : 2 ≤ n) (F : Configuration n p) :
    originalPressureRow F * (pairFlatTotal F * pairRowFactor F) ^ (p + 1) ≤ geometricPressureRow F := by
  let m := sortedPressureMass F
  let w := massWeight m
  let V := logRowMean p m
  let G := geometricPressureRow F
  let v := pressureTrialMass F
  let φ (i : Fin n) := center (massCells w) i
  let a : ℝ := 1 / (p + 1)
  have hM : 0 < massTotal m := massTotal_pos (by omega) (fun i => F.mass_pos _)
  have hG : 0 < G := geometricPressureRow_pos hp hn F
  have hV : 0 < V := logRowMean_pos _ _
  have hQ := zero_lt_one.trans_le (pairFlatTotal_ge_one hp hn F)
  have hW := massWeight_sum_one (show 0 < n by omega) (show ∀ i, 0 < m i from fun i => F.mass_pos _)
  have he := massCells_strictMonoOn (w := w) (fun i => div_pos (F.mass_pos _) hM)
  have hφ (i : Fin n) : φ i ∈ Ioo 0 (2 * Real.pi) :=
    center_mem he (massCells_zero w) (massCells_end hW) i
  have hArc : ∀ i j, j ≠ i → halfArc φ i j ∈ Ioo 0 Real.pi :=
    fun i j h => halfArc_mem (center_strictMono he) (fun k => (hφ k).1.le) (fun k => (hφ k).2) h
  have hH := (originalPair_holder hp hn F v φ (pressureTrialMass_pos F) hArc).trans (pressureTrial_cell_le hp hn F)
  change massTotal m * originalPressureRow F *
    (∑ i, ∑ j, originalPairLaw F i j * ((v i / m i) * (v j / m j)) ^ a) ^ (p + 1) ≤ massTotal m * V at hH
  have hT (i j : Fin n) :
      originalPairLaw F i j * ((v i / m i) * (v j / m j)) ^ a =
        (V / G) ^ a * (pairFlatWeight F i j * Real.exp (pairRowLog F i j)) :=
    pressureTrial_pairMoment hp hn F i j
  simp only [hT,← Finset.mul_sum] at hH
  have hE : (∑ i, ∑ j, pairFlatWeight F i j * Real.exp (pairRowLog F i j)) =
      pairFlatTotal F * pairRowFactor F := by
    unfold pairRowFactor
    field_simp [hQ.ne']
  have hQB : 0 ≤ pairFlatTotal F * pairRowFactor F := by
    rw [← hE]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg ((originalPairLaw_marginals hp hn F).1 i j) (Real.exp_pos _).le)
        (Real.exp_pos _).le
  rw [hE,Real.mul_rpow (Real.rpow_nonneg (div_nonneg hV.le hG.le) a) hQB,
    ← Real.rpow_mul (div_nonneg hV.le hG.le),
    show a * (p + 1) = 1 by unfold a; field_simp,Real.rpow_one] at hH
  have h := (mul_le_mul_iff_right₀ hM).mp (by simpa only [mul_assoc] using hH)
  apply (mul_le_mul_iff_right₀ (div_pos hV hG)).mp
  have hCancel : V / G * G = V := div_mul_cancel₀ _ hG.ne'
  rw [hCancel]
  nlinarith only [h]

theorem pressure_pristine_lt {n : ℕ} {p : ℝ} (hp : 1 < p) (hp₂ : p ≤ 2) (hn : 2 ≤ n)
    (F : Configuration n p) (hWord : ∃ i j, sortedPressureMass F i ≠ sortedPressureMass F j) :
    originalPressureRow F * pairFlatTotal F ^ (p + 1) < geometricPressureRow F := by
  have hP := zero_lt_one.trans hp
  have hQ := zero_lt_one.trans_le (pairFlatTotal_ge_one hP hn F)
  have hB' : pairFlatTotal F < pairFlatTotal F * pairRowFactor F :=
    by simpa only [mul_one] using mul_lt_mul_of_pos_left (pairRowFactor_gt_one hp hp₂ hn F hWord) hQ
  have h := Real.rpow_lt_rpow hQ.le hB' (show 0 < p + 1 by positivity)
  exact (mul_lt_mul_of_pos_left h (originalPressureRow_pos hn F)).trans_le (pressure_pristine_calibrated_le hP hn F)

theorem pressure_pristine_le {n : ℕ} {p : ℝ} (hp : 1 < p) (hp₂ : p ≤ 2) (hn : 2 ≤ n)
    (F : Configuration n p) :
    originalPressureRow F * pairFlatTotal F ^ (p + 1) ≤ geometricPressureRow F := by
  by_cases hWord : ∃ i j, sortedPressureMass F i ≠ sortedPressureMass F j
  · exact (pressure_pristine_lt hp hp₂ hn F hWord).le
  push Not at hWord
  let m := sortedPressureMass F
  have hm (i : Fin n) : 0 < m i := F.mass_pos _
  let i₀ : Fin n := ⟨0,by omega⟩
  have hMass (i : Fin n) : m i = m i₀ := hWord i i₀
  have hMean : massGeometricMean m = m i₀ := by
    unfold massGeometricMean
    rw [Finset.sum_congr rfl (fun i _ => congrArg (fun x => massWeight m i * Real.log x) (hMass i)),
      ← Finset.sum_mul,massWeight_sum_one (show 0 < n by omega) hm,
      one_mul,Real.exp_log (hm i₀)]
  have hX (i : Fin n) : centeredLogMass m i = 0 := by
    unfold centeredLogMass
    rw [hMean,hMass i,div_self (hm i₀).ne',Real.log_one]
  have hF : pairRowFactor F = 1 := by
    unfold pairRowFactor
    have hLog (i j : Fin n) : pairRowLog F i j = 0 := by
      unfold pairRowLog
      simp only [show centeredLogMass (sortedPressureMass F) = centeredLogMass m from rfl,hX,add_zero]
      ring
    simp only [hLog,Real.exp_zero,mul_one]
    exact div_self (zero_lt_one.trans_le (pairFlatTotal_ge_one (zero_lt_one.trans hp) hn F)).ne'
  simpa only [hF,mul_one] using pressure_pristine_calibrated_le (zero_lt_one.trans hp) hn F

end ACS12.Pressure


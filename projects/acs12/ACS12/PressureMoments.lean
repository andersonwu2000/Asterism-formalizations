import ACS12.PressureCurvature
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! The complete moment comparison under the original finite mass law in PM0–4. -/
namespace ACS12.Pressure

open Set

noncomputable def massTotal {n : ℕ} (m : Fin n → ℝ) : ℝ := ∑ i, m i

noncomputable def massWeight {n : ℕ} (m : Fin n → ℝ) (i : Fin n) : ℝ := m i / massTotal m

noncomputable def massGeometricMean {n : ℕ} (m : Fin n → ℝ) : ℝ :=
  Real.exp (∑ i, massWeight m i * Real.log (m i))

noncomputable def centeredLogMass {n : ℕ} (m : Fin n → ℝ) (i : Fin n) : ℝ :=
  Real.log (massGeometricMean m / m i)

noncomputable def centeredMoment {n : ℕ} (m : Fin n → ℝ) (c : ℝ) : ℝ :=
  ∑ i, massWeight m i * Real.exp (c * centeredLogMass m i)

theorem massTotal_pos {n : ℕ} (hn : 0 < n) {m : Fin n → ℝ} (hm : ∀ i, 0 < m i) :
    0 < massTotal m := by
  exact Finset.sum_pos (fun i _ => hm i) ⟨⟨0, hn⟩, Finset.mem_univ _⟩

theorem massWeight_sum_one {n : ℕ} (hn : 0 < n) {m : Fin n → ℝ} (hm : ∀ i, 0 < m i) :
    (∑ i, massWeight m i) = 1 := by
  unfold massWeight
  rw [← Finset.sum_div, ← massTotal, div_self (massTotal_pos hn hm).ne']

theorem centeredLogMass_mean_zero {n : ℕ} (hn : 0 < n) {m : Fin n → ℝ} (hm : ∀ i, 0 < m i) :
    (∑ i, massWeight m i * centeredLogMass m i) = 0 := by
  have hg : 0 < massGeometricMean m := Real.exp_pos _
  simp_rw [centeredLogMass, Real.log_div hg.ne' (hm _).ne', mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, massWeight_sum_one hn hm, one_mul, massGeometricMean,
    Real.log_exp, sub_self]

theorem centeredMoment_ge_one {n : ℕ} (hn : 0 < n) {m : Fin n → ℝ} (hm : ∀ i, 0 < m i) (c : ℝ) :
    1 ≤ centeredMoment m c := by
  unfold centeredMoment
  have h : (∑ i, massWeight m i * (c * centeredLogMass m i + 1)) ≤
      ∑ i, massWeight m i * Real.exp (c * centeredLogMass m i) :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (Real.add_one_le_exp _)
      (div_nonneg (hm i).le (massTotal_pos hn hm).le))
  simp only [mul_add, mul_one] at h
  rw [Finset.sum_add_distrib, massWeight_sum_one hn hm] at h
  have hX : (∑ i, massWeight m i * (c * centeredLogMass m i)) = 0 := by
    calc
      _ = c * ∑ i, massWeight m i * centeredLogMass m i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = _ := by rw [centeredLogMass_mean_zero hn hm, mul_zero]
  simpa only [hX, zero_add] using h

theorem centeredMoment_mass_power {n : ℕ} (hn : 0 < n) {m : Fin n → ℝ} (hm : ∀ i, 0 < m i) (c : ℝ) :
    centeredMoment m c = massGeometricMean m ^ c / massTotal m * ∑ i, m i ^ (1 - c) := by
  have hg : 0 < massGeometricMean m := Real.exp_pos _
  unfold centeredMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hE : Real.exp (c * centeredLogMass m i) = (massGeometricMean m / m i) ^ c := by
    rw [centeredLogMass, Real.rpow_def_of_pos (div_pos hg (hm i)), mul_comm]
  rw [hE, Real.div_rpow hg.le (hm i).le, Real.rpow_sub (hm i) 1, Real.rpow_one]
  unfold massWeight
  field_simp [(massTotal_pos hn hm).ne', (Real.rpow_pos_of_pos (hm i) c).ne']

private theorem centeredLogMass_lt_cap {n : ℕ} (hn : 0 < n) {m : Fin n → ℝ}
    (hm : ∀ i, 0 < m i) (hFloor : ∀ i, 1 / 16 < m i) (hCap : ∀ i, m i ≤ 1) (i : Fin n) :
    centeredLogMass m i < 111 / 40 := by
  have hg₀ : 0 < massGeometricMean m := Real.exp_pos _
  have hg : massGeometricMean m ≤ 1 := by
    unfold massGeometricMean
    apply Real.exp_le_one_iff.mpr
    exact Finset.sum_nonpos (fun j _ =>
      mul_nonpos_of_nonneg_of_nonpos (div_nonneg (hm j).le (massTotal_pos hn hm).le)
        (Real.log_nonpos (hm j).le (hCap j)))
  have h : massGeometricMean m / m i < 16 := (div_lt_iff₀ (hm i)).mpr (by linarith only [hFloor i, hg])
  exact (Real.log_lt_log (div_pos hg₀ (hm i)) h).trans pressure_log16_lt_cap

theorem centeredMoment_curvature_le {n : ℕ} (hn : 0 < n) {m : Fin n → ℝ}
    (hm : ∀ i, 0 < m i) (hFloor : ∀ i, 1 / 16 < m i) (hCap : ∀ i, m i ≤ 1)
    {p : ℝ} (hp : 9 / 5 ≤ p) (hP : p ≤ 2) :
    1 + (18 / 25) / (p + 1) * (centeredMoment m 1 - 1) ≤ centeredMoment m (p / (p + 1)) := by
  let c := p / (p + 1)
  let w := massWeight m
  let X := centeredLogMass m
  have hX := centeredLogMass_mean_zero hn hm
  change (∑ i, w i * X i) = 0 at hX
  have hW := massWeight_sum_one hn hm
  change (∑ i, w i) = 1 at hW
  have h : 0 ≤ ∑ i, w i * momentCurvature p (X i) := by
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (div_nonneg (hm i).le (massTotal_pos hn hm).le)
    by_cases hi : X i = 0
    · rw [hi, momentCurvature_zero]
    · exact (momentCurvature_pos hp hP (centeredLogMass_lt_cap hn hm hFloor hCap i).le hi).le
  have hA (k : ℝ) : (∑ i, w i * entropyExp (k * X i)) = centeredMoment m k - 1 := by
    simp only [entropyExp, mul_sub, Finset.sum_sub_distrib, mul_one]
    have hSum : (∑ i, w i * (k * X i)) = 0 := by
      calc
        _ = k * ∑ i, w i * X i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => by ring)
        _ = _ := by rw [hX, mul_zero]
    rw [hSum, hW, sub_zero]
    rfl
  have hVal : (∑ i, w i * momentCurvature p (X i)) =
      (p + 1) * (centeredMoment m c - 1) - (18 / 25) * (centeredMoment m 1 - 1) := by
    rw [← hA c, ← hA 1, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [momentCurvature, c, one_mul]
    ring
  rw [hVal] at h
  have hDen : 0 < p + 1 := by linarith only [hp]
  change 1 + (18 / 25) / (p + 1) * (centeredMoment m 1 - 1) ≤ centeredMoment m c
  apply (le_of_mul_le_mul_right _ hDen)
  rw [add_mul, one_mul]
  have hE : (18 / 25) / (p + 1) * (centeredMoment m 1 - 1) * (p + 1) =
      (18 / 25) * (centeredMoment m 1 - 1) := by
    rw [mul_right_comm, div_mul_cancel₀ _ hDen.ne']
  rw [hE]
  nlinarith only [h]

private theorem rpow_one_add_quadratic {a x : ℝ} (ha : 2 ≤ a) (hx : 0 ≤ x) :
    1 + a * x + a * (a - 1) * x ^ 2 / 2 ≤ (1 + x) ^ a := by
  let f (t : ℝ) := (1 + t) ^ a - (1 + a * t + a * (a - 1) * t ^ 2 / 2)
  let D (t : ℝ) := a * (1 + t) ^ (a - 1) - a - a * (a - 1) * t
  let E (t : ℝ) := a * (a - 1) * ((1 + t) ^ (a - 2) - 1)
  have hd (t : ℝ) (ht : 0 ≤ t) : HasDerivAt f (D t) t := by
    have h := hasDerivAt_id t
    have hp := (h.const_add 1).rpow_const (p := a) (Or.inl (by positivity))
    have hP := ((h.const_mul a).const_add 1).add (((h.pow 2).const_mul (a * (a - 1))).div_const 2)
    convert hp.sub hP using 1
    norm_num [D, id_eq]; ring
  have he (t : ℝ) (ht : 0 ≤ t) : HasDerivAt D (E t) t := by
    have h := hasDerivAt_id t
    have hp := (h.const_add 1).rpow_const (p := a - 1) (Or.inl (by positivity))
    convert (((hp.const_mul a).sub_const a).sub (h.const_mul (a * (a - 1)))) using 1
    simp only [E, id_eq, mul_one, show a - 1 - 1 = a - 2 by ring]
    ring
  have hD : MonotoneOn D (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · exact fun t ht => (he t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (he t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : 0 ≤ t := show t ∈ Ici (0 : ℝ) from interior_subset ht
      rw [(he t ht').deriv]
      apply mul_nonneg (mul_nonneg (by linarith only [ha]) (by linarith only [ha]))
      exact sub_nonneg.mpr (Real.one_le_rpow (by linarith only [ht']) (sub_nonneg.mpr ha))
  have h₀ : D 0 = 0 := by simp [D]
  have hF : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : 0 ≤ t := show t ∈ Ici (0 : ℝ) from interior_subset ht
      rw [(hd t ht').deriv, ← h₀]
      exact hD (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht') ht'
  have hF₀ : f 0 = 0 := by simp [f]
  exact sub_nonneg.mp (hF₀ ▸ hF (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx) hx)

theorem centeredMoment_polynomial_le {n : ℕ} (hn : 0 < n) {m : Fin n → ℝ}
    (hm : ∀ i, 0 < m i) (hFloor : ∀ i, 1 / 16 < m i) (hCap : ∀ i, m i ≤ 1)
    {p : ℝ} (hp : 9 / 5 ≤ p) (hP : p ≤ 2) :
    let u := centeredMoment m 1 - 1
    1 + (18 / 25) * u + (2916 / 17500) * u ^ 2 ≤ centeredMoment m (p / (p + 1)) ^ (p + 1) := by
  let u := centeredMoment m 1 - 1
  let x := (18 / 25) / (p + 1) * u
  have hu : 0 ≤ u := sub_nonneg.mpr (centeredMoment_ge_one hn hm 1)
  have hP₀ : 0 < p + 1 := by linarith only [hp]
  have hx : 0 ≤ x := mul_nonneg (div_nonneg (by norm_num) hP₀.le) hu
  have hC := centeredMoment_curvature_le hn hm hFloor hCap hp hP
  change 1 + x ≤ _ at hC
  have hPow := Real.rpow_le_rpow (by linarith only [hx] : 0 ≤ 1 + x) hC hP₀.le
  have hPoly := rpow_one_add_quadratic (a := p + 1) (by linarith only [hp]) hx
  have hβ : 9 / 14 ≤ p / (p + 1) := (le_div_iff₀ hP₀).mpr (by linarith only [hp])
  have hβ' := mul_le_mul_of_nonneg_right hβ (show 0 ≤ (18 / 25 : ℝ) ^ 2 / 2 * u ^ 2 by positivity)
  have hEq : 1 + (p + 1) * x + (p + 1) * p * x ^ 2 / 2 =
      1 + (18 / 25) * u + (p / (p + 1)) * ((18 / 25) ^ 2 / 2 * u ^ 2) := by
    dsimp only [x]
    field_simp [hP₀.ne']
  have h := hPoly.trans hPow
  rw [add_sub_cancel_right, hEq] at h
  change 1 + 18 / 25 * u + 2916 / 17500 * u ^ 2 ≤ _
  nlinarith only [h,hβ']

theorem centeredMoment_ratio_gt {n : ℕ} (hn : 0 < n) {m : Fin n → ℝ}
    (hm : ∀ i, 0 < m i) (hFloor : ∀ i, 1 / 16 < m i) (hCap : ∀ i, m i ≤ 1)
    {p : ℝ} (hp : 9 / 5 ≤ p) (hP : p ≤ 2) :
    13 / 14 < centeredMoment m (p / (p + 1)) ^ (p + 1) / centeredMoment m 1 := by
  let u := centeredMoment m 1 - 1
  have h := centeredMoment_polynomial_le hn hm hFloor hCap hp hP
  have hT : 0 < centeredMoment m 1 := zero_lt_one.trans_le (centeredMoment_ge_one hn hm 1)
  have hQ : (13 / 14) * (1 + u) < 1 + (18 / 25) * u + (2916 / 17500) * u ^ 2 := by
    nlinarith only [sq_nonneg (u - (1825 / 2916 : ℝ))]
  apply (lt_div_iff₀ hT).mpr
  change 1 + 18 / 25 * u + 2916 / 17500 * u ^ 2 ≤ _ at h
  have hE : centeredMoment m 1 = 1 + u := by dsimp only [u]; ring
  exact hE ▸ hQ.trans_le h

theorem centeredMoment_coefficient_gt {n : ℕ} (hn : 0 < n) {m : Fin n → ℝ}
    (hm : ∀ i, 0 < m i) (hFloor : ∀ i, 1 / 16 < m i) (hCap : ∀ i, m i ≤ 1)
    {p : ℝ} (hp : 9 / 5 ≤ p) (hP : p ≤ 2) :
    1521 / 800 < (centeredMoment m (p / (p + 1)) ^ (p + 1) / centeredMoment m 1) *
      (1 + centeredMoment m 1 ^ (1 / (p + 1))) := by
  let t := centeredMoment m 1
  let u := t - 1
  let a := 1 / (p + 1)
  let K := centeredMoment m (p / (p + 1)) ^ (p + 1)
  let Q := 1 + (18 / 25) * u + (4 / 25) * u ^ 2
  have ht₁ : 1 ≤ t := centeredMoment_ge_one hn hm 1
  have ht : 0 < t := zero_lt_one.trans_le ht₁
  have hu : 0 ≤ u := sub_nonneg.mpr ht₁
  have hD : 0 < p + 1 := by linarith only [hp]
  have ha : (1 / 3 : ℝ) ≤ a := (le_div_iff₀ hD).mpr (by linarith only [hP])
  have ha₀ : 0 < a := one_div_pos.mpr hD
  have hU : 0 ≤ 1 - t⁻¹ := by
    have h := inv_le_one_of_one_le₀ ht₁
    linarith only [h]
  have hG := mul_le_mul ha (Real.one_sub_inv_le_log_of_pos ht) hU ha₀.le
  have hExp := Real.add_one_le_exp (Real.log t * a)
  have hPow : 1 + u / (3 * t) ≤ t ^ a := by
    have hE : (1 / 3) * (1 - t⁻¹) = u / (3 * t) := by
      dsimp only [u]
      field_simp [ht.ne']
    rw [Real.rpow_def_of_pos ht, ← hE]
    nlinarith only [hG,hExp]
  have hK : Q ≤ K := by
    have h := centeredMoment_polynomial_le hn hm hFloor hCap hp hP
    change 1 + 18 / 25 * u + 2916 / 17500 * u ^ 2 ≤ K at h
    dsimp only [Q]
    nlinarith only [h,sq_nonneg u]
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hSum : 1 + (1 + u / (3 * t)) ≤ 1 + t ^ a := by linarith only [hPow]
  have h := mul_le_mul (div_le_div_of_nonneg_right hK ht.le) hSum
    (by positivity : 0 ≤ 1 + (1 + u / (3 * t))) (div_nonneg (hQ.trans hK) ht.le)
  have hMain : (6 + 7 * u) * Q / (3 * t ^ 2) ≤ (K / t) * (1 + t ^ a) := by
    refine le_trans (le_of_eq ?_) h
    have htE : t = 1 + u := by dsimp only [u]; ring
    field_simp [ht.ne']
    linear_combination -(6 * Q) * htE
  have hNum : 0 < 237 - 70 * u + 237 * u ^ 2 + 896 * u ^ 3 := by
    nlinarith only [sq_nonneg (u - 1),hu,pow_nonneg hu 3,sq_nonneg (u - (35 / 237 : ℝ))]
  have hDiff : (6 + 7 * u) * Q / (3 * t ^ 2) - 1521 / 800 =
      (237 - 70 * u + 237 * u ^ 2 + 896 * u ^ 3) / (2400 * t ^ 2) := by
    dsimp only [Q]
    have htE : t = 1 + u := by dsimp only [u]; ring
    rw [htE]
    field_simp [(show 1 + u ≠ 0 by positivity)]
    ring
  have hStrict : 1521 / 800 < (6 + 7 * u) * Q / (3 * t ^ 2) :=
    sub_pos.mp (hDiff.symm ▸ div_pos hNum (by positivity))
  exact hStrict.trans_le hMain

end ACS12.Pressure

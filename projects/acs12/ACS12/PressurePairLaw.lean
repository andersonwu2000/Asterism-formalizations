import ACS12.NativeNormalization
import ACS12.PressureRowSurplus

/-! The directed pressure pair law from the original physical radial row. -/
namespace ACS12.Pressure

open Set CenteredCircle.AllN

noncomputable def pairLaw {n : ℕ} (p C : ℝ) (m θ : Fin n → ℝ) (i j : Fin n) : ℝ :=
  m i * m j * angularCost p (halfArc θ i j) / (massTotal m * C)

theorem pairLaw_nonneg {n : ℕ} {p C : ℝ} {m θ : Fin n → ℝ} (hm : ∀ i, 0 < m i)
    (hC : 0 < C) (hp : 0 < p)
    (hAngle : ∀ i j, j ≠ i → halfArc θ i j ∈ Ioo 0 Real.pi) (i j : Fin n) : 0 ≤ pairLaw p C m θ i j := by
  have hM : 0 ≤ massTotal m := Finset.sum_nonneg (fun i _ => (hm i).le)
  have hK : 0 ≤ angularCost p (halfArc θ i j) := by
    by_cases h : j = i
    · subst j
      simp [halfArc_self,angularCost,Real.zero_rpow hp.ne']
    · exact one_div_nonneg.mpr (Real.rpow_nonneg
        (Real.sin_pos_of_pos_of_lt_pi (hAngle i j h).1 (hAngle i j h).2).le _)
  unfold pairLaw
  exact div_nonneg (mul_nonneg (mul_nonneg (hm i).le (hm j).le) hK) (mul_nonneg hM hC.le)

theorem pairLaw_symm {n : ℕ} (p C : ℝ) (m θ : Fin n → ℝ) (i j : Fin n) :
    pairLaw p C m θ i j = pairLaw p C m θ j i := by
  by_cases h : i = j
  · subst j
    rfl
  unfold pairLaw angularCost
  rw [halfArc_reverse θ h,Real.sin_pi_sub,mul_comm (m i) (m j)]

theorem pairLaw_diag {n : ℕ} {p : ℝ} (hp : 0 < p) (C : ℝ) (m θ : Fin n → ℝ) (i : Fin n) :
    pairLaw p C m θ i i = 0 := by
  simp only [pairLaw,halfArc_self,angularCost,Real.sin_zero,Real.zero_rpow hp.ne',div_zero,mul_zero,zero_div]

theorem pairLaw_marginal_left {n : ℕ} {p C : ℝ} {m θ : Fin n → ℝ} (hC : 0 < C)
    (hRow : ∀ i, (∑ j, m j * angularCost p (halfArc θ i j)) = C) (i : Fin n) :
    (∑ j, pairLaw p C m θ i j) = massWeight m i := by
  unfold pairLaw massWeight
  simp only [← Finset.sum_div,mul_assoc,← Finset.mul_sum,hRow]
  rw [mul_div_mul_right _ _ hC.ne']

theorem pairLaw_marginal_right {n : ℕ} {p C : ℝ} {m θ : Fin n → ℝ} (hC : 0 < C)
    (hRow : ∀ i, (∑ j, m j * angularCost p (halfArc θ i j)) = C) (j : Fin n) :
    (∑ i, pairLaw p C m θ i j) = massWeight m j := by
  rw [← pairLaw_marginal_left hC hRow j]
  exact Finset.sum_congr rfl fun i _ => pairLaw_symm p C m θ i j

noncomputable def sortedPressureMass {n : ℕ} {p : ℝ} (F : Configuration n p) : Fin n → ℝ :=
  F.mass ∘ Tuple.sort F.phase

noncomputable def sortedPressureAngle {n : ℕ} {p : ℝ} (F : Configuration n p) : Fin n → ℝ :=
  F.phase ∘ Tuple.sort F.phase

noncomputable def originalPressureRow {n : ℕ} {p : ℝ} (F : Configuration n p) : ℝ :=
  (2 * F.radius) ^ p * (2 * F.coefficient * F.radius ^ 2)

theorem originalPressureRow_pos {n : ℕ} {p : ℝ} (hn : 2 ≤ n) (F : Configuration n p) :
    0 < originalPressureRow F := by
  have hR := F.radius_pos
  have hC := F.coefficient_pos hn
  unfold originalPressureRow
  positivity

theorem sortedPressureAngle_mem {n : ℕ} {p : ℝ} (F : Configuration n p) {i j : Fin n} (h : j ≠ i) :
    halfArc (sortedPressureAngle F) i j ∈ Ioo 0 Real.pi := by
  have hθ : StrictMono (sortedPressureAngle F) := (Tuple.monotone_sort F.phase).strictMono_of_injective
    (F.phase_injective.comp (Tuple.sort F.phase).injective)
  exact halfArc_mem hθ (fun i => (positiveAngle_range _).1) (fun i => (positiveAngle_range _).2) h

theorem sortedPressure_radial {n : ℕ} {p : ℝ} (hp : 0 < p) (F : Configuration n p) (i : Fin n) :
    (∑ j, sortedPressureMass F j * angularCost p (halfArc (sortedPressureAngle F) i j)) =
      originalPressureRow F := by
  let σ := Tuple.sort F.phase
  have hθ : StrictMono (sortedPressureAngle F) := (Tuple.monotone_sort F.phase).strictMono_of_injective
    (F.phase_injective.comp σ.injective)
  exact F.weighted_radial_row hp (sortedPressureAngle F) σ hθ
    (fun i => (positiveAngle_range _).1) (fun i => (positiveAngle_range _).2) (fun i => F.phase_eq (σ i)) i

theorem sortedPressure_torque {n : ℕ} {p : ℝ} (hp : 0 < p) (F : Configuration n p) (i : Fin n) :
    (∑ j, sortedPressureMass F j * angularKernel p (halfArc (sortedPressureAngle F) i j)) = 0 := by
  let σ := Tuple.sort F.phase
  have hθ : StrictMono (sortedPressureAngle F) := (Tuple.monotone_sort F.phase).strictMono_of_injective
    (F.phase_injective.comp σ.injective)
  have h := F.weighted_angular_row (sortedPressureAngle F) σ hθ
    (fun i => (positiveAngle_range _).1) (fun i => (positiveAngle_range _).2) (fun i => F.phase_eq (σ i)) i
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)] at h
  simpa only [halfArc_self,angularKernel,Real.sin_zero,Real.zero_rpow (show p + 1 ≠ 0 by positivity),
    div_zero,mul_zero,sub_zero,sortedPressureMass,Function.comp_apply] using h

noncomputable def originalPairLaw {n : ℕ} {p : ℝ} (F : Configuration n p) : Fin n → Fin n → ℝ :=
  pairLaw p (originalPressureRow F) (sortedPressureMass F) (sortedPressureAngle F)

theorem originalPairLaw_marginals {n : ℕ} {p : ℝ} (hp : 0 < p) (hn : 2 ≤ n) (F : Configuration n p) :
    (∀ i j, 0 ≤ originalPairLaw F i j) ∧
    (∀ i, ∑ j, originalPairLaw F i j = massWeight (sortedPressureMass F) i) ∧
    (∀ j, ∑ i, originalPairLaw F i j = massWeight (sortedPressureMass F) j) := by
  have hC := originalPressureRow_pos hn F
  have hR := sortedPressure_radial hp F
  exact ⟨pairLaw_nonneg (fun i => F.mass_pos _) hC hp (fun _ _ h => sortedPressureAngle_mem F h),pairLaw_marginal_left hC hR,pairLaw_marginal_right hC hR⟩

end ACS12.Pressure


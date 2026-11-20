import CenteredCircle.PreliminaryMassBound
import CenteredCircle.PeriodicSourceQuadrature

/-! Circular mass caps survive both exterior distance parametrizations. -/

namespace CenteredCircle.AllN

namespace AnchoredCircleSource

variable {ι : Type*} (F : AnchoredCircleSource ι) [DecidableEq ι]

theorem leftDistance_le_period (i : ι) : F.leftDistance i ≤ F.period := by
  dsimp [leftDistance]
  linarith [F.coordinate_nonneg i]

theorem rightDistance_le_period (i : ι) : F.rightDistance i ≤ F.period := by
  by_cases hi : i = F.neighbor
  · simp [rightDistance, hi, F.coordinate_neighbor]
  · exact (F.rightDistance_lt_period hi).le

theorem leftDistance_mass_le (hcaps : F.HasCircularMassCaps) (i : ι) :
    F.mass i ≤ F.leftDistance i := by
  by_cases hi : i = F.root
  · rw [hi, F.mass_root]
    exact F.leftDistance_ge_one hcaps F.root
  · have h := (hcaps i F.root hi).2
    rw [F.coordinate_root, zero_sub, abs_neg, abs_of_nonneg (F.coordinate_nonneg i)] at h
    exact h

theorem rightDistance_mass_le (hcaps : F.HasCircularMassCaps) (i : ι) :
    F.mass i ≤ F.rightDistance i := by
  by_cases hir : i = F.root
  · simp only [hir, rightDistance, true_or, ite_true, F.mass_root, F.coordinate_root, zero_add]
    linarith [F.period_ge_two]
  · by_cases hin : i = F.neighbor
    · rw [hin]
      exact F.rightDistance_ge_neighbor hcaps F.neighbor
    · have h := (hcaps i F.neighbor hin).1
      have hp : 0 ≤ F.coordinate i - 1 := by linarith [F.other_coordinate i hir hin]
      rw [F.coordinate_neighbor, abs_sub_comm, abs_of_nonneg hp] at h
      simpa only [rightDistance, hir, hin, false_or, ite_false] using h

theorem leftDistance_circular_caps (hcaps : F.HasCircularMassCaps) (i j : ι) (hij : i ≠ j) :
    F.mass i ≤ |F.leftDistance j - F.leftDistance i| ∧
    F.mass i ≤ F.period - |F.leftDistance j - F.leftDistance i| := by
  have he : |F.leftDistance j - F.leftDistance i| = |F.coordinate j - F.coordinate i| := by
    rw [show F.leftDistance j - F.leftDistance i = -(F.coordinate j - F.coordinate i) by
      dsimp [leftDistance]; ring, abs_neg]
  rw [he]
  exact hcaps i j hij

theorem rightDistance_circular_abs (i j : ι) :
    |F.rightDistance j - F.rightDistance i| = |F.coordinate j - F.coordinate i| ∨
    |F.rightDistance j - F.rightDistance i| = F.period - |F.coordinate j - F.coordinate i| := by
  have hsmall (k : ι) (hk : k = F.root ∨ k = F.neighbor) : F.coordinate k ≤ 1 := by
    rcases hk with rfl | rfl
    · rw [F.coordinate_root]; norm_num
    · rw [F.coordinate_neighbor]
  have hlarge (k : ι) (hk : ¬(k = F.root ∨ k = F.neighbor)) : 1 < F.coordinate k :=
    F.other_coordinate k (fun h => hk (Or.inl h)) (fun h => hk (Or.inr h))
  by_cases hi : i = F.root ∨ i = F.neighbor
  · by_cases hj : j = F.root ∨ j = F.neighbor
    · left
      simp only [rightDistance, if_pos hi, if_pos hj]
      congr 1
      ring
    · right
      simp only [rightDistance, if_pos hi, if_neg hj]
      rw [abs_of_nonpos (by linarith [F.coordinate_nonneg i, F.coordinate_lt_period j]),
        abs_of_nonneg (by linarith [hsmall i hi, hlarge j hj])]
      ring
  · by_cases hj : j = F.root ∨ j = F.neighbor
    · right
      simp only [rightDistance, if_neg hi, if_pos hj]
      rw [abs_of_nonneg (by linarith [F.coordinate_nonneg j, F.coordinate_lt_period i]),
        abs_of_nonpos (by linarith [hlarge i hi, hsmall j hj])]
      ring
    · left
      simp only [rightDistance, if_neg hi, if_neg hj]
      congr 1
      ring

theorem rightDistance_circular_caps (hcaps : F.HasCircularMassCaps) (i j : ι) (hij : i ≠ j) :
    F.mass i ≤ |F.rightDistance j - F.rightDistance i| ∧
    F.mass i ≤ F.period - |F.rightDistance j - F.rightDistance i| := by
  have h := hcaps i j hij
  rcases F.rightDistance_circular_abs i j with he | he
  · rw [he]
    exact h
  · rw [he]
    constructor
    · exact h.2
    · linarith [h.1]

theorem leftDistance_injective : Function.Injective F.leftDistance := by
  intro i j h
  apply F.coordinate_injective
  dsimp [leftDistance] at h
  linarith

theorem rightDistance_injective (hcaps : F.HasCircularMassCaps) :
    Function.Injective F.rightDistance := by
  intro i j he
  by_contra hij
  have hp := (F.rightDistance_circular_caps hcaps i j hij).1
  rw [he, sub_self, abs_zero] at hp
  linarith [F.mass_pos i]

variable [Fintype ι]

theorem leftExterior_quadrature {K : ℝ → ℝ} (hK : QuadratureData K 1)
    (hcaps : F.HasCircularMassCaps) : F.leftExterior K ≤ samplingTail K 0 1 := by
  exact periodic_source_quadrature hK (by norm_num) F.period_pos F.leftDistance F.mass
    F.leftDistance_le_period (F.leftDistance_ge_one hcaps) F.leftDistance_injective
    (fun i => (F.mass_pos i).le) (F.leftDistance_mass_le hcaps)
    (F.leftDistance_circular_caps hcaps)

theorem rightExterior_quadrature {K : ℝ → ℝ} (hK : QuadratureData K (F.mass F.neighbor))
    (hcaps : F.HasCircularMassCaps) :
    F.rightExterior K ≤ samplingTail K 0 (F.mass F.neighbor) := by
  exact periodic_source_quadrature hK (F.mass_pos _) F.period_pos F.rightDistance F.mass
    F.rightDistance_le_period (F.rightDistance_ge_neighbor hcaps) (F.rightDistance_injective hcaps)
    (fun i => (F.mass_pos i).le) (F.rightDistance_mass_le hcaps)
    (F.rightDistance_circular_caps hcaps)

end AnchoredCircleSource

end CenteredCircle.AllN

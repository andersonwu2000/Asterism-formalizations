import ACS12.GammaPeano
import ACS12.GammaBoundary
import ACS12.ChartExterior

/-! The corrected radial and torque rows at every occupied site in one period. -/

namespace ACS12.Configuration

open CenteredCircle.AllN
open ACS12.GammaMeasure
open scoped BigOperators

variable {n : ℕ} {p : ℝ} (F : Configuration n p)
    (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi))

theorem chart_radial_images (hp : 0 < p) (i : Fin n) :
    C.source.forwardExterior (imagePotential p C.source.period) i +
      C.source.backwardExterior (imagePotential p C.source.period) i =
    F.chartRadialScale C * (2 * F.coefficient * F.radius ^ 2) +
      C.source.mass i * imageSelf p C.source.period := by
  let S := C.source
  let L := S.period
  let K := imagePotential p L
  have hE : S.forwardExterior K i + S.backwardExterior K i =
      ∑ j, S.mass j *
        (imageTail K L (S.forwardDistance i j) + imageTail K L (S.forwardDistance j i)) := by
    simp only [AnchoredCircleSource.forwardExterior, AnchoredCircleSource.backwardExterior,
      mul_add, Finset.sum_add_distrib, L]
  rw [hE, ← Finset.sum_erase_add _ _ (Finset.mem_univ i), S.forwardDistance_self,
    ← two_mul, ← imageSelf_eq_tail]
  congr 1
  rw [← F.chart_forward_radial_eq C i]
  apply Finset.sum_congr rfl
  intro j hj
  have hij := (Finset.mem_erase.mp hj).1.symm
  rw [S.forwardDistance_flip hij,
    imagePotential_pair hp S.period_pos (S.forwardDistance_pos i j) (S.forwardDistance_lt_period hij)]

theorem chart_torque_images (hp : 0 < p) (i : Fin n) :
    C.source.forwardExterior (imageSlope p C.source.period) i -
      C.source.backwardExterior (imageSlope p C.source.period) i = 0 := by
  let S := C.source
  let L := S.period
  let U := imageSlope p L
  have hE : S.forwardExterior U i - S.backwardExterior U i =
      ∑ j, S.mass j *
        (imageTail U L (S.forwardDistance i j) - imageTail U L (S.forwardDistance j i)) := by
    simp only [AnchoredCircleSource.forwardExterior, AnchoredCircleSource.backwardExterior,
      mul_sub, Finset.sum_sub_distrib, L]
  rw [hE, ← Finset.sum_erase_add _ _ (Finset.mem_univ i), sub_self, mul_zero, add_zero]
  have hRow :
      (∑ j ∈ Finset.univ.erase i, S.mass j *
        (imageTail U L (S.forwardDistance i j) - imageTail U L (S.forwardDistance j i))) =
      p * (Real.pi / L) ^ (p + 1) *
        ∑ j ∈ Finset.univ.erase i, S.mass j * circleTorque p L (S.forwardDistance i j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hij := (Finset.mem_erase.mp hj).1.symm
    rw [S.forwardDistance_flip hij,
      imageSlope_pair hp S.period_pos (S.forwardDistance_pos i j) (S.forwardDistance_lt_period hij)]
    ring
  rw [hRow, F.chart_forward_torque_eq_zero C i, mul_zero]

end ACS12.Configuration

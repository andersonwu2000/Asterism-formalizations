import ACS12.QuarticUniform
import ACS12
import ACS12.NativeCellEnergy
import ACS12.JointFarSign
import ACS12.JointPureUpperDiagonal
import ACS12.JointConeValue
import ACS12.AngularEnergy
import ACS12.ConvexRightSampling
import CenteredCircle.KernelQuadratureData
import CenteredCircle.LaplaceSampling

/-!
Selected manuscript correspondences, including the source-feasible cone and
fixed-geometry comparison. The integrated frequency square uses the
symmetric double sum equivalent to the manuscript's unordered-pair sum.
-/

namespace ACS12.NativeCells
open CenteredCircle.AllN MeasureTheory Set Filter
open GammaMeasure (gammaDensity gammaDensity_pos gammaDensity_cosh_moment)

theorem cellEnergy_integrated_square {n : ℕ} {w : Fin n → ℝ}
    (hw : ∀ i, 0 < w i) (hw₁ : ∀ i, w i < 1)
    (hW : (∑ i, w i) = 1) {p : ℝ} (hp : 0 < p) (v : Fin n → ℝ) :
    (∑ i, v i ^ 2 * analyticRow p (w i)⁻¹) -
      angularEnergy p v (fun i => center (massCells w) i) =
    ∫ s : ℝ in Ioi 0, 2 * gammaDensity p s *
      ((1 / 2 : ℝ) * ∑ i : Fin n, ∑ j : Fin n,
        (v i / Real.sinh (s * halfWidth (massCells w) i) -
          v j / Real.sinh (s * halfWidth (massCells w) j)) ^ 2 *
        (Real.sinh (s * halfWidth (massCells w) i) *
          Real.sinh (s * halfWidth (massCells w) j) * cellEntry s (massCells w) i j)) := by
  let edge := massCells w
  let a (i : Fin n) := center edge i
  let f (i j : Fin n) (s : ℝ) := v i * v j * (2 * gammaDensity p s * cellEntry s edge i j)
  let g (i : Fin n) (s : ℝ) := v i ^ 2 * (2 * gammaDensity p s * rowAtFrequency (w i) s)
  have he := massCells_strictMonoOn hw
  have h0 := massCells_zero w
  have hN := massCells_end hW
  have hF (i j : Fin n) : IntegrableOn (f i j) (Ioi 0) :=
    (cellEntry_integral he h0 hN hp i j).1.const_mul _
  have hG (i : Fin n) : IntegrableOn (g i) (Ioi 0) := by
    have h := (analyticRow_integrable hp ((one_lt_inv₀ (hw i)).mpr (hw₁ i))).const_mul (v i ^ 2)
    simpa only [g, inv_inv] using h
  have hF' (i : Fin n) : IntegrableOn (fun s => ∑ j : Fin n, f i j s) (Ioi 0) :=
    integrable_finsetSum _ (fun j _ => hF i j)
  have hFI : IntegrableOn (fun s => ∑ i : Fin n, ∑ j : Fin n, f i j s) (Ioi 0) :=
    integrable_finsetSum _ (fun i _ => hF' i)
  have hGI : IntegrableOn (fun s => ∑ i : Fin n, g i s) (Ioi 0) :=
    integrable_finsetSum _ (fun i _ => hG i)
  have hFE : (∫ s : ℝ in Ioi 0, ∑ i : Fin n, ∑ j : Fin n, f i j s) = angularEnergy p v a := by
    rw [integral_finsetSum _ (fun i _ => hF' i)]
    unfold angularEnergy
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => hF i j)]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [f]
    rw [integral_const_mul, (cellEntry_integral he h0 hN hp i j).2]
  have hGE : (∫ s : ℝ in Ioi 0, ∑ i : Fin n, g i s) = ∑ i, v i ^ 2 * analyticRow p (w i)⁻¹ := by
    rw [integral_finsetSum _ (fun i _ => hG i)]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [g]
    rw [integral_const_mul, analyticRow, inv_inv]
  rw [← hGE, ← hFE, ← integral_sub hGI hFI]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  have h := cellEnergy_frequency_square he h0 hN v (show 0 < s from hs)
  dsimp only at h
  dsimp only
  rw [← h]
  dsimp only [g, f, rowAtFrequency]
  simp only [massCells_halfWidth]
  simp only [mul_sub, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [edge]
    ring

end ACS12.NativeCells

namespace ACS12.Paper

alias theorem_1_1 := Configuration.rigidity
alias theorem_1_1_converse := regular_polygon_converse
alias lemma_2_1 := angularEnergy_minimum
alias corollary_2_2 := Configuration.equal_mass_regular
alias lemma_3_1 := GammaMeasure.gammaDensity_exp_moment
alias lemma_3_4 := NativeCells.cellEnergy_integrated_square
alias lemma_3_4_nonnegative := NativeCells.cellEnergy_le
alias lemma_4_6_smooth_sampling := CenteredCircle.AllN.convex_cubic_quadratureData
alias lemma_4_6_convex_sampling := CenteredCircle.AllN.convex_right_quadratureData_of_quadratic_decay
alias lemma_4_6_packing := CenteredCircle.AllN.half_source_bound
alias lemma_4_6_equality := CenteredCircle.AllN.half_source_rigid_laplace
alias lemma_7_4_root := GammaMeasure.fourthComparisonRoot_spec
alias lemma_7_4_diagonal := GammaMeasure.fourthComparisonRoot_diagonal_speed
alias lemma_7_4_fixed := GammaMeasure.fourthComparisonRoot_fixed_speed
alias lemma_7_4_continuity := GammaMeasure.fourthComparisonRoot_diagonal_continuousOn
alias lemma_7_9_strip := GammaMeasure.fourthComparisonRoot_high_bracket
alias lemma_7_9_boundary := GammaMeasure.diagonalAdjacent_lowMass_pos
alias lemma_7_10 := Configuration.inner_feasible_necessary
alias lemma_7_11 := GammaMeasure.deficit_joint_cone
alias lemma_7_11_feasible := GammaMeasure.feasible_joint_cone
alias lemma_7_12 := GammaMeasure.outerMass_feasible
alias fixed_geometry_return := GammaMeasure.jointAugmentedValue_actual_lt
alias joint_diagonal_convex := GammaMeasure.jointPureValue_convex_diagonal
alias joint_cone_increment := GammaMeasure.jointPure_wholeCone_increment
alias lemma_E_3 := GammaMeasure.jointPure_upperDiag_bound
alias lemma_H_1 := GammaMeasure.jointFarValue_linear_margin

alias theorem_13_1 := Configuration.quartic_mass_ratio_five
alias lemma_13_2 := Configuration.quartic_massTotal_div_mass_gt_four
alias proposition_14_1 := NativeCells.quartic_separation
alias proposition_14_1_uniform := NativeCells.quarticUniform_root_eq_upper
alias quartic_anchor := NativeCells.quartic_anchor
alias quartic_two_arc_receipt := NativeCells.quartic_rank_receipt
alias quartic_sine_tangent := NativeCells.quarticSineDeficit_lower
alias quartic_affine_return := NativeCells.quartic_scalar_return
alias low_weighted_entropy := Pressure.weightedPressureEntropy_nonneg
alias low_escort_curvature := NativeCells.endpointEscortAtom_pos

end ACS12.Paper

#print axioms ACS12.Paper.theorem_1_1
#print axioms ACS12.Paper.theorem_1_1_converse
#print axioms ACS12.Paper.lemma_2_1
#print axioms ACS12.Paper.corollary_2_2
#print axioms ACS12.Paper.lemma_3_1
#print axioms ACS12.Paper.lemma_3_4
#print axioms ACS12.Paper.lemma_4_6_smooth_sampling
#print axioms ACS12.Paper.lemma_4_6_convex_sampling
#print axioms ACS12.Paper.lemma_4_6_packing
#print axioms ACS12.Paper.lemma_4_6_equality
#print axioms ACS12.Paper.lemma_7_4_diagonal
#print axioms ACS12.Paper.lemma_7_4_fixed
#print axioms ACS12.Paper.lemma_7_9_strip
#print axioms ACS12.Paper.lemma_7_9_boundary
#print axioms ACS12.Paper.lemma_7_10
#print axioms ACS12.Paper.lemma_7_11
#print axioms ACS12.Paper.lemma_7_11_feasible
#print axioms ACS12.Paper.lemma_7_12
#print axioms ACS12.Paper.fixed_geometry_return
#print axioms ACS12.Paper.joint_diagonal_convex
#print axioms ACS12.Paper.joint_cone_increment
#print axioms ACS12.Paper.lemma_E_3
#print axioms ACS12.Paper.lemma_H_1



#print axioms ACS12.Paper.theorem_13_1
#print axioms ACS12.Paper.lemma_13_2
#print axioms ACS12.Paper.proposition_14_1
#print axioms ACS12.Paper.quartic_anchor
#print axioms ACS12.Paper.quartic_two_arc_receipt
#print axioms ACS12.Paper.quartic_sine_tangent
#print axioms ACS12.Paper.quartic_affine_return
#print axioms ACS12.Paper.low_weighted_entropy
#print axioms ACS12.Paper.low_escort_curvature

#print axioms ACS12.Paper.proposition_14_1_uniform

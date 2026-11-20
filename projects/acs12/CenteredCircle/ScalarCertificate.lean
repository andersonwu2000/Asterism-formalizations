import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

/-!
Initial, deliberately limited verification for Dot's all-finite-n manuscript.
The exact eight-term certificate is unconditional. The scalar endpoint theorem
below is a conditional consumer: its convexity, tail and comparison hypotheses
still have to be proved for the analytic kernels in the manuscript.
No circle-rigidity or physical central-configuration theorem is asserted here.
-/

namespace CenteredCircle.AllN

open scoped BigOperators

noncomputable def comparisonF (t : ℝ) : ℝ :=
  (3 * t - 1) / (4 * t ^ 2 * (t + 1) ^ 2)

noncomputable def comparisonG (t : ℝ) : ℝ :=
  (3 * t + 4) / (4 * t ^ 2 * (t + 1) ^ 2)

noncomputable def eightTermCertificate : ℝ :=
  (∑ k ∈ Finset.range 8,
    (comparisonF ((k : ℝ) + 1) +
      (7 / 10 : ℝ) * comparisonG (((k : ℝ) + 1) * (7 / 10)))) +
    (1 + (7 / 10 : ℝ)⁻¹ ^ 2) / 128 - 9 / 4 + 3 / 2 * (7 / 10)

set_option maxHeartbeats 2000000 in
theorem eightTermCertificate_exact :
    eightTermCertificate =
      -(1794985965991645696553 : ℝ) / 84600393758389463834880 := by
  norm_num [eightTermCertificate, comparisonF, comparisonG, Finset.sum_range_succ]

theorem certificate_margin_exact :
    eightTermCertificate + (1 - (7 / 10 : ℝ)) / 18 =
      -(76995880670364259861 : ℝ) / 16920078751677892766976 := by
  rw [eightTermCertificate_exact]
  norm_num

theorem certificate_margin_neg :
    eightTermCertificate + (1 - (7 / 10 : ℝ)) / 18 < 0 := by
  rw [certificate_margin_exact]
  norm_num

/-- This checks the convex-chord implication, not its analytic premises. -/
theorem scalar_endpoint_of_comparison
    (F : ℝ → ℝ) (b actualResidual : ℝ)
    (hconv : ConvexOn ℝ (Set.Icc (7 / 10 : ℝ) 1) F)
    (hone : F 1 = 0)
    (hcertificate : F (7 / 10) ≤ eightTermCertificate)
    (hb : (7 / 10 : ℝ) ≤ b) (hb1 : b ≤ 1)
    (hactual : 0 ≤ actualResidual)
    (hcomparison : actualResidual ≤ F b + (1 - b) / 18) :
    b = 1 := by
  by_contra hne
  have hlt : b < 1 := lt_of_le_of_ne hb1 hne
  let η : ℝ := (1 - b) * (10 / 3)
  have hηpos : 0 < η := by dsimp [η]; nlinarith
  have hηle : η ≤ 1 := by dsimp [η]; nlinarith
  have hcomb : η * (7 / 10 : ℝ) + (1 - η) * 1 = b := by
    dsimp [η]
    ring
  have hc := hconv.2
    (show (7 / 10 : ℝ) ∈ Set.Icc (7 / 10 : ℝ) 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Set.Icc (7 / 10 : ℝ) 1 by constructor <;> norm_num)
    (le_of_lt hηpos) (sub_nonneg.mpr hηle)
    (show η + (1 - η) = 1 by ring)
  simp only [smul_eq_mul, hcomb, hone, mul_zero, add_zero] at hc
  have hleft : F (7 / 10) < -(1 - (7 / 10 : ℝ)) / 18 := by
    have hm := certificate_margin_neg
    linarith
  have hm := mul_lt_mul_of_pos_left hleft hηpos
  have hscale : η * (-(1 - (7 / 10 : ℝ)) / 18) = -(1 - b) / 18 := by
    dsimp [η]
    ring
  rw [hscale] at hm
  linarith

end CenteredCircle.AllN

#print axioms CenteredCircle.AllN.eightTermCertificate_exact
#print axioms CenteredCircle.AllN.certificate_margin_exact
#print axioms CenteredCircle.AllN.certificate_margin_neg
#print axioms CenteredCircle.AllN.scalar_endpoint_of_comparison

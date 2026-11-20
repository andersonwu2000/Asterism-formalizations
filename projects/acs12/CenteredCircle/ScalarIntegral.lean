import CenteredCircle.MixedSampling

/-! Exact scalar lattice sums, their integral representations, and strict comparison. -/

namespace CenteredCircle.AllN

open MeasureTheory Set Filter

noncomputable def circleScalar (L b : ℝ) : ℝ :=
  samplingTail (mixedLeftKernel L) 0 1 + samplingTail (mixedRightKernel L) 0 b -
    (1 - b / 4) * torqueKernel L 1 - (5 / 4) * (1 - b) * radialCorrection L

noncomputable def lineScalar (b : ℝ) : ℝ :=
  samplingTail lineLeftKernel 0 1 + samplingTail lineRightKernel 0 b -
    (1 - b / 4) - (5 / 4) * (1 - b)

theorem circleScalar_integral {L b : ℝ} (hL : 0 < L) (hb : 0 < b) :
    IntegrableOn (fun u : ℝ => circleResidualDensity L u b) (Ioi 0) ∧
      circleScalar L b = ∫ u : ℝ in Ioi 0, circleResidualDensity L u b := by
  have hf := mixedLeftKernel_sampling hL (by norm_num : (0 : ℝ) < 1)
  have hg := mixedRightKernel_sampling hL hb
  have hu : IntegrableOn (fun u : ℝ => (u * circleWeight L u) * Real.exp (-u)) (Ioi 0) := by
    simpa only [mul_one] using torqueKernel_integrable hL 1 (by norm_num)
  have hr : IntegrableOn (fun u : ℝ => circleWeight L u * Real.exp (-u)) (Ioi 0) := by
    simpa only [mul_one] using radialKernel_integrable hL 1 (by norm_num)
  have hi := imageDensity_integrable hL
  have hd : IntegrableOn (fun u : ℝ => circleWeight L u * Real.exp (-u) + 2 * imageDensity L u)
      (Ioi 0) := hr.add (hi.const_mul 2)
  have huval : (∫ u : ℝ in Ioi 0, (u * circleWeight L u) * Real.exp (-u)) = torqueKernel L 1 := by
    simp only [torqueKernel, mul_one]
  have hdval : (∫ u : ℝ in Ioi 0, circleWeight L u * Real.exp (-u) + 2 * imageDensity L u) =
      radialCorrection L := by
    rw [integral_add hr (hi.const_mul 2), integral_const_mul,
      ← selfImageTerm_integral hL]
    simp only [radialCorrection, radialKernel, mul_one]
  have he : (fun u : ℝ => circleResidualDensity L u b) = fun u =>
      circleWeight L u * leftMixPolynomial u * scaledExpTail u 1 +
      circleWeight L u * rightMixPolynomial u * scaledExpTail u b -
      (1 - b / 4) * ((u * circleWeight L u) * Real.exp (-u)) -
      ((5 / 4) * (1 - b)) * (circleWeight L u * Real.exp (-u) + 2 * imageDensity L u) := by
    funext u
    dsimp [circleResidualDensity, lineResidualDensity]
    ring
  rw [he]
  constructor
  · exact ((hf.1.add hg.1).sub (hu.const_mul (1 - b / 4))).sub
      (hd.const_mul ((5 / 4) * (1 - b)))
  · have hv := integral_four_terms hf.1 hg.1 hu hd 1 1 (1 - b / 4) ((5 / 4) * (1 - b))
    simp only [one_mul] at hv
    rw [huval, hdval, ← hf.2, ← hg.2] at hv
    exact hv.symm

theorem lineScalar_integral {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun u : ℝ => lineResidualDensity u b) (Ioi 0) ∧
      lineScalar b = ∫ u : ℝ in Ioi 0, lineResidualDensity u b := by
  have hf := lineLeftKernel_sampling (by norm_num : (0 : ℝ) < 1)
  have hg := lineRightKernel_sampling hb
  have hu : IntegrableOn (fun u : ℝ => u * Real.exp (-u)) (Ioi 0) := by
    simpa only [pow_one, mul_one] using integrable_power_exponential 1 1 (by norm_num)
  have hr : IntegrableOn (fun u : ℝ => Real.exp (-u)) (Ioi 0) := by
    simpa using integrable_power_exponential 0 1 (by norm_num)
  have huval : (∫ u : ℝ in Ioi 0, u * Real.exp (-u)) = 1 := by
    simpa using integral_power_exponential 1 1 (by norm_num)
  have hrval : (∫ u : ℝ in Ioi 0, Real.exp (-u)) = 1 := by
    simpa using integral_power_exponential 0 1 (by norm_num)
  have he : (fun u : ℝ => lineResidualDensity u b) = fun u =>
      leftMixPolynomial u * scaledExpTail u 1 + rightMixPolynomial u * scaledExpTail u b -
      (1 - b / 4) * (u * Real.exp (-u)) - ((5 / 4) * (1 - b)) * Real.exp (-u) := by
    funext u
    dsimp [lineResidualDensity]
    ring
  rw [he]
  constructor
  · exact ((hf.1.add hg.1).sub (hu.const_mul (1 - b / 4))).sub
      (hr.const_mul ((5 / 4) * (1 - b)))
  · have hv := integral_four_terms hf.1 hg.1 hu hr 1 1 (1 - b / 4) ((5 / 4) * (1 - b))
    simp only [one_mul] at hv
    rw [huval, hrval, ← hf.2, ← hg.2] at hv
    simpa only [mul_one, lineScalar] using hv.symm

theorem circleScalar_lt_lineScalar {L b : ℝ} (hL : 0 < L) (hb : 0 < b) (hb1 : b < 1) :
    circleScalar L b < lineScalar b := by
  letI : NeZero (volume.restrict (Ioi (0 : ℝ))) := ⟨positiveHalfLine_ne_zero⟩
  rw [(circleScalar_integral hL hb).2, (lineScalar_integral hb).2]
  apply integral_strict_of_ae_lt _ (circleScalar_integral hL hb).1 (lineScalar_integral hb).1
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact circleResidualDensity_lt_line L hu hb hb1

theorem lineResidualDensity_one {u : ℝ} (hu : 0 < u) : lineResidualDensity u 1 = 0 := by
  have he := polynomial_total_sample hu
  dsimp [lineResidualDensity]
  nlinarith

theorem lineScalar_one : lineScalar 1 = 0 := by
  rw [(lineScalar_integral (by norm_num : (0 : ℝ) < 1)).2]
  calc
    (∫ u : ℝ in Ioi 0, lineResidualDensity u 1) = ∫ _u : ℝ in Ioi 0, (0 : ℝ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact lineResidualDensity_one hu
    _ = 0 := integral_zero _ _

theorem circleScalar_one {L : ℝ} (hL : 0 < L) : circleScalar L 1 = 0 := by
  rw [(circleScalar_integral hL (by norm_num : (0 : ℝ) < 1)).2]
  calc
    (∫ u : ℝ in Ioi 0, circleResidualDensity L u 1) = ∫ _u : ℝ in Ioi 0, (0 : ℝ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [circleResidualDensity, lineResidualDensity_one hu]
      ring
    _ = 0 := integral_zero _ _

end CenteredCircle.AllN

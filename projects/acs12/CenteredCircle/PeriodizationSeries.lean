import CenteredCircle.KernelSeries

/-! Periodic image sums reduced to absolutely convergent scalar integrals. -/

namespace CenteredCircle.AllN

open MeasureTheory Filter Set
open scoped BigOperators

theorem circleWeight_exp_ratio (L u : ℝ) :
    circleWeight L u = (1 - Real.exp (-u * L)) / (1 + Real.exp (-u * L)) := by
  let x := L * u / 2
  have he : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  have hr : Real.exp (-u * L) = (Real.exp (-x)) ^ 2 := by
    rw [sq, ← Real.exp_add]
    congr 1
    dsimp [x]
    ring
  rw [circleWeight, Real.tanh_eq]
  change (Real.exp x - Real.exp (-x)) / (Real.exp x + Real.exp (-x)) = _
  apply (div_eq_div_iff (ne_of_gt (add_pos (Real.exp_pos x) (Real.exp_pos (-x))))
    (ne_of_gt (by positivity : 0 < 1 + Real.exp (-u * L)))).mpr
  rw [hr]
  have he2 := congrArg (fun y : ℝ => y * Real.exp (-x)) he
  dsimp at he2
  nlinarith

theorem radial_sample_tsum_integral {L : ℝ} (hL : 0 < L)
    (t : ℝ) (ht : 0 < t) :
    (∑' j : ℕ, radialKernel L (t + j * L)) =
      ∫ u : ℝ in Ioi 0, Real.exp (-u * t) / (1 + Real.exp (-u * L)) := by
  have hInt : ∀ j : ℕ, IntegrableOn
      (fun u => circleWeight L u * Real.exp (-u * (t + j * L))) (Ioi 0) := by
    intro j
    apply radialKernel_integrable hL
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    positivity
  have hnorm (j : ℕ) : (∫ u : ℝ in Ioi 0,
      ‖circleWeight L u * Real.exp (-u * (t + j * L))‖) =
      radialKernel L (t + j * L) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact Real.norm_of_nonneg (mul_pos (circleWeight_pos hL hu) (Real.exp_pos _)).le
  have hNorm : Summable (fun j : ℕ => ∫ u : ℝ in Ioi 0,
      ‖circleWeight L u * Real.exp (-u * (t + j * L))‖) := by
    simp_rw [hnorm]
    exact summable_radialKernel hL t L ht hL
  have hswap := integral_tsum_of_summable_integral_norm hInt hNorm
  calc
    (∑' j : ℕ, radialKernel L (t + j * L)) =
        ∫ u : ℝ in Ioi 0,
          ∑' j : ℕ, circleWeight L u * Real.exp (-u * (t + j * L)) := hswap
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      change 0 < u at hu
      dsimp only
      rw [tsum_mul_left, (exponential_samples_hasSum u t L hu hL).tsum_eq,
        circleWeight_exp_ratio]
      have hden : 1 - Real.exp (-u * L) ≠ 0 :=
        ne_of_gt (by simpa only [neg_mul] using expHead_den_pos (mul_pos hu hL))
      field_simp
      exact div_self (by simpa only [neg_mul] using hden)

theorem integrable_radial_sample_integrand {L : ℝ} (hL : 0 < L)
    (t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun u : ℝ => Real.exp (-u * t) / (1 + Real.exp (-u * L)))
      (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [← radial_sample_tsum_integral hL t ht]
  have hsum := summable_radialKernel hL t L ht hL
  have hlead := hsum.le_tsum 0 (fun j _ => (radialKernel_pos hL _ (by positivity)).le)
  simp only [Nat.cast_zero, zero_mul, add_zero] at hlead
  exact ne_of_gt ((radialKernel_pos hL t ht).trans_le hlead)

theorem radial_periodization_integral {L t : ℝ} (hL : 0 < L)
    (ht : 0 < t) (htL : t < L) :
    (∑' j : ℤ, radialKernel L |t + j * L|) =
      ∫ u : ℝ in Ioi 0,
        (Real.exp (-u * t) + Real.exp (-u * (L - t))) /
          (1 + Real.exp (-u * L)) := by
  have hLt : 0 < L - t := sub_pos.mpr htL
  have hp (j : ℕ) : |t + (j : ℤ) * L| = t + (j : ℝ) * L := by
    rw [Int.cast_natCast]
    apply abs_of_pos
    positivity
  have hn (j : ℕ) : |t + (-(j + 1) : ℤ) * L| = (L - t) + (j : ℝ) * L := by
    push_cast
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    rw [abs_of_neg (by nlinarith)]
    ring
  have hs1 : Summable (fun j : ℕ => radialKernel L |t + (j : ℤ) * L|) := by
    simp_rw [hp]
    exact summable_radialKernel hL t L ht hL
  have hs2 : Summable (fun j : ℕ => radialKernel L |t + (-(j + 1) : ℤ) * L|) := by
    simp_rw [hn]
    exact summable_radialKernel hL (L - t) L hLt hL
  rw [tsum_of_nat_of_neg_add_one
    (f := fun j : ℤ => radialKernel L |t + (j : ℝ) * L|) hs1 hs2]
  simp_rw [hp, hn]
  rw [radial_sample_tsum_integral hL t ht, radial_sample_tsum_integral hL (L - t) hLt,
    ← integral_add (integrable_radial_sample_integrand hL t ht)
      (integrable_radial_sample_integrand hL (L - t) hLt)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  exact (add_div _ _ _).symm

end CenteredCircle.AllN

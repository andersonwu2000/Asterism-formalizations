import ACS12.SpeedCut
import ACS12.LeftMoments

/-! Exact one-cut signs and complete moments in P945 G1–G3. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set

theorem expHeadFactor_eq_add_expTail {x : ℝ} (hx : 0 < x) :
    expHeadFactor x = x + expTailFactor x := by
  rw [BoseShape.expTail_eq_decay hx, expHeadFactor]
  field_simp [(expHead_den_pos hx).ne']
  ring

noncomputable def diagonalSpeedKernel (x : ℝ) : ℝ :=
  Real.exp (-x) * (-1 - 2 * x + x * expHeadFactor x) - 2 * polyA x * BoseShape.C x

noncomputable def fixedMassSpeedKernel (θ x : ℝ) : ℝ :=
  diagonalSpeedKernel x + Real.exp (-x) * ((1 - θ) * x - 1)

private theorem diagonalSpeedKernel_cleared {x : ℝ} (hx : 0 < x) :
    diagonalSpeedKernel x * (Real.exp x - 1) ^ 2 = diagonalSpeedNumerator x := by
  simp only [diagonalSpeedKernel, expHeadFactor_eq_add_expTail hx, expTailFactor,
    polyA, BoseShape.C, diagonalSpeedNumerator, BoseShape.expQuad, zero_mul, zero_add,
    one_mul, neg_one_mul, Real.exp_neg]
  field_simp [(expTail_den_pos hx).ne', Real.exp_ne_zero x]
  ring

private theorem fixedMassSpeedKernel_cleared (θ : ℝ) {x : ℝ} (hx : 0 < x) :
    fixedMassSpeedKernel θ x * (Real.exp x - 1) ^ 2 = x * fixedMassSpeedNumerator θ x := by
  rw [fixedMassSpeedKernel, add_mul, diagonalSpeedKernel_cleared hx]
  simp only [diagonalSpeedNumerator, fixedMassSpeedNumerator, BoseShape.expQuad, zero_mul,
    zero_add, one_mul, neg_one_mul, Real.exp_neg]
  field_simp [Real.exp_ne_zero x]
  ring

theorem diagonalSpeedKernel_cut : NegativePositiveCut diagonalSpeedKernel := by
  obtain ⟨c, hc, hBefore, hAt, hAfter⟩ := diagonalSpeedNumerator_cut
  refine ⟨c, hc, ?_, ?_, ?_⟩
  · intro x hx
    have h := (diagonalSpeedKernel_cleared hx.1).symm ▸ hBefore x hx
    exact neg_of_mul_neg_left h (sq_nonneg _)
  · exact (mul_eq_zero.mp ((diagonalSpeedKernel_cleared hc).trans hAt)).resolve_right
      (pow_ne_zero _ (expTail_den_pos hc).ne')
  · intro x hx
    have h := (diagonalSpeedKernel_cleared (hc.trans hx)).symm ▸ hAfter x hx
    exact pos_of_mul_pos_left h (sq_nonneg _)

theorem fixedMassSpeedKernel_cut {θ : ℝ} (hθ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    NegativePositiveCut (fixedMassSpeedKernel θ) := by
  obtain ⟨c, hc, hBefore, hAt, hAfter⟩ := fixedMassSpeedNumerator_cut hθ hθ₁
  refine ⟨c, hc, ?_, ?_, ?_⟩
  · intro x hx
    apply neg_of_mul_neg_left _ (sq_nonneg (Real.exp x - 1))
    rw [fixedMassSpeedKernel_cleared θ hx.1]
    exact mul_neg_of_pos_of_neg hx.1 (hBefore x hx)
  · have h := fixedMassSpeedKernel_cleared θ hc
    rw [hAt, mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero _ (expTail_den_pos hc).ne')
  · intro x hx
    have hx₀ := hc.trans hx
    apply pos_of_mul_pos_left _ (sq_nonneg (Real.exp x - 1))
    rw [fixedMassSpeedKernel_cleared θ hx₀]
    exact mul_pos hx₀ (hAfter x hx)

private theorem diagonalSpeedKernel_pointwise {x : ℝ} (hx : x ∈ Ioi (0 : ℝ)) :
    x * diagonalSpeedKernel x =
      x ^ 3 * Real.exp (-x * 1) +
        x ^ 3 * (Real.exp (-x * (2 : ℕ)) / (1 - Real.exp (-x))) -
      x ^ 1 * Real.exp (-x * 1) - 2 * (x ^ 2 * Real.exp (-x * 1)) -
      2 * (x * leftMultiplier 0 1 x * BoseShape.C x) := by
  rw [diagonalSpeedKernel, expHeadFactor_eq_add_expTail hx, BoseShape.expTail_eq_decay hx]
  simp only [Nat.cast_ofNat, mul_one, pow_one, polyA, leftMultiplier, zero_mul, sub_zero,
    show -x * (2 : ℝ) = -x + -x by ring, Real.exp_add]
  field_simp [(expHead_den_pos hx).ne']
  ring

theorem diagonalSpeedKernel_moment :
    (∫ x : ℝ in Ioi 0, x * diagonalSpeedKernel x) = 1 + 4 * powerTail 3 1 - 6 * powerTail 4 1 := by
  let f (x : ℝ) := x ^ (3 : ℕ) * Real.exp (-x * 1)
  let g (x : ℝ) := x ^ (3 : ℕ) * (Real.exp (-x * (2 : ℕ)) / (1 - Real.exp (-x)))
  let h (x : ℝ) := x ^ (1 : ℕ) * Real.exp (-x * 1)
  let k (x : ℝ) := x ^ (2 : ℕ) * Real.exp (-x * 1)
  let l (x : ℝ) := x * leftMultiplier 0 1 x * BoseShape.C x
  let μ := volume.restrict (Ioi (0 : ℝ))
  have hf : Integrable f μ := expMoment_nat_integrable 3 zero_lt_one
  have hg : Integrable g μ := boseMoment_nat_integrable (by decide : 0 < 3) (by decide : 0 < 2)
  have hh : Integrable h μ := expMoment_nat_integrable 1 zero_lt_one
  have hk : Integrable k μ := expMoment_nat_integrable 2 zero_lt_one
  have hl : Integrable l μ := reference_second_integrable 0 1
  have hCalc (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
      x * diagonalSpeedKernel x = (1 * f x + 1 * g x - 1 * h x - 2 * k x) - 2 * l x := by
    simpa only [f, g, h, k, l, one_mul] using diagonalSpeedKernel_pointwise hx
  rw [setIntegral_congr_fun measurableSet_Ioi hCalc]
  have hI : Integrable (fun x => 1 * f x + 1 * g x - 1 * h x - 2 * k x) μ :=
    ((((hf.const_mul 1).add (hg.const_mul 1)).sub (hh.const_mul 1)).sub (hk.const_mul 2))
  rw [integral_sub hI (hl.const_mul 2), integral_four_terms hf hg hh hk, integral_const_mul]
  dsimp only [f, g, h, k, l, μ]
  rw [expMoment_nat_integral 3 zero_lt_one, expMoment_nat_integral 1 zero_lt_one,
    expMoment_nat_integral 2 zero_lt_one, boseMoment_nat_integral (by decide : 0 < 3) (by decide : 0 < 2),
    reference_second_eq]
  have h4 := powerTail_shift (q := 4) (by norm_num) 1
  norm_num [Nat.factorial] at h4 ⊢
  rw [h4]
  ring

theorem diagonalSpeedKernel_moment_neg :
    (∫ x : ℝ in Ioi 0, x * diagonalSpeedKernel x) < 0 := by
  rw [diagonalSpeedKernel_moment]
  linarith only [powerTail_three_lt, powerTail_four_gt]

theorem fixedMassSpeedKernel_moment (θ : ℝ) :
    (∫ x : ℝ in Ioi 0, x * fixedMassSpeedKernel θ x) =
      2 + 4 * powerTail 3 1 - 6 * powerTail 4 1 - 2 * θ := by
  let g (x : ℝ) := x * diagonalSpeedKernel x
  let h (x : ℝ) := (1 - θ) * (x ^ (2 : ℕ) * Real.exp (-x * 1)) - x ^ (1 : ℕ) * Real.exp (-x * 1)
  have hG : IntegrableOn g (Ioi 0) := Integrable.of_integral_ne_zero diagonalSpeedKernel_moment_neg.ne
  have hA := (expMoment_nat_integrable 2 zero_lt_one).const_mul (1 - θ)
  have hB := expMoment_nat_integrable 1 zero_lt_one
  have hH : IntegrableOn h (Ioi 0) := hA.sub hB
  have hPoint (x : ℝ) : x * fixedMassSpeedKernel θ x = g x + h x := by
    simp only [g, h, fixedMassSpeedKernel, pow_one, mul_one]
    ring
  simp_rw [hPoint]
  rw [integral_add hG hH]
  dsimp only [g, h]
  rw [diagonalSpeedKernel_moment, integral_sub hA hB, integral_const_mul,
    expMoment_nat_integral 2 zero_lt_one, expMoment_nat_integral 1 zero_lt_one]
  norm_num [Nat.factorial]
  ring

theorem fixedMassSpeedKernel_moment_neg {θ : ℝ} (hθ : 1 / 3 ≤ θ) :
    (∫ x : ℝ in Ioi 0, x * fixedMassSpeedKernel θ x) < 0 := by
  rw [fixedMassSpeedKernel_moment]
  linarith only [powerTail_three_lt, powerTail_four_gt, hθ]

end ACS12.GammaMeasure


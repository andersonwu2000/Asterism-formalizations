import CenteredCircle.KernelCalculus

/-! The two decreasing density ratios used in the actual A/B comparison. -/

namespace CenteredCircle.AllN

open Set

theorem exp_pair_gt_quadratic {u : ℝ} (hu : 0 < u) :
    u ^ 2 + 2 < Real.exp u + Real.exp (-u) := by
  have hh : 0 < u / 2 := by positivity
  have hs := Real.self_lt_sinh_iff.mpr hh
  have hsp := Real.sinh_pos_iff.mpr hh
  have hc := Real.cosh_two_mul (u / 2)
  rw [show 2 * (u / 2) = u by ring, Real.cosh_sq, Real.cosh_eq] at hc
  have hp := mul_pos (sub_pos.mpr hs) (add_pos hsp hh)
  nlinarith

noncomputable def densityRatio (u : ℝ) : ℝ := polyA u / polyB u

theorem hasDerivAt_densityRatio {u : ℝ} (hu : 0 < u) :
    HasDerivAt densityRatio
      (((u * Real.exp (-u)) * polyB u - polyA u * (1 - Real.exp (-u))) / (polyB u) ^ 2) u :=
  (hasDerivAt_polyA u).div (hasDerivAt_polyB u) (ne_of_gt (polyB_pos hu))

theorem densityRatio_derivative_negative {u : ℝ} (hu : 0 < u) :
    ((u * Real.exp (-u)) * polyB u - polyA u * (1 - Real.exp (-u))) / (polyB u) ^ 2 < 0 := by
  apply div_neg_of_neg_of_pos _ (sq_pos_of_pos (polyB_pos hu))
  have he : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have hb := exp_pair_gt_quadratic hu
  have hneg : u ^ 2 + 2 - Real.exp u - Real.exp (-u) < 0 := by linarith
  have hp := mul_neg_of_neg_of_pos hneg (Real.exp_pos (-u))
  dsimp [polyA, polyB]
  nlinarith

theorem strictAntiOn_densityRatio : StrictAntiOn densityRatio (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro u hu
    exact (hasDerivAt_densityRatio hu).continuousAt.continuousWithinAt
  · intro u hu
    have hu' : 0 < u := by simpa using hu
    rw [(hasDerivAt_densityRatio hu').deriv]
    exact densityRatio_derivative_negative hu'

theorem density_polynomial_cross_nonneg {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (huv : u ≤ v) :
    0 ≤ polyA u * polyB v - polyA v * polyB u := by
  have h := strictAntiOn_densityRatio.antitoneOn hu hv huv
  change polyA v / polyB v ≤ polyA u / polyB u at h
  have hc := (div_le_div_iff₀ (polyB_pos hv) (polyB_pos hu)).mp h
  linarith

noncomputable def weightRatio (L u : ℝ) : ℝ := circleWeight L u / u

theorem hasDerivAt_weightRatio {L u : ℝ} (hL : 0 < L) (hu : 0 < u) :
    HasDerivAt (weightRatio L)
      (((L / 2) * Real.cosh ((L / 2) * u) * (u * Real.cosh ((L / 2) * u)) -
        Real.sinh ((L / 2) * u) *
          (Real.cosh ((L / 2) * u) + u * ((L / 2) * Real.sinh ((L / 2) * u)))) /
        (u * Real.cosh ((L / 2) * u)) ^ 2) u := by
  have hsh := (Real.hasDerivAt_sinh ((L / 2) * u)).comp u
    ((hasDerivAt_id u).const_mul (L / 2))
  have hch := (Real.hasDerivAt_cosh ((L / 2) * u)).comp u
    ((hasDerivAt_id u).const_mul (L / 2))
  have hd := hsh.div ((hasDerivAt_id u).mul hch)
    (ne_of_gt (mul_pos hu (Real.cosh_pos _)))
  convert hd using 1
  · funext x
    dsimp [weightRatio, circleWeight]
    rw [Real.tanh_eq_sinh_div_cosh,
      show L * x / 2 = (L / 2) * x by ring]
    ring
  · dsimp
    ring

theorem weightRatio_derivative_negative {L u : ℝ} (hL : 0 < L) (hu : 0 < u) :
    ((L / 2) * Real.cosh ((L / 2) * u) * (u * Real.cosh ((L / 2) * u)) -
        Real.sinh ((L / 2) * u) *
          (Real.cosh ((L / 2) * u) + u * ((L / 2) * Real.sinh ((L / 2) * u)))) /
        (u * Real.cosh ((L / 2) * u)) ^ 2 < 0 := by
  apply div_neg_of_neg_of_pos _ (sq_pos_of_pos (mul_pos hu (Real.cosh_pos _)))
  have hz : 0 < (L / 2) * u := by positivity
  have hbig := Real.self_lt_sinh_iff.mpr (mul_pos (by norm_num : (0 : ℝ) < 2) hz)
  rw [Real.sinh_two_mul] at hbig
  have hc := congrArg (fun x : ℝ => ((L / 2) * u) * x)
    (Real.cosh_sq_sub_sinh_sq ((L / 2) * u))
  dsimp at hc
  nlinarith

theorem strictAntiOn_weightRatio {L : ℝ} (hL : 0 < L) :
    StrictAntiOn (weightRatio L) (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro u hu
    exact (hasDerivAt_weightRatio hL hu).continuousAt.continuousWithinAt
  · intro u hu
    have hu' : 0 < u := by simpa using hu
    rw [(hasDerivAt_weightRatio hL hu').deriv]
    exact weightRatio_derivative_negative hL hu'

theorem circle_weight_cross_nonneg {L u v : ℝ} (hL : 0 < L)
    (hu : 0 < u) (hv : 0 < v) (huv : u ≤ v) :
    0 ≤ circleWeight L u * v - circleWeight L v * u := by
  have h := (strictAntiOn_weightRatio hL).antitoneOn hu hv huv
  change circleWeight L v / v ≤ circleWeight L u / u at h
  have hc := (div_le_div_iff₀ hv hu).mp h
  linarith

end CenteredCircle.AllN

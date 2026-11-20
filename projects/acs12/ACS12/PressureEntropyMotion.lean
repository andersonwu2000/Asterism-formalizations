import ACS12.PressureCurvature

/-! Exponent and mass-floor motions of the original pressure pair entropy. -/
namespace ACS12.Pressure

open Set

theorem entropyExp_nonneg (x : ℝ) : 0 ≤ entropyExp x := by
  unfold entropyExp
  linarith only [Real.add_one_le_exp x]

private theorem entropyExp_deriv (x : ℝ) : HasDerivAt entropyExp (Real.exp x - 1) x := by
  simpa only [zero_sub,sub_zero] using ((Real.hasDerivAt_exp x).sub_const 1).sub (hasDerivAt_id x)

theorem entropyExp_scale_mono (x : ℝ) : MonotoneOn (fun k => entropyExp (k * x)) (Ici 0) := by
  have hD (k : ℝ) : HasDerivAt (fun z => entropyExp (z * x)) ((Real.exp (k * x) - 1) * x) k := by
    simpa only [Function.comp_apply,id_eq,one_mul] using
      (entropyExp_deriv (k * x)).comp k ((hasDerivAt_id k).mul_const x)
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    (fun k _ => (hD k).continuousAt.continuousWithinAt)
    (fun k _ => (hD k).differentiableAt.differentiableWithinAt)
  intro k hk
  have hk' : 0 ≤ k := interior_subset hk
  rw [(hD k).deriv]
  rcases le_total 0 x with h | h
  · exact mul_nonneg (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg hk' h))) h
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonneg_of_nonpos hk' h))) h

noncomputable def pressureBeta (p : ℝ) : ℝ := p / (p + 1)
noncomputable def pressureB (p : ℝ) : ℝ := (p - 1) / p
noncomputable def pressureC (p : ℝ) : ℝ := (p - 1) / (p + 1)
noncomputable def pressureTau (p σ : ℝ) : ℝ := Real.exp (-σ / (p * (p + 1)))

end ACS12.Pressure

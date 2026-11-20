import ACS12.HighCurrentKernel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! The original shorter-half-circle arc variable and its complete current Jacobian. -/
namespace ACS12.HighCurrent

set_option backward.isDefEq.respectTransparency false

open Set

noncomputable def circleCurrentZeta (D s : ℝ) : ℝ :=
  Real.cos (s / D) / (D * Real.sin (s / D))

theorem circleCurrentZeta_deriv {D s : ℝ} (hD : 0 < D)
    (hs : 0 < s) (hsπ : s ≤ Real.pi * D / 2) :
    HasDerivAt (circleCurrentZeta D) (-(1 / D ^ 2 + circleCurrentZeta D s ^ 2)) s := by
  have hA : 0 < s / D := div_pos hs hD
  have hB : s / D ≤ Real.pi / 2 := (div_le_iff₀ hD).mpr (by linarith only [hsπ])
  have hSin := Real.sin_pos_of_pos_of_lt_pi hA (lt_of_le_of_lt hB (by linarith only [Real.pi_pos]))
  have hArg : HasDerivAt (fun u : ℝ => u / D) (1 / D) s :=
    (hasDerivAt_id s).div_const D
  have hCosD := (Real.hasDerivAt_cos (s / D)).comp s hArg
  have hSinD := ((Real.hasDerivAt_sin (s / D)).comp s hArg).const_mul D
  simp only [Function.comp_apply] at hCosD hSinD
  have hDeriv := hCosD.div hSinD (mul_pos hD hSin).ne'
  unfold circleCurrentZeta
  convert hDeriv using 1
  simp only [Function.comp_apply]
  field_simp [hD.ne',hSin.ne']
  nlinarith only [Real.sin_sq_add_cos_sq (s / D)]

theorem circleCurrentZeta_nonneg {D s : ℝ} (hD : 0 < D)
    (hs : 0 < s) (hsπ : s ≤ Real.pi * D / 2) : 0 ≤ circleCurrentZeta D s := by
  have hA : 0 < s / D := div_pos hs hD
  have hB : s / D ≤ Real.pi / 2 := (div_le_iff₀ hD).mpr (by linarith only [hsπ])
  have hSin := Real.sin_pos_of_pos_of_lt_pi hA (lt_of_le_of_lt hB (by linarith only [Real.pi_pos]))
  have hCos := Real.cos_nonneg_of_mem_Icc ⟨by linarith only [hA,Real.pi_pos],hB⟩
  exact div_nonneg hCos (mul_pos hD hSin).le

theorem circleCurrentZeta_end {D : ℝ} (hD : 0 < D) :
    circleCurrentZeta D (Real.pi * D / 2) = 0 := by
  have hArg : (Real.pi * D / 2) / D = Real.pi / 2 := by field_simp
  simp only [circleCurrentZeta,hArg,Real.cos_pi_div_two,zero_div]

theorem circleCurrentZeta_continuousOn {D a : ℝ} (hD : 0 < D) (ha : 0 < a) :
    ContinuousOn (circleCurrentZeta D) (Icc a (Real.pi * D / 2)) :=
  fun s hs => (circleCurrentZeta_deriv hD (ha.trans_le hs.1) hs.2).continuousAt.continuousWithinAt

theorem circleCurrentZeta_antitone {D a : ℝ} (hD : 0 < D) (ha : 0 < a) :
    AntitoneOn (circleCurrentZeta D) (Icc a (Real.pi * D / 2)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
    (circleCurrentZeta_continuousOn hD ha)
  · intro s hs
    have h := interior_subset hs
    exact (circleCurrentZeta_deriv hD (ha.trans_le h.1) h.2).hasDerivWithinAt
  · intro s _
    exact neg_nonpos.mpr (add_nonneg (by positivity) (sq_nonneg _))

end ACS12.HighCurrent

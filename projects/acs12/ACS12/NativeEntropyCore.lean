import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-! The original finite-law entropy and support definitions, shared by its structural returns. -/
namespace ACS12.NativeCells

open Finset

noncomputable def nativeEntropyCost (P u : ℝ) : ℝ :=
  (P - 2) * u * Real.log u - ((P - 3) / 2) * u * Real.log ((1 + u ^ 2) / 2) -
    ((P - 1) / 2) * (u - 1)

noncomputable def nativeEntropyCostSlope (P u : ℝ) : ℝ :=
  (P - 2) * (Real.log u + 1) -
    ((P - 3) / 2) * (Real.log ((1 + u ^ 2) / 2) + 2 * u ^ 2 / (1 + u ^ 2)) - (P - 1) / 2

noncomputable def nativeEntropyCostCurvature (P u : ℝ) : ℝ :=
  (P - 2) / u - (P - 3) * u * (3 + u ^ 2) / (1 + u ^ 2) ^ 2

theorem nativeEntropyCost_deriv (P : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (nativeEntropyCost P) (nativeEntropyCostSlope P u) u := by
  have hBase : 0 < (1 + u ^ 2) / 2 := by positivity
  have hLog := ((((hasDerivAt_id u).pow 2).const_add 1).div_const 2).log hBase.ne'
  have h₁ := ((hasDerivAt_id u).mul (Real.hasDerivAt_log hu.ne')).const_mul (P - 2)
  have h₂ := ((hasDerivAt_id u).mul hLog).const_mul ((P - 3) / 2)
  convert (h₁.sub h₂).sub (((hasDerivAt_id u).sub_const 1).const_mul ((P - 1) / 2)) using 1
  · funext x
    simp only [nativeEntropyCost,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply,id_eq]
    ring
  · simp only [id_eq,Pi.pow_apply,Pi.mul_apply,pow_one,one_mul,mul_one,nativeEntropyCostSlope]
    field_simp [hu.ne',hBase.ne',show 1 + u ^ 2 ≠ 0 by positivity]
    <;> ring

theorem nativeEntropyCostSlope_deriv (P : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (nativeEntropyCostSlope P) (nativeEntropyCostCurvature P u) u := by
  have hBase : 0 < (1 + u ^ 2) / 2 := by positivity
  have hU := (hasDerivAt_id u).pow 2
  have hLog := ((hU.const_add 1).div_const 2).log hBase.ne'
  have hRat := (hU.const_mul 2).div (hU.const_add 1) (show 1 + u ^ 2 ≠ 0 by positivity)
  have h₁ := ((Real.hasDerivAt_log hu.ne').add_const 1).const_mul (P - 2)
  have h₂ := (hLog.add hRat).const_mul ((P - 3) / 2)
  convert (h₁.sub h₂).sub_const ((P - 1) / 2) using 1
  simp only [id_eq,Pi.pow_apply,Pi.div_apply,pow_one,one_mul,mul_one,nativeEntropyCostCurvature]
  field_simp [hu.ne',hBase.ne',show 1 + u ^ 2 ≠ 0 by positivity]
  <;> ring

theorem nativeEntropyCost_unit (P : ℝ) : nativeEntropyCost P 1 = 0 := by
  norm_num [nativeEntropyCost]

theorem nativeEntropyCostSlope_unit (P : ℝ) : nativeEntropyCostSlope P 1 = 0 := by
  norm_num [nativeEntropyCostSlope]
  ring

noncomputable def nativeSupportRatio (P : ℝ) : ℝ := 7 * (P - 1) / 2

theorem nativeSupportRatio_pos {P : ℝ} (hP : 3 ≤ P) : 0 < nativeSupportRatio P := by
  unfold nativeSupportRatio
  linarith only [hP]

theorem nativeSupportRatio_le {P : ℝ} (hP₅ : P ≤ 5) : nativeSupportRatio P ≤ 14 := by
  unfold nativeSupportRatio
  linarith only [hP₅]

noncomputable def nativeFiniteFunctional {ι : Type*} [Fintype ι]
    (P : ℝ) (w u : ι → ℝ) : ℝ :=
  P * Real.log (∑ i, w i * u i ^ (1 / P)) + ∑ i, w i * nativeEntropyCost P (u i)

end ACS12.NativeCells

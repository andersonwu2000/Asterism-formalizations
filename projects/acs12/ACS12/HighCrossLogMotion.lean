import ACS12.HighCrossExponent

/-! The complete source crossing price retains its actual whole-row mass factor under exponent motion. -/
namespace ACS12.HighCurrent

open Set
set_option backward.isDefEq.respectTransparency false

noncomputable def completeCrossLogPrice (p : ℝ) : ℝ :=
  (-p - 2) * Real.log 2 - Real.log (p - 1) +
    ((p + 1) / 2) * (Real.log 2 + Real.log (p - 1) - Real.log (p + 1)) +
      2 * Real.log ((35 * p + 19) / 54)

theorem completeCrossLogPrice_deriv {p : ℝ} (hp : 3 ≤ p) :
    HasDerivAt completeCrossLogPrice (-crossExponentDrift p) p := by
  have hPlus : 0 < p + 1 := by linarith only [hp]
  have hMinus : 0 < p - 1 := by linarith only [hp]
  have hDen : 0 < 35 * p + 19 := by linarith only [hp]
  have hPlusD := (hasDerivAt_id p).add_const 1
  have hMinusD := (hasDerivAt_id p).sub_const 1
  have hFirst := (((hasDerivAt_id p).neg.sub_const 2).mul_const (Real.log 2)).sub
    (hMinusD.log hMinus.ne')
  have hBracket := ((hMinusD.log hMinus.ne').const_add (Real.log 2)).sub (hPlusD.log hPlus.ne')
  have hProduct := (hPlusD.div_const 2).mul hBracket
  have hMass := ((((hasDerivAt_id p).const_mul 35).add_const 19).div_const 54).log
    (div_pos hDen (by norm_num)).ne'
  convert (hFirst.add hProduct).add (hMass.const_mul 2) using 1
  simp only [id_eq,Pi.add_apply,Pi.sub_apply]
  unfold crossExponentDrift
  field_simp [hPlus.ne',hMinus.ne',hDen.ne']
  <;> ring

theorem completeCrossLogPrice_strictAnti :
    StrictAntiOn completeCrossLogPrice (Ici 3) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · intro p hp
    exact (completeCrossLogPrice_deriv hp).continuousAt.continuousWithinAt
  · intro p hp
    have hp' : 3 ≤ p := interior_subset hp
    rw [(completeCrossLogPrice_deriv hp').deriv]
    exact neg_neg_of_pos (crossExponentDrift_pos hp')

end ACS12.HighCurrent

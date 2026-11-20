import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! The selected complete minimum-current crossing coefficient decreases on its entire exponent ray. -/
namespace ACS12.HighCurrent

open Set
set_option backward.isDefEq.respectTransparency false

noncomputable def crossExponentDrift (p : ℝ) : ℝ :=
  (Real.log 2 + Real.log (p + 1) - Real.log (p - 1)) / 2 - 70 / (35 * p + 19)

theorem crossExponentDrift_deriv {p : ℝ} (hp : 3 ≤ p) :
    HasDerivAt crossExponentDrift
      ((1225 * p ^ 2 - 1330 * p - 2811) /
        ((p ^ 2 - 1) * (35 * p + 19) ^ 2)) p := by
  have hPlus : 0 < p + 1 := by linarith only [hp]
  have hMinus : 0 < p - 1 := by linarith only [hp]
  have hDen : 0 < 35 * p + 19 := by linarith only [hp]
  have hP := (hasDerivAt_id p).add_const 1
  have hM := (hasDerivAt_id p).sub_const 1
  have hL := ((hP.log hPlus.ne').const_add (Real.log 2)).sub (hM.log hMinus.ne')
  have hD := ((hasDerivAt_id p).const_mul 35).add_const 19
  have hQ := (hasDerivAt_const p (70 : ℝ)).div hD hDen.ne'
  convert (hL.div_const 2).sub hQ using 1
  simp only [id_eq,one_mul]
  field_simp [hPlus.ne',hMinus.ne',hDen.ne',show p ^ 2 - 1 ≠ 0 by nlinarith only [hp]]
  <;> ring

theorem crossExponentDrift_pos {p : ℝ} (hp : 3 ≤ p) : 0 < crossExponentDrift p := by
  have hMono : MonotoneOn crossExponentDrift (Ici 3) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici _)
    · intro p hp
      exact (crossExponentDrift_deriv hp).continuousAt.continuousWithinAt
    · intro p hp
      exact (crossExponentDrift_deriv (interior_subset hp)).hasDerivWithinAt
    · intro p hp
      have hp' : 3 ≤ p := interior_subset hp
      have hNum : 0 < 1225 * p ^ 2 - 1330 * p - 2811 := by
        nlinarith only [sq_nonneg (p - 3),hp']
      exact div_nonneg hNum.le (mul_nonneg (by nlinarith only [hp']) (sq_nonneg _))
  have hAt : 0 < crossExponentDrift 3 := by
    have hLog : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      simpa only [show (2 : ℝ) ^ (2 : ℕ) = 4 by norm_num,Nat.cast_ofNat] using Real.log_pow (2 : ℝ) 2
    unfold crossExponentDrift
    norm_num only [show (3 : ℝ) + 1 = 4 by norm_num,show (3 : ℝ) - 1 = 2 by norm_num,
      show 35 * (3 : ℝ) + 19 = 124 by norm_num]
    rw [hLog]
    linarith only [Real.log_two_gt_d9]
  exact hAt.trans_le (hMono (by norm_num : (3 : ℝ) ∈ Ici 3) hp hp)

end ACS12.HighCurrent

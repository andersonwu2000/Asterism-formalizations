import ACS12.GammaArgumentCore
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Shared unit-shape Gamma reflection, independent of any source or translated spectral law. -/
namespace ACS12.GammaMeasure

theorem gammaUnit_norm_sq {t : ℝ} (ht : 0 < t) :
    ‖Complex.Gamma (gammaArgument 1 t)‖ ^ 2 = Real.pi * t / Real.sinh (Real.pi * t) := by
  let z := (t : ℂ) * Complex.I
  have hz : z ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne') Complex.I_ne_zero
  have hsin : Complex.sin ((Real.pi : ℂ) * z) = (Real.sinh (Real.pi * t) : ℂ) * Complex.I := by
    rw [show (Real.pi : ℂ) * z = ((Real.pi * t : ℝ) : ℂ) * Complex.I by dsimp [z]; push_cast; ring,
      Complex.sin_mul_I, ← Complex.ofReal_sinh]
  have hc : 1 - z = star (gammaArgument 1 t) := by
    simp [gammaArgument, z, Complex.conj_I, sub_eq_add_neg]
  have hprod : Complex.Gamma (gammaArgument 1 t) * Complex.Gamma (1 - z) =
      z * ((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * z)) := by
    rw [show gammaArgument 1 t = z + 1 by simp [gammaArgument, z, add_comm],
      Complex.Gamma_add_one z hz, mul_assoc, Complex.Gamma_mul_Gamma_one_sub]
  have h := (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht)).ne'
  rw [hc, Complex.star_def, Complex.Gamma_conj, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, hsin] at hprod
  have hr : z * ((Real.pi : ℂ) / ((Real.sinh (Real.pi * t) : ℂ) * Complex.I)) =
      ((Real.pi * t / Real.sinh (Real.pi * t) : ℝ) : ℂ) := by
    dsimp [z]
    push_cast
    field_simp [Complex.I_ne_zero, Complex.ofReal_ne_zero.mpr h]
  rw [hr] at hprod
  exact Complex.ofReal_injective hprod


end ACS12.GammaMeasure


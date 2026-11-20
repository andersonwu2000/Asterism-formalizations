import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-! The same original crossing endpoints retain the complete chord-product bound. -/
namespace ACS12.HighCurrent

theorem crossing_sine_product (u v : ℝ) :
    Real.sin u * Real.sin v ≤ Real.sin ((u + v) / 2) ^ 2 := by
  have hAdd := Real.cos_add u v
  have hSub := Real.cos_sub u v
  have hDouble := Real.cos_two_mul ((u + v) / 2)
  rw [show 2 * ((u + v) / 2) = u + v by ring] at hDouble
  have hTrig := Real.sin_sq_add_cos_sq ((u + v) / 2)
  have hBound := Real.cos_le_one (u - v)
  nlinarith only [hAdd,hSub,hDouble,hTrig,hBound]

theorem crossing_chord_product_square {D : ℝ} (u v : ℝ) :
    4 * ((D * Real.sin u) * (D * Real.sin v)) * Real.cos ((u + v) / 2) ^ 2 ≤
      (D * Real.sin (u + v)) ^ 2 := by
  have hProd := mul_le_mul_of_nonneg_left (crossing_sine_product u v)
    (by positivity : 0 ≤ 4 * D ^ 2 * Real.cos ((u + v) / 2) ^ 2)
  have hSum : Real.sin (u + v) =
      2 * Real.sin ((u + v) / 2) * Real.cos ((u + v) / 2) := by
    simpa only [show 2 * ((u + v) / 2) = u + v by ring] using Real.sin_two_mul ((u + v) / 2)
  rw [hSum]
  convert hProd using 1 <;> ring

end ACS12.HighCurrent

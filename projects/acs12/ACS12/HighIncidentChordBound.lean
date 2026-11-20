import ACS12.HighPhysicalReweight

/-! The actual minimum mass and the original smaller radial side bound every retained incident chord. -/
namespace ACS12.HighCurrent

theorem incident_inverse_chord_bound {p q m d : ℝ} (hp : 0 < p)
    (hq : 0 < q) (hd : 0 < d) (hqm : q ≤ m) (hRow : m / d ^ p ≤ 1 / 2) :
    1 / d ≤ (2 * q) ^ (-(1 / p)) := by
  have hDp : 0 < d ^ p := Real.rpow_pos_of_pos hd p
  have hPaid := (div_le_iff₀ hDp).mp hRow
  have hBase : 2 * q ≤ d ^ p := by linarith only [hqm,hPaid]
  have hPow := Real.rpow_le_rpow (mul_pos (by norm_num : (0 : ℝ) < 2) hq).le hBase
    (one_div_pos.mpr hp).le
  rw [← Real.rpow_mul hd.le,mul_one_div_cancel hp.ne',Real.rpow_one] at hPow
  have hInv := one_div_le_one_div_of_le
    (Real.rpow_pos_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hq) (1 / p)) hPow
  simpa only [Real.rpow_neg (mul_pos (by norm_num : (0 : ℝ) < 2) hq).le,one_div] using hInv

end ACS12.HighCurrent

namespace ACS12.Configuration

open HighCurrent
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {p : ℝ} (F : ACS12.Configuration n p)

theorem currentZeta_le_inverse_chord {o j : Fin n} (hjo : j ≠ o) :
    F.currentZeta o j ≤ 1 / F.currentChord o j := by
  have hZ := F.currentZeta_nonneg hjo.symm
  have hD := F.currentChord_pos hjo
  have hId := F.currentZeta_chord_identity hjo.symm
  change 1 / (2 * F.radius) ^ 2 + F.currentZeta o j ^ 2 = 1 / F.currentChord o j ^ 2 at hId
  have hInv := one_div_pos.mpr hD
  have hSquare : (1 / F.currentChord o j) ^ 2 = 1 / F.currentChord o j ^ 2 := by
    rw [div_pow,one_pow]
  have hPositive : 0 < 1 / (2 * F.radius) ^ 2 :=
    one_div_pos.mpr (sq_pos_of_pos (mul_pos (by norm_num) F.radius_pos))
  nlinarith only [hId,hSquare,hZ,hInv,hPositive]

end ACS12.Configuration

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-! The original complete crossing kernel has its exact positive-ratio maximum. -/
namespace ACS12.HighCurrent

open Set
set_option backward.isDefEq.respectTransparency false

theorem rationalPower_deriv {h r : ℝ} (hr : 0 ≤ r) :
    HasDerivAt (fun t : ℝ => t / (1 + t) ^ h)
      ((1 + (1 - h) * r) / (1 + r) ^ (h + 1)) r := by
  have hB : 0 < 1 + r := by linarith only [hr]
  have hBase := (hasDerivAt_id r).const_add 1
  have hPower := hBase.rpow_const (p := h) (Or.inl hB.ne')
  have hDeriv := (hasDerivAt_id r).div hPower (Real.rpow_pos_of_pos hB h).ne'
  simp only [id_eq,one_mul] at hDeriv
  rw [Real.rpow_sub hB,Real.rpow_one] at hDeriv
  have hNext : (1 + r) ^ (h + 1) = (1 + r) ^ h * (1 + r) := by
    rw [Real.rpow_add hB,Real.rpow_one]
  rw [hNext]
  convert hDeriv using 1
  field_simp [hB.ne',(Real.rpow_pos_of_pos hB h).ne']
  <;> ring

theorem rationalPower_global_peak {h r : ℝ} (hh : 1 < h) (hr : 0 ≤ r) :
    r / (1 + r) ^ h ≤ (1 / (h - 1)) / (1 + 1 / (h - 1)) ^ h := by
  let c := 1 / (h - 1)
  let f (t : ℝ) := t / (1 + t) ^ h
  have hhm : 0 < h - 1 := sub_pos.mpr hh
  have hc : 0 < c := one_div_pos.mpr hhm
  have hValue : (h - 1) * c = 1 := by unfold c; field_simp
  have hLeft : MonotoneOn f (Icc 0 c) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    · intro t ht
      exact (rationalPower_deriv ht.1).continuousAt.continuousWithinAt
    · intro t ht
      exact (rationalPower_deriv (interior_subset ht).1).hasDerivWithinAt
    · intro t ht
      have ht' : t ∈ Icc 0 c := interior_subset ht
      have hProd := mul_le_mul_of_nonneg_left ht'.2 hhm.le
      exact div_nonneg (by nlinarith only [hProd,hValue])
        (Real.rpow_pos_of_pos (by linarith only [ht'.1]) _).le
  have hRight : AntitoneOn f (Ici c) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici _)
    · intro t ht
      exact (rationalPower_deriv (hc.le.trans ht)).continuousAt.continuousWithinAt
    · intro t ht
      exact (rationalPower_deriv (hc.le.trans (interior_subset ht))).hasDerivWithinAt
    · intro t ht
      have ht' : c ≤ t := interior_subset ht
      have hProd := mul_le_mul_of_nonneg_left ht' hhm.le
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith only [hProd,hValue])
        (Real.rpow_pos_of_pos (by linarith only [hc,ht']) _).le
  by_cases hrc : r ≤ c
  · exact hLeft ⟨hr,hrc⟩ ⟨hc.le,le_rfl⟩ hrc
  · exact hRight (by change c ≤ c; exact le_rfl : c ∈ Ici c) (le_of_not_ge hrc) (le_of_not_ge hrc)

end ACS12.HighCurrent

import ACS12.HighCurrentKernel
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! The literal current hump is continuous and has exactly the one-height receiving shape. -/
namespace ACS12.HighCurrent

open Set

theorem currentHump_continuous (τ : ℝ) : Continuous (currentHump τ) := by
  unfold currentHump
  apply Continuous.if_le (by fun_prop) continuous_const continuous_id continuous_const
  intro z hz
  change z = τ at hz
  simp only [hz,sub_self,mul_zero]

theorem currentHump_polynomial_deriv (τ z : ℝ) :
    HasDerivAt (fun s : ℝ => τ * s ^ 3 * (τ - s)) (τ * z ^ 2 * (3 * τ - 4 * z)) z := by
  convert ((((hasDerivAt_id z).pow 3).const_mul τ).mul
    ((hasDerivAt_const z τ).sub (hasDerivAt_id z))) using 1
  simp only [id_eq,Pi.pow_apply,Pi.sub_apply,pow_one,one_mul]
  ring

theorem currentHump_min {τ a b c : ℝ} (hτ : 0 ≤ τ) (ha : 0 ≤ a)
    (hab : a ≤ b) (hbc : b ≤ c) :
    min (currentHump τ a) (currentHump τ c) ≤ currentHump τ b := by
  have hb : 0 ≤ b := ha.trans hab
  have hc : 0 ≤ c := hb.trans hbc
  by_cases haτ : a ≤ τ
  · by_cases hcτ : c ≤ τ
    · let q (z : ℝ) := τ * z ^ 3 * (τ - z)
      have hD (z : ℝ) : HasDerivAt q (τ * z ^ 2 * (3 * τ - 4 * z)) z :=
        currentHump_polynomial_deriv τ z
      have hMono : MonotoneOn q (Icc 0 (3 * τ / 4)) := by
        apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) (by unfold q; fun_prop)
          (fun z _ => (hD z).hasDerivWithinAt)
        intro z hz
        have hz' := interior_subset hz
        exact mul_nonneg (mul_nonneg hτ (sq_nonneg _)) (by linarith only [hz'.2])
      have hAnti : AntitoneOn q (Icc (3 * τ / 4) τ) := by
        apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) (by unfold q; fun_prop)
          (fun z _ => (hD z).hasDerivWithinAt)
        intro z hz
        have hz' := interior_subset hz
        exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hτ (sq_nonneg _)) (by linarith only [hz'.1])
      have hbτ : b ≤ τ := hbc.trans hcτ
      simp only [currentHump,if_pos haτ,if_pos hbτ,if_pos hcτ]
      by_cases hbPeak : b ≤ 3 * τ / 4
      · exact min_le_left _ _ |>.trans (hMono ⟨ha,hab.trans hbPeak⟩ ⟨hb,hbPeak⟩ hab)
      · exact min_le_right _ _ |>.trans
          (hAnti ⟨(le_of_not_ge hbPeak),hbτ⟩ ⟨(le_of_not_ge hbPeak).trans hbc,hcτ⟩ hbc)
    · calc
        _ ≤ currentHump τ c := min_le_right _ _
        _ = 0 := by simp only [currentHump,if_neg hcτ]
        _ ≤ _ := currentHump_nonneg hτ hb
  · calc
      _ ≤ currentHump τ a := min_le_left _ _
      _ = 0 := by simp only [currentHump,if_neg haτ]
      _ ≤ _ := currentHump_nonneg hτ hb

end ACS12.HighCurrent

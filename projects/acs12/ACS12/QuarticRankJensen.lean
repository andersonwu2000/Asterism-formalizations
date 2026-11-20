import ACS12.QuarticDebitWord
import ACS12.QuarticRankMeans
import ACS12.QuarticRankReceipt
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! One exponential Jensen comparison combines all three receipts at the same rank. -/
namespace ACS12.NativeCells

open Finset
set_option backward.isDefEq.respectTransparency false

theorem quarticRank_rate_lower {n : ℕ} [NeZero n] (hn : 5 ≤ n)
    {w : Fin n → ℝ} (hw : ∀ i, 0 < w i) (hcap : ∀ i, w i ≤ 1 / 4)
    (hW : ∑ i, w i = 1) {r : Fin n} (hr : r ∈ quarticFarRanks n) {t : ℝ} (ht : 0 ≤ t) :
    quarticRegularGap r * Real.exp (-(4 + t) * quarticRegularGap r) *
      Real.exp (-(quarticDebitA w + quarticDebitB w * t)) ≤
      (∑ i, quarticRankPrefactor w i (i + r) * quarticActualGap w i (i + r) *
        Real.exp (-(4 + t) * quarticActualGap w i (i + r))) / n := by
  let p := 4 + t
  let g := quarticRegularGap r
  let G (i : Fin n) := quarticActualGap w i (i + r)
  let c (i : Fin n) := quarticRankPrefactor w i (i + r)
  let X (i : Fin n) := Real.log (c i) + Real.log (G i / g) - p * (G i - g)
  have hN : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hp : 0 ≤ p := by dsimp only [p]; positivity
  have hg : 0 < g := (by norm_num : (0 : ℝ) < 1 / 4).trans_le (quarticRegularGap_lower hn hr)
  have hw₁ (i : Fin n) : w i < 1 := by linarith only [hcap i]
  obtain ⟨hG, hLogG⟩ := quartic_rank_receipt hn hw hcap hW hr
  have hC (i : Fin n) : 0 < c i := quarticRankPrefactor_pos (by omega) hw hw₁ i _
  have hr₀ : r ≠ 0 := (mem_erase.mp (mem_erase.mp (mem_erase.mp hr).2).2).1
  have hLogC := quarticRankPrefactor_mean_lower hn hw hcap hW r
  have hMeanG := quarticActualGap_mean_upper hn hw hcap hW hr₀
  have hLogG' := div_le_div_of_nonneg_right hLogG hN.le
  have hMeanX :
      -(quarticDebitA w + quarticDebitB w * t) ≤ (∑ i, X i) / n := by
    have hSum : (∑ i, X i) = (∑ i, Real.log (c i)) + (∑ i, Real.log (G i / g)) -
        p * ((∑ i, G i) - (n : ℝ) * g) := by
      simp only [X, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const,
        card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hUpper := mul_le_mul_of_nonneg_left hMeanG hp
    rw [hSum, sub_div, add_div, mul_div_assoc, sub_div, mul_div_cancel_left₀ _ hN.ne']
    unfold quarticDebitA quarticDebitB quarticReverseEntropy quarticWidthVariance
    dsimp only [p, c, g, G] at *
    simp only [div_eq_mul_inv] at *
    linarith only [hLogC, hUpper, hLogG']
  have hWeights : (∑ i : Fin n, (n : ℝ)⁻¹) = 1 := by
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_inv_cancel₀ hN.ne']
  have hJ := convexOn_exp.map_sum_le (t := (univ : Finset (Fin n)))
    (w := fun _ => (n : ℝ)⁻¹) (p := X)
    (fun _ _ => (inv_pos.mpr hN).le) hWeights (fun i _ => Set.mem_univ (X i))
  simp only [smul_eq_mul, ← div_eq_inv_mul, ← sum_div] at hJ
  have h := (Real.exp_le_exp.mpr hMeanX).trans hJ
  have hScale : 0 ≤ g * Real.exp (-p * g) := mul_nonneg hg.le (Real.exp_pos _).le
  have hFinal := mul_le_mul_of_nonneg_left h hScale
  rw [← mul_div_assoc, mul_sum] at hFinal
  have hTerm (i : Fin n) : g * Real.exp (-p * g) * Real.exp (X i) =
      c i * G i * Real.exp (-p * G i) := by
    dsimp only [X]
    rw [Real.exp_sub, Real.exp_add, Real.exp_log (hC i), Real.exp_log (div_pos (hG i) hg)]
    rw [show p * (G i - g) = p * G i + (-p * g) by ring, Real.exp_add,
      show -p * G i = -(p * G i) by ring, Real.exp_neg]
    change g * Real.exp (-p * g) * (c i * (G i / g) / (Real.exp (p * G i) * Real.exp (-p * g))) = _
    field_simp [hg.ne', (Real.exp_pos (-p * g)).ne', (Real.exp_pos (p * G i)).ne']
  rwa [sum_congr rfl (fun i _ => hTerm i)] at hFinal

end ACS12.NativeCells

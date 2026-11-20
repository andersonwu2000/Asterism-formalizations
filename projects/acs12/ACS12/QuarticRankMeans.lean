import ACS12.QuarticRankEnergy
import Mathlib.Analysis.Convex.Jensen

/-! The cyclic means for the actual prefactor and the two endpoint sines. -/
namespace ACS12.NativeCells

open Finset
set_option backward.isDefEq.respectTransparency false

theorem quarticRankPrefactor_mean_lower {n : ℕ} [NeZero n] (hn : 5 ≤ n)
    {w : Fin n → ℝ} (hw : ∀ i, 0 < w i) (hcap : ∀ i, w i ≤ 1 / 4) (hW : ∑ i, w i = 1)
    (r : Fin n) :
    (∑ i, Real.log ((n : ℝ) * w i)) / n - (7 / 2) * (∑ i, (w i - 1 / (n : ℝ)) ^ 2) / n ≤
      (∑ i, Real.log (quarticRankPrefactor w i (i + r))) / n := by
  let x := 1 / (n : ℝ)
  let L (i : Fin n) := Real.log (quarticRankFactor (w i))
  have hN : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hN5 : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : 0 < x := by dsimp [x]; positivity
  have hxCap : x ≤ 1 / 4 := (div_le_iff₀ hN).mpr (by linarith)
  have hw₁ (i : Fin n) : w i < 1 := by linarith only [hcap i]
  have hF (i : Fin n) := quarticRankFactor_pos (hw i) (hw₁ i)
  have hS := quarticRankScale_pos (show 2 ≤ n by omega)
  have hCycle : (∑ i, L (i + r)) = ∑ i, L i := Equiv.sum_comp (Equiv.addRight r) L
  have hSum :
      (∑ i, Real.log (quarticRankPrefactor w i (i + r))) =
        (∑ i, (Real.log (w i) - quarticLogGauge (w i))) -
          (n : ℝ) * (Real.log x - quarticLogGauge x) := by
    have hTerm (i : Fin n) :
        Real.log (quarticRankPrefactor w i (i + r)) = L i + L (i + r) - 2 * Real.log (quarticRankFactor x) := by
      rw [quarticRankPrefactor, Real.log_div (mul_pos (hF i) (hF (i + r))).ne' hS.ne',
        Real.log_mul (hF i).ne' (hF (i + r)).ne', quarticRankScale, Real.log_pow]
      rfl
    simp only [hTerm, sum_sub_distrib, sum_add_distrib, hCycle, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    change (∑ i, L i) + ∑ i, L i - _ = _
    rw [← two_mul, mul_sum]
    simp only [L, quarticRankFactor_log (hw _) (hcap _), sum_sub_distrib]
    have hg := quarticRankFactor_log hx hxCap
    linarith only [congrArg ((n : ℝ) * ·) hg]
  have hLogx : Real.log (n : ℝ) = -Real.log x := by
    dsimp [x]
    rw [Real.log_div (by norm_num) hN.ne', Real.log_one, zero_sub, neg_neg]
  have hLog (i : Fin n) : Real.log ((n : ℝ) * w i) = Real.log (w i) - Real.log x := by
    rw [Real.log_mul hN.ne' (hw i).ne', hLogx]
    ring
  rw [hSum]
  simp only [hLog, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hGauge : (∑ i,quarticLogGauge (w i))/(n:ℝ) ≤
      quarticLogGauge x + (7/2)*(∑ i,(w i-x)^2)/(n:ℝ) := quarticLogGauge_mean_le hn hw hcap hW
  have hG := (div_le_iff₀ hN).mp hGauge
  rw [add_mul,div_mul_cancel₀ _ hN.ne'] at hG
  apply (le_div_iff₀ hN).mpr
  rw [sub_mul,div_mul_cancel₀ _ hN.ne',div_mul_cancel₀ _ hN.ne']
  linarith only [hG]

theorem quarticActualGap_mean_upper {n : ℕ} [NeZero n] (hn : 5 ≤ n)
    {w : Fin n → ℝ} (hw : ∀ i, 0 < w i) (hcap : ∀ i, w i ≤ 1 / 4) (hW : ∑ i, w i = 1)
    {r : Fin n} (hr : r ≠ 0) :
    (∑ i, quarticActualGap w i (i + r)) / n ≤ quarticRegularGap r -
      (∑ i, Real.log ((n : ℝ) * w i)) / n + 2 * (∑ i, (w i - 1 / (n : ℝ)) ^ 2) / n := by
  let a := quarticCellAngle w
  let t (i : Fin n) := halfArc a i (i + r)
  let L (i : Fin n) := Real.log (Real.sin (Real.pi * w i))
  let θ := Real.pi * (r : ℝ) / (n : ℝ)
  have hN : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hN₁ : (1 : ℝ) < n := Nat.one_lt_cast.mpr (by omega)
  have ha := center_strictMono (massCells_strictMonoOn hw)
  have hb (i : Fin n) : a i ∈ Set.Ioo 0 (2 * Real.pi) :=
    center_mem (massCells_strictMonoOn hw) (massCells_zero w) (massCells_end hW) i
  have hDiff (i : Fin n) : i + r ≠ i := fun h => hr (add_left_cancel (h.trans (add_zero i).symm))
  have ht (i : Fin n) : t i ∈ Set.Ioo 0 Real.pi :=
    halfArc_mem ha (fun k => (hb k).1.le) (fun k => (hb k).2) (hDiff i)
  have hSin (i : Fin n) : 0 < Real.sin (t i) := Real.sin_pos_of_pos_of_lt_pi (ht i).1 (ht i).2
  have hWsin (i : Fin n) : 0 < Real.sin (Real.pi * w i) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos (hw i)) (by nlinarith only [Real.pi_pos, hcap i])
  have hCycle : (∑ i, L (i + r)) = ∑ i, L i := Equiv.sum_comp (Equiv.addRight r) L
  have hGap :
      (∑ i, quarticActualGap w i (i + r)) = (∑ i, Real.log (Real.sin (t i))) - ∑ i, L i := by
    have hTerm (i : Fin n) : quarticActualGap w i (i + r) = Real.log (Real.sin (t i)) - (L i + L (i + r)) / 2 := by
      change Real.log (Real.sin (t i) / Real.sqrt (Real.sin (Real.pi * w i) * Real.sin (Real.pi * w (i + r)))) = _
      rw [Real.log_div (hSin i).ne' (Real.sqrt_pos.mpr (mul_pos (hWsin i) (hWsin (i + r)))).ne',
        Real.log_sqrt (mul_nonneg (hWsin i).le (hWsin (i + r)).le),
        Real.log_mul (hWsin i).ne' (hWsin (i + r)).ne']
    simp only [hTerm, sum_sub_distrib, ← sum_div, sum_add_distrib, hCycle]
    ring
  have hConst : (∑ i : Fin n, (n : ℝ)⁻¹) = 1 := by
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_inv_cancel₀ hN.ne']
  have hJ := strictConcaveOn_log_Ioi.concaveOn.le_map_sum (t := (univ : Finset (Fin n)))
    (w := fun _ => (n : ℝ)⁻¹) (p := fun i => Real.sin (t i))
    (fun _ _ => (inv_pos.mpr hN).le) hConst (fun i _ => show Real.sin (t i) ∈ Set.Ioi 0 from hSin i)
  have hJ' : (∑ i,Real.log (Real.sin (t i)))/(n:ℝ) ≤ Real.log ((∑ i,Real.sin (t i))/(n:ℝ)) := by
    simpa only [smul_eq_mul,← mul_sum,div_eq_inv_mul] using hJ
  have hMean := Rank.sine_sum_bound univ ⟨0, mem_univ 0⟩ t (fun i _ => Set.Ioo_subset_Icc_self (ht i))
  rw [card_univ, Fintype.card_fin, show (∑ i, t i) = (n : ℝ) * θ from Rank.halfArc_rank_sum n a r,
    mul_div_cancel_left₀ _ hN.ne'] at hMean
  have hSMean : (∑ i,Real.sin (t i))/(n:ℝ) ≤ Real.sin θ :=
    (div_le_iff₀ hN).mpr (by simpa only [mul_comm] using hMean)
  have hR : (∑ i, Real.log (Real.sin (t i))) / n ≤ Real.log (Real.sin θ) :=
    hJ'.trans (Real.log_le_log (div_pos (sum_pos (fun i _ => hSin i) ⟨0, mem_univ 0⟩) hN) hSMean)
  have hWidth := quarticLogSin_mean_lower hn hw hcap hW
  rw [hGap, quarticRegularGap, Real.log_div (rank_sine_pos hr).ne' (nearest_sine_pos (by omega : 2 ≤ n)).ne',
    sub_div]
  change (∑ i, Real.log (Real.sin (t i))) / n - (∑ i, L i) / n ≤
    Real.log (Real.sin θ) - _ - _ + _
  linarith only [hR, hWidth]

end ACS12.NativeCells

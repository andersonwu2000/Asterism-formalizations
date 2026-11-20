import ACS12.QuarticPhysicalCount
import ACS12.QuarticPhysicalRatio
import ACS12.QuarticRayDefect
import ACS12.QuarticPaymentJoin
import ACS12.FourSiteExchange
import ACS12.ShortCycle

/-! The quartic anchor receives the same physical one-fifth and count bounds on the full ray. -/
namespace ACS12.NativeCells

open Pressure (massTotal massTotal_pos massWeight massWeight_sum_one)

theorem quartic_separation {n : ℕ} (hn : 5 ≤ n) {p : ℝ} (hp : 4 ≤ p)
    {m : Fin n → ℝ} (hm : ∀ i, 0 < m i)
    (hfloor : ∀ i, 1 / 5 ≤ (n : ℝ) * massWeight m i)
    (hcap : ∀ i, massWeight m i ≤ 1 / 4)
    (hne : ¬ ∀ i, massWeight m i = 1 / (n : ℝ))
    (hZ : 0 < quarticZ p (massWeight m)) :
    quarticEntropy (massWeight m) / 50 +
      (1 - quarticZ 4 (massWeight m)) / quarticRegularRatio p n <
        Real.log (rootRow p m / quarticUpper p m) := by
  letI : NeZero n := ⟨by omega⟩
  have hM := massTotal_pos (by omega) hm
  have hw (i : Fin n) : 0 < massWeight m i := div_pos (hm i) hM
  have hW := massWeight_sum_one (by omega) hm
  have hInf : quarticRankFloor n ≤ quarticRegularRatio p n :=
    quarticNearest_lower_regular hn (by linarith only [hp])
  exact quartic_separation_of_defect hn hp hm hfloor hcap hne hZ hInf
    (quartic_ray_defect_le hn hw hcap hW hp)

end ACS12.NativeCells

namespace ACS12.Configuration

open Finset NativeCells Pressure
set_option backward.isDefEq.respectTransparency false

theorem rigidity_atLeastFour_of_five {n : ℕ} {p : ℝ} (F : Configuration n p)
    (hn : 5 ≤ n) (hp : 4 ≤ p) : IsEqualMassRegular F := by
  have hn₂ : 2 ≤ n := by omega
  have hn₀ : 0 < n := by omega
  have hP : 0 < p := by linarith only [hp]
  have hN : 0 < (n : ℝ) := Nat.cast_pos.mpr hn₀
  let σ := Tuple.sort F.phase
  let m := F.mass ∘ σ
  let w := massWeight m
  let M := massTotal m
  have hm (i : Fin n) : 0 < m i := F.mass_pos (σ i)
  have hM : 0 < M := massTotal_pos hn₀ hm
  have hTotal : M = massTotal F.mass := Equiv.sum_comp σ F.mass
  have hw (i : Fin n) : 0 < w i := div_pos (hm i) hM
  have hW := massWeight_sum_one hn₀ hm
  by_cases hUniform : ∀ i, w i = 1 / (n : ℝ)
  · refine F.equal_mass_regular hn₂ hP.le (div_pos hM hN) ?_
    intro i
    have hi := hUniform (σ.symm i)
    change F.mass (σ (σ.symm i)) / M = 1 / (n : ℝ) at hi
    rw [Equiv.apply_symm_apply] at hi
    have hh := (div_eq_iff hM.ne').mp hi
    simpa only [one_div, div_eq_mul_inv, mul_one, one_mul, mul_comm] using hh
  · obtain ⟨o, _, hMax'⟩ := (univ : Finset (Fin n)).exists_max_image F.mass ⟨⟨0, hn₀⟩, mem_univ _⟩
    have hMax (i : Fin n) : F.mass i ≤ F.mass o := hMax' i (mem_univ _)
    have hCount := F.quartic_massTotal_div_mass_gt_four hn hp o hMax
    have hCount' : 4 * F.mass o < M := by rw [hTotal]; exact (lt_div_iff₀ (F.mass_pos o)).mp hCount
    have hCap (i : Fin n) : w i ≤ 1 / 4 := by
      change m i / M ≤ _
      apply (div_le_iff₀ hM).mpr
      have h := hMax (σ i)
      change m i ≤ F.mass o at h
      linarith only [h, hCount']
    have hFloor (i : Fin n) : 1 / 5 ≤ (n : ℝ) * w i := by
      have h := sum_le_sum (s := univ) (fun j _ => (F.quartic_mass_ratio_five hn hp (σ j) (σ i)).le)
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h
      change M ≤ (n : ℝ) * (5 * m i) at h
      change 1 / 5 ≤ (n : ℝ) * (m i / M)
      rw [← mul_div_assoc, le_div_iff₀ hM]
      linarith only [h]
    have hw₁ (i : Fin n) : w i < 1 := lt_of_le_of_lt (hCap i) (by norm_num)
    have hUpper := commonRow_le_quarticUpper F hn₂ hP hw₁
    have hC : 0 < (2 * F.radius) ^ p * (2 * F.coefficient * F.radius ^ 2) :=
      mul_pos (Real.rpow_pos_of_pos (mul_pos zero_lt_two F.radius_pos) _)
        (mul_pos (mul_pos zero_lt_two (F.coefficient_pos hn₂)) (sq_pos_of_pos F.radius_pos))
    have hU : 0 < quarticUpper p m := hC.trans_le hUpper
    have hZ : 0 < quarticZ p w := by
      have hDiv : 0 < quarticZ p w / M :=
        pos_of_mul_pos_left hU (Real.exp_pos _).le
      exact (div_pos_iff_of_pos_right hM).mp hDiv
    have hSep := quartic_separation hn hp hm hFloor hCap hUniform hZ
    have hΔ : 0 ≤ 1 - quarticZ 4 w := sub_nonneg.mpr (quartic_anchor hw hw₁ hW)
    have hReg := quarticRegularRatio_pos hP (show (1 : ℝ) < n by exact_mod_cast (show 1 < n by omega))
    have hH := quarticEntropy_pos (by omega) hw hUniform
    have hLog : 0 < Real.log (rootRow p m / quarticUpper p m) :=
      (add_pos_of_pos_of_nonneg (div_pos hH (by norm_num : (0 : ℝ) < 50)) (div_nonneg hΔ hReg.le)).trans hSep
    have hMean : Rank.meanRoot p m = Rank.meanRoot p F.mass := by
      unfold Rank.meanRoot
      rw [show (∑ i, m i ^ (1 / (p + 1))) = ∑ i, F.mass i ^ (1 / (p + 1)) from
        Equiv.sum_comp σ (fun i => F.mass i ^ (1 / (p + 1)))]
    have hRootEq : rootRow p m = rootRow p F.mass := by unfold rootRow; rw [hMean]
    have hRoot : rootRow p m ≤ quarticUpper p m := by
      rw [hRootEq]
      exact (rootRow_le_commonRow hn₂ hP F).trans hUpper
    have hRoot₀ : 0 ≤ rootRow p m := by
      unfold rootRow
      exact mul_nonneg (analyticRow_pos hP (show (1 : ℝ) < n by exact_mod_cast (show 1 < n by omega))).le
        (Real.rpow_nonneg (div_nonneg (sum_nonneg (fun i _ => Real.rpow_nonneg (hm i).le _)) hN.le) _)
    exact False.elim ((not_lt_of_ge (Real.log_nonpos (div_nonneg hRoot₀ hU.le) ((div_le_one hU).mpr hRoot))) hLog)

theorem rigidity_atLeastFour {n : ℕ} {p : ℝ} (F : Configuration n p)
    (hn : 2 ≤ n) (hp : 4 ≤ p) : IsEqualMassRegular F := by
  by_cases hFive : 5 ≤ n
  · exact F.rigidity_atLeastFour_of_five hFive hp
  · have hUpper : n ≤ 4 := by omega
    interval_cases n
    · exact F.two_sites_regular (by linarith only [hp])
    · exact F.three_sites_regular (by linarith only [hp])
    · exact F.four_sites_regular (by linarith only [hp])

end ACS12.Configuration

import ACS12.QuarticRankJensen
import ACS12.QuarticRaySupport

/-! The literal row derivative is paid rank by rank before integrating the entire ray. -/
namespace ACS12.NativeCells

open Finset
set_option backward.isDefEq.respectTransparency false

noncomputable def quarticRankFloor (n : ℕ) : ℝ := 2 * ((n : ℝ) * quarticRankScale n)

private theorem regularGap_eq_zero_nearest {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    {r : Fin n} (hr : r = 1 ∨ r = -1) : quarticRegularGap r = 0 := by
  obtain ⟨h₁, h₂⟩ := nearest_sines hn
  rcases hr with rfl | rfl
  · rw [quarticRegularGap, h₁, div_self (nearest_sine_pos hn).ne', Real.log_one]
  · rw [quarticRegularGap, h₂, div_self (nearest_sine_pos hn).ne', Real.log_one]

theorem quartic_ray_defect_le {n : ℕ} [NeZero n] (hn : 5 ≤ n) {w : Fin n → ℝ}
    (hw : ∀ i, 0 < w i) (hcap : ∀ i, w i ≤ 1 / 4) (hW : ∑ i, w i = 1)
    {p : ℝ} (hp : 4 ≤ p) :
    quarticZ p w - quarticRegularRatio p n ≤ quarticZ 4 w - 1 +
      quarticRankFloor n * ((13 / 400) * (quarticDebitA w + quarticDebitB w / 2) +
        (p - 4) * (69 / 1250) * (quarticDebitA w + quarticDebitB w)) := by
  let E := (univ : Finset (Fin n)).erase 0
  let C := quarticRankScale n
  let A := quarticDebitA w
  let B := quarticDebitB w
  let I := quarticRankFloor n
  let G (r i : Fin n) := quarticActualGap w i (i + r)
  let c (r i : Fin n) := quarticRankPrefactor w i (i + r)
  let g := @quarticRegularGap n
  let Q (r : Fin n) := Real.exp (-g r)
  let F (t : ℝ) := C * ∑ r ∈ E,
    ((∑ i, c r i * Real.exp (-(4 + t) * G r i)) - (n : ℝ) * Real.exp (-(4 + t) * g r))
  let F' (t : ℝ) := C * ∑ r ∈ E, ((n : ℝ) * (g r * Real.exp (-(4 + t) * g r)) -
    ∑ i, c r i * G r i * Real.exp (-(4 + t) * G r i))
  have hn₂ : 2 ≤ n := by omega
  have hN : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hN₁ : 1 < (n : ℝ) := Nat.one_lt_cast.mpr (by omega)
  have hC : 0 < C := quarticRankScale_pos hn₂
  have hI : 0 ≤ I := by dsimp only [I, quarticRankFloor]; positivity
  have hw₁ (i : Fin n) : w i < 1 := by linarith only [hcap i]
  have hFit (t : ℝ) (ht : 0 ≤ t) : F t = quarticZ (4 + t) w - quarticRegularRatio (4 + t) n := by
    have hp : 0 < 4 + t := by positivity
    rw [quarticZ_rank_sum hn₂ hp hw hw₁ hW, quarticRegular_rank_sum hn₂ hp]
    unfold F G c g
    rw [sum_sub_distrib, ← mul_sum]
    ring
  have hDerivative (t : ℝ) (_ : 0 ≤ t) : HasDerivAt F (F' t) t := by
    have hE (x : ℝ) : HasDerivAt (fun v => Real.exp (-(4 + v) * x))
        (-x * Real.exp (-(4 + t) * x)) t := by
      simpa only [Pi.neg_apply, id_eq, neg_one_mul, mul_comm (Real.exp (-(4 + t) * x)) (-x)] using
        (((hasDerivAt_id t).const_add 4).neg.mul_const x).exp
    have hThis (r : Fin n) :
        HasDerivAt (fun v => (∑ i, c r i * Real.exp (-(4 + v) * G r i)) -
          (n : ℝ) * Real.exp (-(4 + v) * g r))
          ((n : ℝ) * (g r * Real.exp (-(4 + t) * g r)) -
            ∑ i, c r i * G r i * Real.exp (-(4 + t) * G r i)) t := by
      convert (HasDerivAt.fun_sum (u := (univ : Finset (Fin n))) (fun i _ =>
        (hE (G r i)).const_mul (c r i))).sub ((hE (g r)).const_mul (n : ℝ)) using 1
      have hTerm (i : Fin n) : -(c r i * G r i * Real.exp (-(4 + t) * G r i)) =
          c r i * (-G r i * Real.exp (-(4 + t) * G r i)) := by ring
      simp only [← hTerm, sum_neg_distrib]
      ring
    exact (HasDerivAt.fun_sum (u := E) (fun r _ => hThis r)).const_mul C
  have hPrice (v : ℝ) (hv : 0 ≤ v) : F' v ≤ I * ∑ r ∈ quarticFarRanks n,
      (1 / 2 : ℝ) * Q r ^ 4 * (g r * Real.exp (-g r * v) * (A + B * v)) := by
    let f (r : Fin n) := (n : ℝ) * (g r * Real.exp (-(4 + v) * g r)) -
      ∑ i, c r i * G r i * Real.exp (-(4 + v) * G r i)
    let k (r : Fin n) := Q r ^ 4 * (g r * Real.exp (-g r * v) * (A + B * v))
    have hPoint (r : Fin n) (hr : r ∈ E) : f r ≤ if r ∈ quarticFarRanks n then (n : ℝ) * k r else 0 := by
      by_cases hFar : r ∈ quarticFarRanks n
      · rw [if_pos hFar]
        have h := quarticRank_rate_lower hn hw hcap hW hFar hv
        have hK := Real.add_one_le_exp (-(A + B * v))
        have hG : 0 ≤ g r := (by norm_num : (0 : ℝ) ≤ 1 / 4).trans (quarticRegularGap_lower hn hFar)
        have hK' := mul_le_mul_of_nonneg_left hK
          (mul_nonneg hG (Real.exp_pos (-(4 + v) * g r)).le)
        have hE : Q r ^ 4 * Real.exp (-g r * v) = Real.exp (-(4 + v) * g r) := by
          dsimp only [Q]
          rw [← Real.exp_nat_mul, ← Real.exp_add]
          congr 1
          push_cast
          ring
        have hk : k r = g r * Real.exp (-(4 + v) * g r) * (A + B * v) := by
          dsimp only [k]
          rw [show Q r ^ 4 * (g r * Real.exp (-g r * v) * (A + B * v)) =
            g r * (Q r ^ 4 * Real.exp (-g r * v)) * (A + B * v) by ring, hE]
        change g r * Real.exp (-(4 + v) * g r) * Real.exp (-(A + B * v)) ≤
          (∑ i, c r i * G r i * Real.exp (-(4 + v) * G r i)) / n at h
        have hL := (le_div_iff₀ hN).mp (hK'.trans h)
        unfold f
        rw [hk]
        linarith only [hL]
      · rw [if_neg hFar]
        have hNear : r = 1 ∨ r = -1 := by
          unfold quarticFarRanks at hFar
          simp only [mem_erase] at hFar
          by_contra! he
          exact hFar ⟨he.2, he.1, mem_erase.mp hr⟩
        have hNon : 0 ≤ ∑ i, c r i * G r i * Real.exp (-(4 + v) * G r i) := by
          apply sum_nonneg
          intro i _
          have hDiff : i + r ≠ i := fun h => (mem_erase.mp hr).1 (add_left_cancel (h.trans (add_zero i).symm))
          exact mul_nonneg (mul_nonneg (quarticRankPrefactor_pos hn₂ hw hw₁ i _).le
            (quarticActualGap_nonneg hw hcap hW hDiff)) (Real.exp_pos _).le
        unfold f
        rw [show g r = 0 from regularGap_eq_zero_nearest hn₂ hNear, zero_mul, mul_zero]
        exact sub_nonpos.mpr hNon
    have h := sum_le_sum hPoint
    rw [← sum_filter] at h
    have hFilter : E.filter (· ∈ quarticFarRanks n) = quarticFarRanks n := by
      ext r
      simp only [mem_filter]
      constructor
      · exact And.right
      · intro hr
        exact ⟨(mem_erase.mp (mem_erase.mp hr).2).2, hr⟩
    rw [hFilter, ← mul_sum] at h
    have hB := mul_le_mul_of_nonneg_left h hC.le
    change F' v ≤ _ at hB
    unfold I quarticRankFloor
    have hEq : ∑ r ∈ quarticFarRanks n, (1/2:ℝ) * Q r ^ 4 *
        (g r * Real.exp (-g r * v) * (A + B * v)) = (1/2:ℝ) * ∑ r ∈ quarticFarRanks n, k r := by
      rw [mul_sum]
      apply sum_congr rfl
      intro r _
      unfold k
      ring
    rw [hEq]
    linarith only [hB]
  have hMoment := quarticRegular_moments hn
  have hm₂ : (∑ r ∈ quarticFarRanks n, (1/2:ℝ) * Real.exp (-g r) ^ 2) ≤ 13/20 := by
    rw [← mul_sum]
    linarith only [hMoment.1]
  have hm₄ : (∑ r ∈ quarticFarRanks n, (1/2:ℝ) * Real.exp (-g r) ^ 4) ≤ 3/20 := by
    rw [← mul_sum]
    linarith only [hMoment.2]
  obtain ⟨hA, hB, hBA⟩ := quarticDebit_nonneg (by omega : 1 ≤ n) hw hW
  have h := quarticRay_defect_le (quarticFarRanks n) (fun _ => 1/2) g F F' hA hB hBA
    (sub_nonneg.mpr hp) hI (fun _ _ => by norm_num) (fun _ hr => quarticRegularGap_lower hn hr)
    hm₂ hm₄ hDerivative hPrice
  rw [hFit _ (sub_nonneg.mpr hp), hFit 0 (by norm_num), show 4 + (p - 4) = p by ring, add_zero,
    quarticRegularRatio_four hN₁] at h
  exact h

end ACS12.NativeCells

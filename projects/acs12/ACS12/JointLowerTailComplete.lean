import ACS12.JointLowerTailPrice
import ACS12.JointFarValue

/-! Full native third-derivative tail, including all central corrections. -/
namespace ACS12.GammaMeasure

open Set

private theorem lowerTailChord {p : ℝ} (hp : 1 ≤ p) (hpP : p ≤ 9 / 5) :
    (6898 / 1000 - 303 / 1000 * p) * (7 / 2 : ℝ) ^ (-p) <
      189 / 100 - 152 / 100 * (p - 1) := by
  let a : ℝ := 6898 / 1000
  let b : ℝ := 303 / 1000
  let l := Real.log (7 / 2)
  let F (x : ℝ) := (a - b * x) * Real.exp (-x * l)
  let G (x : ℝ) := (-b - l * (a - b * x)) * Real.exp (-x * l)
  let H (x : ℝ) := (2 * b * l + l ^ 2 * (a - b * x)) * Real.exp (-x * l)
  have hL : 0 < l := Real.log_pos (by norm_num)
  have hD (x : ℝ) : HasDerivAt F (G x) x := by
    have hx := hasDerivAt_id x
    convert ((hx.const_mul b).const_sub a).mul ((hx.neg.mul_const l).exp) using 1
    simp only [G,Pi.neg_apply,id_eq]
    ring
  have hE (x : ℝ) : HasDerivAt G (H x) x := by
    have hx := hasDerivAt_id x
    convert ((((hx.const_mul b).const_sub a).const_mul l).const_sub (-b)).mul
      ((hx.neg.mul_const l).exp) using 1
    simp only [H,Pi.neg_apply,id_eq]
    ring
  have hConv : ConvexOn ℝ (Icc 1 (9 / 5)) F := by
    apply convexOn_of_deriv2_nonneg (convex_Icc _ _)
    · exact fun x _ => (hD x).continuousAt.continuousWithinAt
    · exact fun x _ => (hD x).differentiableAt.differentiableWithinAt
    · have h : deriv F = G := funext (fun x => (hD x).deriv)
      rw [h]
      exact fun x _ => (hE x).differentiableAt.differentiableWithinAt
    · have h : deriv F = G := funext (fun x => (hD x).deriv)
      intro x hx
      change 0 ≤ deriv (deriv F) x
      rw [h,(hE x).deriv]
      have hax : 0 ≤ a - b * x := by
        unfold a b
        have hU := (interior_subset hx).2
        linarith only [hU]
      unfold H b
      positivity
  have hEq (x : ℝ) : F x = (a - b * x) * (7 / 2 : ℝ) ^ (-x) := by
    unfold F l
    rw [Real.rpow_def_of_pos (by norm_num),mul_comm (Real.log (7 / 2)) (-x)]
  have h₁ : F 1 < 189 / 100 := by
    rw [hEq,Real.rpow_neg_one]
    norm_num [a,b]
  have hP : F (9 / 5) < 674 / 1000 := by
    have h := fifth_rpow_upper (b := 7 / 2) (x := 106 / 1000) (k := 9) (by norm_num) (by norm_num) (by norm_num)
    rw [hEq,show -(9 / 5 : ℝ) = -(9 : ℝ) / 5 by ring]
    norm_num [a,b]
    linarith only [h]
  let t : ℝ := (5 / 4) * (p - 1)
  have ht : 0 ≤ t := mul_nonneg (by norm_num) (sub_nonneg.mpr hp)
  have ht' : 0 ≤ 1 - t := by unfold t; linarith only [hpP]
  have hJ := hConv.2 (show (1 : ℝ) ∈ Icc 1 (9 / 5) by norm_num)
    (show (9 / 5 : ℝ) ∈ Icc 1 (9 / 5) by norm_num) ht' ht (show 1 - t + t = 1 by ring)
  simp only [smul_eq_mul] at hJ
  rw [show (1 - t) * 1 + t * (9 / 5) = p by unfold t; ring] at hJ
  have hStrict : (1 - t) * F 1 + t * F (9 / 5) < (1 - t) * (189 / 100) + t * (674 / 1000) := by
    rcases ht'.eq_or_lt with he | he
    · have ht₀ : 0 < t := by linarith only [he]
      exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left h₁.le ht') (mul_lt_mul_of_pos_left hP ht₀)
    · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left h₁ he) (mul_le_mul_of_nonneg_left hP.le ht)
  rw [hEq] at hJ
  change (a - b * p) * (7 / 2 : ℝ) ^ (-p) < _
  apply (hJ.trans_lt hStrict).trans_le
  unfold t
  ring_nf
  norm_num

theorem lowerNative_tail_third {p δ : ℝ} (hp : 1 ≤ p) (hpP : p ≤ 9 / 5)
    (hd : δ ∈ Icc (0 : ℝ) (1 / 8)) :
    let m := 1 - 2 * δ
    m ^ (p + 2) / (p * (p + 1)) * (∑' j : ℕ, lowerNativeSite 3 p (j + 2 : ℕ) δ) >
      -(189 / 100 - 152 / 100 * (p - 1)) := by
  let m := 1 - 2 * δ
  let h := δ / m
  let Y : ℝ := 7 / 2 + 2 * h
  let N := m ^ (p + 2) / (p * (p + 1))
  let f (k : Fin 5) (j : ℕ) := lowerBaseCoeff k p h * (Y + (j : ℝ)) ^ (-(p + 1 + (k.val : ℝ)))
  let g (j : ℕ) := N * lowerNativeSite 3 p (j + 2 : ℕ) δ
  have hm : 0 < m := by unfold m; linarith only [hd.2]
  have hh : 0 ≤ h := div_nonneg hd.1 hm.le
  have hY : 7 / 2 ≤ Y := by unfold Y; linarith only [hh]
  have hY₁ : 1 ≤ Y := (by norm_num : (1 : ℝ) ≤ 7 / 2).trans hY
  have hp₀ := zero_lt_one.trans_le hp
  have hN : 0 < N := by unfold N; positivity
  have hF (k : Fin 5) : HasSum (f k) (lowerBaseCoeff k p h * shiftedPowerTail (p + 1 + (k.val : ℝ)) Y) := by
    have hk : (0 : ℝ) ≤ (k.val : ℝ) := Nat.cast_nonneg _
    exact (shiftedPowerTail_summable (q := p + 1 + (k.val : ℝ))
      (by linarith only [hp,hk]) hY₁).hasSum.mul_left _
  have hFS := hasSum_sum (s := Finset.univ) (fun k _ => hF k)
  obtain ⟨M,hM,hB⟩ := lowerNativeSite_dominated (k := 3) le_rfl hp
  have hd' : δ ∈ Icc (-(1 / 4) : ℝ) (1 / 4) := ⟨by linarith only [hd.1],by linarith only [hd.2]⟩
  have hD : Summable (fun j : ℕ => lowerNativeSite 3 p (j : ℝ) δ) :=
    Summable.of_norm_bounded ((shiftedPowerTail_summable (q := 2) (x := 1) (by norm_num) le_rfl).mul_left M)
      (fun j => hB j δ hd')
  have hG : Summable g := ((summable_nat_add_iff 2).mpr hD).mul_left N
  have hCmp (j : ℕ) : (∑ k : Fin 5, f k j) ≤ g j := by
    have hj : 2 ≤ ((j + 2 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_add_left 2 j)
    have hd₂ : δ < 1 / 2 := by linarith only [hd.2]
    have hp₂ : p ≤ 2 := hpP.trans (by norm_num)
    have hJ := lowerBaseThird_eq hp hj hd₂
    change N * lowerBaseThird p ((j + 2 : ℕ) : ℝ) δ =
      ∑ k : Fin 5, lowerBaseCoeff k p h * (((j + 2 : ℕ) : ℝ) + 3 / 2 + 2 * h) ^ (-p - 1 - (k.val : ℝ)) at hJ
    have hb : ((j + 2 : ℕ) : ℝ) + 3 / 2 + 2 * h = Y + (j : ℝ) := by push_cast; unfold Y; ring
    simp_rw [hb,show ∀ k : Fin 5, -p - 1 - (k.val : ℝ) = -(p + 1 + (k.val : ℝ)) from fun k => by ring] at hJ
    rw [show (∑ k : Fin 5, f k j) = N * lowerBaseThird p ((j + 2 : ℕ) : ℝ) δ from hJ.symm]
    exact mul_le_mul_of_nonneg_left (lowerNativeSite_third_ge_centralBase hp hp₂ hj hd) hN.le
  have hC := hFS.summable.tsum_le_tsum hCmp hG
  rw [hFS.tsum_eq] at hC
  have hc : 0 ≤ 6898 / 1000 - 303 / 1000 * p := by linarith only [hpP]
  have hy := Real.rpow_le_rpow_of_nonpos (show (0 : ℝ) < 7 / 2 by norm_num) hY (neg_nonpos.mpr hp₀.le)
  have hLower : -(189 / 100 - 152 / 100 * (p - 1)) < -(6898 / 1000 - 303 / 1000 * p) * Y ^ (-p) := by
    have h := mul_le_mul_of_nonneg_left hy hc
    linarith only [lowerTailChord hp hpP,h]
  have hf := (hLower.trans (lowerBaseTail_directed hp hpP hh)).trans_le hC
  change _ < ∑' j : ℕ, N * lowerNativeSite 3 p (j + 2 : ℕ) δ at hf
  rwa [tsum_mul_left] at hf

end ACS12.GammaMeasure

import ACS12.JointLowerBaseTerms
import ACS12.ShiftedPowerTail

/-! Directed Bernoulli price of the five retained central coefficients. -/
namespace ACS12.GammaMeasure

open Finset

private noncomputable def lowerBaseReduced (k : Fin 5) (p h : ℝ) : ℝ :=
  let l := 1 + 2 * h
  let B := 13 / 25 + 27 / 25 * h + 14 / 25 * h ^ 2
  let d := 1 + 26 / 25 * h
  match k.val with
  | 0 => -(8 * h * (p + 2) + 12)
  | 1 => (24 * h * (p + 2) + 24) * l +
      (p + 2) * (4 * B * (p + 3) - 6 * d) + 72 / 25
  | 2 => -((24 * h * (p + 2) + 12) * l ^ 2 +
      (12 * (p + 2) * (B * (p + 3) - d) + 72 / 25) * l)
  | 3 => 8 * h * (p + 2) * l ^ 3 + 6 * (p + 2) * (2 * B * (p + 3) - d) * l ^ 2
  | _ => -4 * B * (p + 2) * (p + 3) * l ^ 3

private theorem lowerBaseCoeff_factor (k : Fin 5) (p h : ℝ) :
    lowerBaseCoeff k p h = (p + (k.val : ℝ)) * lowerBaseReduced k p h := by
  fin_cases k <;> norm_num [lowerBaseCoeff,lowerBaseReduced] <;> ring

private theorem lowerBaseReduced_sign {p h : ℝ} (hp : 1 ≤ p) (hh : 0 ≤ h) :
    lowerBaseReduced 0 p h ≤ 0 ∧ 0 ≤ lowerBaseReduced 1 p h ∧
    lowerBaseReduced 2 p h ≤ 0 ∧ 0 ≤ lowerBaseReduced 3 p h ∧ lowerBaseReduced 4 p h ≤ 0 := by
  let B : ℝ := 13 / 25 + 27 / 25 * h + 14 / 25 * h ^ 2
  let d : ℝ := 1 + 26 / 25 * h
  have hB : 0 ≤ B := by unfold B; positivity
  have h1 : 0 ≤ B * (p + 3) - d := by
    have hm := mul_nonneg hB (sub_nonneg.mpr hp)
    unfold B d at *
    nlinarith only [hm,hh,sq_nonneg h]
  have h2 : 0 ≤ 4 * B * (p + 3) - 6 * d := by
    have hm := mul_nonneg hB (sub_nonneg.mpr hp)
    unfold B d at *
    nlinarith only [hm,hh,sq_nonneg h]
  have h3 : 0 ≤ 2 * B * (p + 3) - d := by
    have hm := mul_nonneg hB (by linarith only [hp] : 0 ≤ p + 3)
    linarith only [h1,hm]
  have hp₀ : 0 < p := zero_lt_one.trans_le hp
  refine ⟨?_,?_,?_,?_,?_⟩
  · change -(8 * h * (p + 2) + 12) ≤ 0
    exact neg_nonpos.mpr (by positivity)
  · change 0 ≤ (24 * h * (p + 2) + 24) * (1 + 2 * h) + (p + 2) * (4 * B * (p + 3) - 6 * d) + 72 / 25
    positivity
  · change -((24 * h * (p + 2) + 12) * (1 + 2 * h) ^ 2 +
      (12 * (p + 2) * (B * (p + 3) - d) + 72 / 25) * (1 + 2 * h)) ≤ 0
    exact neg_nonpos.mpr (by positivity)
  · change 0 ≤ 8 * h * (p + 2) * (1 + 2 * h) ^ 3 +
      6 * (p + 2) * (2 * B * (p + 3) - d) * (1 + 2 * h) ^ 2
    positivity
  · change -4 * B * (p + 2) * (p + 3) * (1 + 2 * h) ^ 3 ≤ 0
    exact nonpos_of_neg_nonneg (by rw [neg_mul,neg_mul,neg_mul,neg_mul,neg_neg]; positivity)

private noncomputable def lowerBaseDirectedTerm (k : Fin 5) (p h : ℝ) : ℝ :=
  let Y := 7 / 2 + 2 * h
  let j := k.val
  let q := p + 1 + (j : ℝ)
  let C := lowerBaseCoeff k p h
  lowerBaseReduced k p h * Y ^ (7 - j) + C * (Y ^ (6 - j) / 2 + q * Y ^ (5 - j) / 12) -
    (if j = 1 ∨ j = 3 then C * q * (q + 1) * (q + 2) * Y ^ (3 - j) / 720 else 0)

private noncomputable def lowerBaseDirected (p h : ℝ) : ℝ :=
  (6898 / 1000 - 303 / 1000 * p) * (7 / 2 + 2 * h) ^ 7 +
    ∑ k : Fin 5, lowerBaseDirectedTerm k p h

/- The polynomial uses the Bernstein basis in the exponent variable and
ordinary powers in the displacement. Its coefficients are exact integers
with a common denominator. The identity below checks the certificate. -/
private noncomputable def lowerTailCertificate (u h : ℝ) : ℝ :=
  (
    u ^ 0 * (1 - u) ^ 6 * (97327665703125 + 464808017812500 * h ^ 1 +
      1825211216250000 * h ^ 2 + 2906102385000000 * h ^ 3 +
      2241706140000000 * h ^ 4 + 909540720000000 * h ^ 5 +
      186137280000000 * h ^ 6 + 15194880000000 * h ^ 7) +
    u ^ 1 * (1 - u) ^ 5 * (534729030206250 + 2368617729225000 * h ^ 1 +
      10285240456500000 * h ^ 2 + 16966809992400000 * h ^ 3 +
      13268647300800000 * h ^ 4 + 5415419001600000 * h ^ 5 +
      1109982182400000 * h ^ 6 + 90610790400000 * h ^ 7) +
    u ^ 2 * (1 - u) ^ 4 * (1234657488044375 + 4907878812217500 * h ^ 1 +
      24082912424670000 * h ^ 2 + 41262060130040000 * h ^ 3 +
      32723960763680000 * h ^ 4 + 13435532496000000 * h ^ 5 +
      2757851712000000 * h ^ 6 + 225130752000000 * h ^ 7) +
    u ^ 3 * (1 - u) ^ 3 * (1539840263505500 + 5245058539174000 * h ^ 1 +
      29984683377912000 * h ^ 2 + 53500740179936000 * h ^ 3 +
      43042566118528000 * h ^ 4 + 17778754368000000 * h ^ 5 +
      3654330624000000 * h ^ 6 + 298312704000000 * h ^ 7) +
    u ^ 4 * (1 - u) ^ 2 * (1098962755495475 + 3001831405964300 * h ^ 1 +
      20930347479548400 * h ^ 2 + 39005949162507200 * h ^ 3 +
      31844653305657600 * h ^ 4 + 13234147344000000 * h ^ 5 +
      2723644224000000 * h ^ 6 + 222338304000000 * h ^ 7) +
    u ^ 5 * (1 - u) ^ 1 * (427350301303770 + 845737870009320 * h ^ 1 +
      7763316491719200 * h ^ 2 + 15160448915433600 * h ^ 3 +
      12564441622064640 * h ^ 4 + 5254310880000000 * h ^ 5 +
      1082616192000000 * h ^ 6 + 88376832000000 * h ^ 7) +
    u ^ 6 * (1 - u) ^ 0 * (70971477892353 + 84895116244164 * h ^ 1 +
      1194768027587664 * h ^ 2 + 2453886575555904 * h ^ 3 +
      2065334597174016 * h ^ 4 + 869263689600000 * h ^ 5 +
      179295782400000 * h ^ 6 + 14636390400000 * h ^ 7)) / 18000000000

set_option maxHeartbeats 2500000 in
private theorem lowerBaseDirected_eq (u h : ℝ) :
    lowerBaseDirected (1 + 4 / 5 * u) h = 1 + lowerTailCertificate u h := by
  norm_num [lowerBaseDirected,lowerBaseDirectedTerm,Fin.sum_univ_succ,Fin.val_succ,
    lowerBaseReduced,lowerBaseCoeff,lowerTailCertificate]
  ring

private theorem lowerBaseDirected_pos {p h : ℝ} (hp : 1 ≤ p) (hpP : p ≤ 9 / 5) (hh : 0 ≤ h) :
    0 < lowerBaseDirected p h := by
  let u := (p - 1) * (5 / 4)
  have hu : 0 ≤ u := mul_nonneg (sub_nonneg.mpr hp) (by norm_num)
  have hU : 0 ≤ 1 - u := by unfold u; linarith only [hpP]
  have he : p = 1 + 4 / 5 * u := by unfold u; ring
  rw [he,lowerBaseDirected_eq]
  have hC : 0 ≤ lowerTailCertificate u h := by unfold lowerTailCertificate; positivity
  linarith only [hC]

private theorem lowerBaseDirectedTerm_le {p h : ℝ} (hp : 1 ≤ p) (hh : 0 ≤ h) (k : Fin 5) :
    let Y := 7 / 2 + 2 * h
    (Y ^ (-p) / Y ^ 7) * lowerBaseDirectedTerm k p h ≤
      lowerBaseCoeff k p h * shiftedPowerTail (p + 1 + (k.val : ℝ)) Y := by
  let Y : ℝ := 7 / 2 + 2 * h
  let j := k.val
  let q : ℝ := p + 1 + (j : ℝ)
  let C := lowerBaseCoeff k p h
  let L := lowerBaseReduced k p h
  let W := Y ^ (-p)
  have hj : j < 5 := k.isLt
  have hY : 1 ≤ Y := by unfold Y; linarith only [hh]
  have hY₀ := zero_lt_one.trans_le hY
  have hq : 1 < q := by unfold q; have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith only [hp,this]
  have hpj : 0 < p + (j : ℝ) := add_pos_of_pos_of_nonneg (zero_lt_one.trans_le hp) (Nat.cast_nonneg j)
  have hC : C = (p + (j : ℝ)) * L := lowerBaseCoeff_factor k p h
  have hP {i : ℕ} (hi : i ≤ 7) : W / Y ^ 7 * Y ^ (7 - i) = W / Y ^ i := by
    have hpow : Y ^ 7 = Y ^ i * Y ^ (7 - i) := by
      rw [← pow_add,Nat.add_sub_of_le hi]
    rw [hpow]
    field_simp [hY₀.ne']
  have h₀ : Y ^ (1 - q) = W / Y ^ j := by
    rw [show 1 - q = -p - (j : ℝ) by unfold q; ring,Real.rpow_sub_natCast hY₀.ne']
  have h₁ : Y ^ (-q) = W / Y ^ (j + 1) := by
    rw [show -q = -p - ((j + 1 : ℕ) : ℝ) by unfold q; push_cast; ring,Real.rpow_sub_natCast hY₀.ne']
  have h₂ : Y ^ (-q - 1) = W / Y ^ (j + 2) := by
    rw [show -q - 1 = -p - ((j + 2 : ℕ) : ℝ) by unfold q; push_cast; ring,Real.rpow_sub_natCast hY₀.ne']
  let B := Y ^ (1 - q) / (q - 1) + Y ^ (-q) / 2 + q * Y ^ (-q - 1) / 12
  let T := q * (q + 1) * (q + 2) * Y ^ (-q - 3) / 720
  have hB : W / Y ^ 7 * (L * Y ^ (7 - j) + C * (Y ^ (6 - j) / 2 + q * Y ^ (5 - j) / 12)) =
      C * B := by
    rw [show 6 - j = 7 - (j + 1) by omega,show 5 - j = 7 - (j + 2) by omega]
    calc
      _ = L * (W / Y ^ 7 * Y ^ (7 - j)) + C * ((W / Y ^ 7 * Y ^ (7 - (j + 1))) / 2 +
          q * (W / Y ^ 7 * Y ^ (7 - (j + 2))) / 12) := by ring
      _ = _ := by
        rw [hP (by omega : j ≤ 7),hP (by omega : j + 1 ≤ 7),hP (by omega : j + 2 ≤ 7)]
        unfold B
        rw [h₀,h₁,h₂,show q - 1 = p + (j : ℝ) by unfold q; ring,hC]
        field_simp [hpj.ne']
        ring
  have hI := shiftedPowerTail_bernoulli hq hY
  change B - T < shiftedPowerTail q Y ∧ shiftedPowerTail q Y < B at hI
  obtain ⟨hL₀,hL₁,hL₂,hL₃,hL₄⟩ := lowerBaseReduced_sign hp hh
  change W / Y ^ 7 * (_ - (if j = 1 ∨ j = 3 then _ else 0)) ≤ C * shiftedPowerTail q Y
  by_cases hs : j = 1 ∨ j = 3
  · have hj₃ : j ≤ 3 := hs.elim (fun he => by omega) (fun he => by omega)
    have hL : 0 ≤ L := by
      rcases hs with he | he
      · have hke : k = 1 := Fin.ext he
        simpa only [L,hke] using hL₁
      · have hke : k = 3 := Fin.ext he
        simpa only [L,hke] using hL₃
    have hCp : 0 ≤ C := hC.symm ▸ mul_nonneg hpj.le hL
    have h₃ : Y ^ (-q - 3) = W / Y ^ (j + 4) := by
      rw [show -q - 3 = -p - ((j + 4 : ℕ) : ℝ) by unfold q; push_cast; ring,Real.rpow_sub_natCast hY₀.ne']
    have hT : W / Y ^ 7 * (C * q * (q + 1) * (q + 2) * Y ^ (3 - j) / 720) = C * T := by
      unfold T
      rw [h₃,show 3 - j = 7 - (j + 4) by omega,← hP (by omega : j + 4 ≤ 7)]
      ring
    rw [if_pos hs,mul_sub,hB,hT,← mul_sub]
    exact mul_le_mul_of_nonneg_left hI.1.le hCp
  · have hL : L ≤ 0 := by
      fin_cases k <;> first
      | exact hL₀
      | exact hL₂
      | exact hL₄
      | exact False.elim (hs (by decide))
    have hCn : C ≤ 0 := hC.symm ▸ mul_nonpos_of_nonneg_of_nonpos hpj.le hL
    rw [if_neg hs,sub_zero,hB]
    exact mul_le_mul_of_nonpos_left hI.2.le hCn

theorem lowerBaseTail_directed {p h : ℝ} (hp : 1 ≤ p) (hpP : p ≤ 9 / 5) (hh : 0 ≤ h) :
    let Y := 7 / 2 + 2 * h;
    -(6898 / 1000 - 303 / 1000 * p) * Y ^ (-p) <
      (∑ k : Fin 5, lowerBaseCoeff k p h * shiftedPowerTail (p + 1 + (k.val : ℝ)) Y) := by
  let Y : ℝ := 7 / 2 + 2 * h
  have hY : 0 < Y := by unfold Y; positivity
  let A := Y ^ (-p) / Y ^ 7
  have hA : 0 < A := by unfold A; positivity
  have hs := sum_le_sum (s := univ) (fun k _ => lowerBaseDirectedTerm_le hp hh k)
  change (∑ k : Fin 5, A * lowerBaseDirectedTerm k p h) ≤ _ at hs
  rw [← mul_sum] at hs
  have hd := mul_pos hA (lowerBaseDirected_pos hp hpP hh)
  change 0 < A * ((6898 / 1000 - 303 / 1000 * p) * Y ^ 7 +
    ∑ k : Fin 5, lowerBaseDirectedTerm k p h) at hd
  rw [mul_add,show A * ((6898 / 1000 - 303 / 1000 * p) * Y ^ 7) =
    (6898 / 1000 - 303 / 1000 * p) * Y ^ (-p) by unfold A; field_simp [hY.ne']] at hd
  change _ < _
  linarith only [hs,hd]

end ACS12.GammaMeasure

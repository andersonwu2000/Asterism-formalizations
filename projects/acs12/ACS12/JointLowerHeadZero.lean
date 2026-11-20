import ACS12.JointLowerFiniteAlgebra
import ACS12.JointLowerTailComplete

/-! The complete first native atom and its known cubic contribution. -/
namespace ACS12.GammaMeasure

open Set

private theorem log_fifteen_eighth_lower : (3 / 5 : ℝ) < Real.log (15 / 8) := by
  have h := Real.hasSum_log_one_add (a := (7 / 8 : ℝ)) (by norm_num)
  have hS := h.summable.sum_le_tsum (Finset.range 3) (fun _ _ => by positivity)
  rw [h.tsum_eq] at hS
  norm_num [Finset.sum_range_succ] at hS
  exact (by norm_num : (3 / 5 : ℝ) < _).trans_le hS

private theorem lowerHead₀Right_nonneg {p v : ℝ} (hp : 1 ≤ p) (hpP : p ≤ 9 / 5) (hv : 15 / 8 ≤ v) :
    0 ≤ lowerHead₀Right p v := by
  let t := p - 1
  let c : ℝ := 15 / 8
  let w := v - c
  let a := lowerNativeAlpha p
  let A := (p - 1) * (2 + 66 * p / 25)
  let B := (p + 2) * (3 + 108 * p / 25)
  let C := (54 / 25) * (p + 2) * (p + 3)
  let E := 1 + (3 / 5) * t + (9 / 50) * t ^ 2
  let L := 1 + (3 / 5) * t
  have hp₀ := zero_lt_one.trans_le hp
  have hp₁ : 0 < p + 1 := by positivity
  have ht : 0 ≤ t := sub_nonneg.mpr hp
  have hw : 0 ≤ w := sub_nonneg.mpr hv
  have hA : 0 ≤ A := mul_nonneg ht (by positivity)
  have ha : 0 ≤ a := (lowerNativeAlpha_bounds hp hpP).1
  have hv₀ : 0 < v := (by norm_num : (0 : ℝ) < 15 / 8).trans_le hv
  have hE : E ≤ Real.exp (t * Real.log v) := by
    have h := log_fifteen_eighth_lower.trans_le (Real.log_le_log (by norm_num) hv)
    calc
      _ ≤ Real.exp ((3 / 5) * t) := by
        convert Real.quadratic_le_exp_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 5) ht) using 1
        unfold E
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by simpa only [mul_comm] using mul_le_mul_of_nonneg_right h.le ht)
  have hv₅ : c ^ 5 + 5 * c ^ 4 * w ≤ v ^ 5 := by
    have h : 0 ≤ w ^ 2 * (10 * c ^ 3 + 10 * c ^ 2 * w + 5 * c * w ^ 2 + w ^ 3) := by
      have : 0 < c := by norm_num [c]
      positivity
    have he : v = c + w := by unfold w; ring
    rw [he]
    nlinarith only [h]
  have hv₃ : c ^ 3 + 3 * c ^ 2 * w ≤ v ^ 3 := by
    have h : 0 ≤ w ^ 2 * (3 * c + w) := by
      have : 0 < c := by norm_num [c]
      positivity
    rw [show v = c + w by unfold w; ring]
    nlinarith only [h]
  have hv₂ : c ^ 2 + 2 * c * w ≤ v ^ 2 := by
    rw [show v = c + w by unfold w; ring]
    nlinarith only [sq_nonneg w]
  have hEL : L ≤ E := by unfold L E; nlinarith only [sq_nonneg t]
  have hE₀ : 0 ≤ E := by unfold E; positivity
  have hPwr : c ^ 5 * E + 5 * c ^ 4 * w * L ≤ v ^ (p + 4) := by
    have hc : 0 < c := by norm_num [c]
    have h₁ := mul_le_mul_of_nonneg_right hv₅ hE₀
    have h₂ := mul_le_mul_of_nonneg_left hEL (show 0 ≤ 5 * c ^ 4 * w by positivity)
    have h₃ := mul_le_mul_of_nonneg_left hE (pow_nonneg hv₀.le 5)
    rw [show p + 4 = ((5 : ℕ) : ℝ) + t by unfold t; push_cast; ring,Real.rpow_add hv₀,
      Real.rpow_natCast,Real.rpow_def_of_pos hv₀,mul_comm (Real.log v) t]
    nlinarith only [h₁,h₂,h₃]
  let P := (36 / 25) * c ^ 5 * E + (p + 1) * (a * c ^ 3 + A * c ^ 2 - B * c + C)
  let D := (36 / 25) * 5 * c ^ 4 * L + (p + 1) * (3 * a * c ^ 2 + 2 * A * c - B)
  have hAC : (p + 1) * a = (12 / 25) * p * (p - 1) * (2 - p) := by
    unfold a lowerNativeAlpha
    field_simp [hp₁.ne']
  have hD : 0 ≤ D := by
    have he : D = (207 / 400) * t ^ 3 + (207 / 25) * t ^ 2 + (786843 / 25600) * t + 1153773 / 25600 := by
      unfold D
      rw [show (p + 1) * (3 * a * c ^ 2 + 2 * A * c - B) =
        3 * ((p + 1) * a) * c ^ 2 + (p + 1) * (2 * A * c - B) by ring,hAC]
      unfold L c A B t
      ring
    rw [he]
    positivity
  have hP : 0 ≤ P := by
    let z := (5 / 4) * t
    have hz : 0 ≤ z := mul_nonneg (by norm_num) ht
    have hz₁ : 0 ≤ 1 - z := by unfold z t; linarith only [hpP]
    have he : P = (585927 / 204800) * (1 - z) ^ 3 + (4485357 / 1024000) * z * (1 - z) ^ 2 +
        (20886957 / 5120000) * z ^ 2 * (1 - z) + (67864167 / 25600000) * z ^ 3 := by
      unfold P
      rw [show (p + 1) * (a * c ^ 3 + A * c ^ 2 - B * c + C) =
        ((p + 1) * a) * c ^ 3 + (p + 1) * (A * c ^ 2 - B * c + C) by ring,hAC]
      unfold E c A B C z t
      ring
    rw [he]
    positivity
  apply nonneg_of_mul_nonneg_right _ hp₁
  have h₁ := mul_le_mul_of_nonneg_left hPwr (show (0 : ℝ) ≤ 36 / 25 by norm_num)
  have h₂ := mul_le_mul_of_nonneg_left hv₃ (mul_nonneg hp₁.le ha)
  have h₃ := mul_le_mul_of_nonneg_left hv₂ (mul_nonneg hp₁.le hA)
  have h₄ := add_nonneg hP (mul_nonneg hD hw)
  have hM : (p + 1) * lowerHead₀Right p v =
      (36 / 25) * v ^ (p + 4) + (p + 1) * (a * v ^ 3 + A * v ^ 2 - B * v + C) := by
    unfold lowerHead₀Right a A B C
    field_simp [hp₁.ne']
    ring
  rw [hM]
  have hV : v = c + w := by unfold w; ring
  let K := (p + 1) * (C - B * v)
  have hLeft : P + D * w =
      (36 / 25) * (c ^ 5 * E + 5 * c ^ 4 * w * L) +
      ((p + 1) * a) * (c ^ 3 + 3 * c ^ 2 * w) + ((p + 1) * A) * (c ^ 2 + 2 * c * w) + K := by
    unfold P D K
    rw [hV]
    ring
  have hRight : (36 / 25) * v ^ (p + 4) + (p + 1) * (a * v ^ 3 + A * v ^ 2 - B * v + C) =
      (36 / 25) * v ^ (p + 4) + ((p + 1) * a) * v ^ 3 + ((p + 1) * A) * v ^ 2 + K := by
    unfold K
    ring
  rw [hLeft] at h₄
  rw [hRight]
  exact h₄.trans (add_le_add_left (add_le_add (add_le_add h₁ h₂) h₃) K)

private theorem lowerNativeScale_bounds {p d : ℝ} (hp : 1 ≤ p) (hpP : p ≤ 9 / 5)
    (hd : d ∈ Icc (0 : ℝ) (1 / 8)) :
    let m := 1 - 2 * d
    let u := 1 - d
    8 / 13 ≤ m ^ (p + 2) * u ^ (-p - 3) ∧ m ^ (p + 2) * u ^ (-p - 3) ≤ 1 := by
  let m := 1 - 2 * d
  let u := 1 - d
  have hm : 0 < m := by unfold m; linarith only [hd.2]
  have hu : 0 < u := by unfold u; linarith only [hd.2]
  have hu₁ : u ≤ 1 := by unfold u; linarith only [hd.1]
  have hmu : m ≤ u := by unfold m u; linarith only [hd.1]
  have hM : m ^ (p + 2) * u ^ (-p - 3) = (m / u) ^ (p + 2) / u := by
    rw [Real.div_rpow hm.le hu.le,show -p - 3 = -(p + 2) - 1 by ring,Real.rpow_sub_one hu.ne',
      Real.rpow_neg hu.le]
    ring
  have hx : 0 < m / u := div_pos hm hu
  have hx₁ : m / u ≤ 1 := (div_le_one hu).mpr hmu
  have h₁ := Real.rpow_le_rpow_of_exponent_ge hx hx₁ (show p + 2 ≤ 4 by linarith only [hpP])
  have h₂ := Real.rpow_le_rpow_of_exponent_ge hx hx₁ (show 3 ≤ p + 2 by linarith only [hp])
  have hu₂ : m / u ≤ u := by
    apply (div_le_iff₀ hu).mpr
    unfold m u
    nlinarith only [sq_nonneg d]
  have hUp : (m / u) ^ (p + 2) / u ≤ 1 := by
    apply (div_le_one hu).mpr
    have h := pow_le_pow_left₀ hx.le hu₂ 3
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,Real.rpow_natCast] at h₂
    exact h₂.trans (h.trans (by
      have h' := pow_le_one₀ hu.le hu₁ (n := 2)
      simpa only [← pow_succ'] using mul_le_of_le_one_right hu.le h'))
  let F (x : ℝ) := (1 - 2 * x) ^ 4 / (1 - x) ^ 5
  have hD (x : ℝ) (hx : x ∈ Icc (0 : ℝ) (1 / 8)) :
      HasDerivAt F ((1 - 2 * x) ^ 3 * (-3 - 2 * x) / (1 - x) ^ 6) x := by
    have hU : 0 < 1 - x := by linarith only [hx.2]
    have hx' := (hasDerivAt_id x).const_sub 1
    have hM' := ((hasDerivAt_id x).const_mul 2).const_sub 1
    convert (hM'.pow 4).div (hx'.pow 5) (pow_ne_zero 5 hU.ne') using 1
    simp only [id_eq,mul_one,Pi.pow_apply]
    field_simp [hU.ne']
    ring
  have hAnti : AntitoneOn F (Icc 0 (1 / 8)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · exact fun x hx => (hD x hx).continuousAt.continuousWithinAt
    · exact fun x hx => (hD x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hD x (interior_subset hx)).deriv]
      have hx' := interior_subset hx
      have hB : 0 ≤ (1 - 2 * x) ^ 3 := pow_nonneg (by linarith only [hx'.2]) _
      have hC : -3 - 2 * x ≤ 0 := by linarith only [hx'.1]
      exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hB hC) (pow_nonneg (by linarith only [hx'.2]) _)
  have hEnd : (8 / 13 : ℝ) ≤ F (1 / 8) := by norm_num [F]
  have hDown : 8 / 13 ≤ (m / u) ^ (p + 2) / u := by
    have hh := hEnd.trans (hAnti hd (by norm_num) hd.2)
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,Real.rpow_natCast] at h₁
    apply hh.trans
    have he : F d = (m / u) ^ 4 / u := by
      change m ^ 4 / u ^ 5 = _
      rw [div_pow,div_div,← pow_succ]
    rw [he]
    exact div_le_div_of_nonneg_right h₁ hu.le
  change 8 / 13 ≤ m ^ (p + 2) * u ^ (-p - 3) ∧ m ^ (p + 2) * u ^ (-p - 3) ≤ 1
  rw [hM]
  exact ⟨hDown,hUp⟩

theorem lowerNative_head_zero_third {p d : ℝ} (hp : 1 ≤ p) (hpP : p ≤ 9 / 5)
    (hd : d ∈ Icc (0 : ℝ) (1 / 8)) :
    let m := 1 - 2 * d
    (7 / 25) * p ^ 2 - (71 / 25) * p + 4 - 3 / 40 - (5 / 13) * (9 / 5) * (9 / 5 - p) ≤
      m ^ (p + 2) / (p * (p + 1)) * ((36 / 25) * p + lowerNativeSite 3 p 0 d) := by
  let m := 1 - 2 * d
  let u := 1 - d
  let v := u + 1
  let Q := m ^ (p + 2) * u ^ (-p - 3)
  let B := lowerHead₀Left p 1
  have hm : 0 < m := by unfold m; linarith only [hd.2]
  have hu : 0 < u := by unfold u; linarith only [hd.2]
  have hu₁ : u ≤ 1 := by unfold u; linarith only [hd.1]
  have hv : 15 / 8 ≤ v := by unfold v u; linarith only [hd.2]
  have hv₀ : 0 < v := (by norm_num : (0 : ℝ) < 15 / 8).trans_le hv
  obtain ⟨hQ,hQ₁⟩ := lowerNativeScale_bounds hp hpP hd
  change 8 / 13 ≤ Q at hQ
  change Q ≤ 1 at hQ₁
  have hQ₀ : 0 ≤ Q := (by norm_num : (0 : ℝ) ≤ 8 / 13).trans hQ
  have hAlpha := lowerNativeAlpha_bounds hp hpP
  have hB : B ≤ lowerHead₀Left p u := by
    have h₁ := mul_le_mul_of_nonneg_left (pow_le_one₀ hu.le hu₁ (n := 2)) hAlpha.1
    have h₂ := mul_le_mul_of_nonpos_left hu₁
      (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hp) (by linarith only [hpP] : 4 * p / 5 - 2 ≤ 0))
    unfold B lowerHead₀Left
    norm_num
    linarith only [h₁,h₂]
  have hB₂ : B ≤ (9 / 5) * (9 / 5 - p) := by
    have h := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hp) (by linarith only [hpP] : 7 * p - 19 ≤ 0)
    unfold B lowerHead₀Left
    norm_num
    nlinarith only [h,hAlpha.1]
  have hB₀ : (7 / 25) * p ^ 2 - (71 / 25) * p + 4 - 3 / 40 ≤ B := by
    unfold B lowerHead₀Left
    norm_num
    nlinarith only [hAlpha.2]
  have hPaid : B - (5 / 13) * (9 / 5) * (9 / 5 - p) ≤ Q * B := by
    by_cases h : 0 ≤ B
    · have he := mul_le_mul_of_nonneg_right hQ h
      linarith only [he,hB₂]
    · have he := mul_le_mul_of_nonpos_right hQ₁ (le_of_not_ge h)
      linarith only [he,hpP]
  have hR : 0 ≤ v ^ (-p - 4) * lowerHead₀Right p v :=
    mul_nonneg (Real.rpow_nonneg hv₀.le _) (lowerHead₀Right_nonneg hp hpP hv)
  have hEq := lowerNativeHead_zero_eq hp (show d < 1 / 2 by linarith only [hd.2])
  change ((36 / 25) * p + lowerNativeSite 3 p 0 d) / (p * (p + 1)) =
    u ^ (-p - 3) * lowerHead₀Left p u + v ^ (-p - 4) * lowerHead₀Right p v at hEq
  change _ ≤ m ^ (p + 2) / (p * (p + 1)) * ((36 / 25) * p + lowerNativeSite 3 p 0 d)
  have hN : 0 ≤ m ^ (p + 2) := Real.rpow_nonneg hm.le _
  have hLeft := mul_le_mul_of_nonneg_left hB hQ₀
  have hRight := mul_nonneg hN hR
  rw [show m ^ (p + 2) / (p * (p + 1)) * ((36 / 25) * p + lowerNativeSite 3 p 0 d) =
    m ^ (p + 2) * (((36 / 25) * p + lowerNativeSite 3 p 0 d) / (p * (p + 1))) by ring,hEq]
  change _ ≤ m ^ (p + 2) * (u ^ (-p - 3) * lowerHead₀Left p u + v ^ (-p - 4) * lowerHead₀Right p v)
  unfold Q at hPaid hLeft
  nlinarith only [hB₀,hPaid,hLeft,hRight]

end ACS12.GammaMeasure

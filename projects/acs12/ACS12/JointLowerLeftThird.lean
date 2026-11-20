import ACS12.JointLowerSourceIdentity

/-! The actual signed left-source pair has positive third response on the lower diagonal. -/
namespace ACS12.GammaMeasure

open Set MeasureTheory

private theorem leftResponse_endpoint_power : (2 / 15 : ℝ) < (3 / 2 : ℝ) ^ (-(24 / 5) : ℝ) := by
  have hb : 0 < (3 / 2 : ℝ) := by norm_num
  have hv : (3 / 2 : ℝ) ^ (24 / 5 : ℝ) < 15 / 2 := by
    apply lt_of_pow_lt_pow_left₀ 5 (by norm_num)
    rw [← Real.rpow_mul_natCast hb.le,
      show (24 / 5 : ℝ) * ↑(5 : ℕ) = ↑(24 : ℕ) by norm_num,Real.rpow_natCast]
    norm_num
  rw [Real.rpow_neg hb.le,lt_inv_comm₀ (by norm_num) (Real.rpow_pos_of_pos hb _)]
  norm_num
  exact hv

theorem lowerLeftPair_response_pos {q r : ℝ} (hq : 4 ≤ q) (hQ : q ≤ 24 / 5)
    (hr : 0 ≤ r) (hR : r ≤ 1 / 2) :
    0 < q * r - 6 + 27 * (1 + r) ^ (-q) := by
  let b : ℝ := 3 / 2
  have hb : 0 < b := by norm_num [b]
  have hr₁ : 0 < 1 + r := by positivity
  have hQ₀ : 0 ≤ 24 / 5 - q := sub_nonneg.mpr hQ
  have hLog : 1 / 3 ≤ Real.log b := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2 / 3)
    rw [show (2 / 3 : ℝ) = b⁻¹ by norm_num [b],Real.log_inv] at h
    linarith only [h]
  have hExp : 1 + (24 / 5 - q) / 3 ≤ Real.exp (Real.log b * (24 / 5 - q)) := by
    have h := mul_le_mul_of_nonneg_right hLog hQ₀
    linarith only [Real.add_one_le_exp (Real.log b * (24 / 5 - q)),h]
  have hB : (2 / 15) * (1 + (24 / 5 - q) / 3) < b ^ (-q) := by
    rw [show -q = -(24 / 5) + (24 / 5 - q) by ring,Real.rpow_add hb,
      Real.rpow_def_of_pos hb (24 / 5 - q)]
    exact mul_lt_mul_of_lt_of_le_of_nonneg_of_pos leftResponse_endpoint_power hExp
      (by linarith only [hQ₀]) (Real.exp_pos _)
  have hB₀ : 2 / 15 < b ^ (-q) := by
    exact (by nlinarith only [hQ₀] : (2 / 15 : ℝ) ≤ (2 / 15) * (1 + (24 / 5 - q) / 3)).trans_lt hB
  have hRat : 0 < (1 + r) / b := div_pos hr₁ hb
  have hRatL := Real.log_le_sub_one_of_pos hRat
  rw [Real.log_div hr₁.ne' hb.ne'] at hRatL
  have hLog' : (2 / 3) * (1 / 2 - r) ≤ Real.log b - Real.log (1 + r) := by
    have hE : (1 + r) / b - 1 = -(2 / 3) * (1 / 2 - r) := by norm_num [b]; ring
    rw [hE] at hRatL
    linarith only [hRatL]
  have hq₀ : 0 ≤ q := by linarith only [hq]
  have hProd : b ^ (-q) * (1 + (2 / 3) * (1 / 2 - r) * q) ≤ (1 + r) ^ (-q) := by
    rw [Real.rpow_def_of_pos hb,Real.rpow_def_of_pos hr₁,
      show Real.log (1 + r) * -q = Real.log b * -q + (Real.log b - Real.log (1 + r)) * q by ring,
      Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    linarith only [mul_le_mul_of_nonneg_right hLog' hq₀,
      Real.add_one_le_exp ((Real.log b - Real.log (1 + r)) * q)]
  have hK : 0 ≤ (1 / 2 - r) * q := mul_nonneg (sub_nonneg.mpr hR) hq₀
  have hN := mul_le_mul_of_nonneg_right hB₀.le hK
  nlinarith only [hB,hProd,hN,hK,hQ]

private theorem affinePower_deriv (a b r δ : ℝ) (h : 0 < a - b * δ) :
    HasDerivAt (fun x => (a - b * x) ^ r) (-b * r * (a - b * δ) ^ (r - 1)) δ := by
  simpa only [id_eq,mul_one,mul_neg,neg_mul] using
    (((hasDerivAt_id δ).const_mul b).const_sub a).rpow_const (p := r) (Or.inl h.ne')

private noncomputable def leftPairAtom (k : ℕ) (p j δ : ℝ) : ℝ :=
  let m := 1 - 2 * δ
  let u := 1 - δ
  let x := j + 1 - δ
  let y := j + 2 - 3 * δ
  match k with
  | 0 => purePeanoB p m (j + u) + purePeanoB p u j
  | 1 => p * (p + 1) * m * x ^ (-p - 2) - 2 * p * x ^ (-p - 1) +
      3 * p * y ^ (-p - 1) - p * j ^ (-p - 1)
  | 2 => p * (p + 1) * ((p + 2) * m * x ^ (-p - 3) - 4 * x ^ (-p - 2) +
      9 * y ^ (-p - 2))
  | _ => p * (p + 1) * (p + 2) *
      ((p + 3) * m * x ^ (-p - 4) - 6 * x ^ (-p - 3) + 27 * y ^ (-p - 3))

private theorem leftPairAtom_deriv {k : ℕ} (hk : k < 3) (p j δ : ℝ)
    (hX : 0 < j + 1 - δ) (hY : 0 < j + 2 - 3 * δ) :
    HasDerivAt (leftPairAtom k p j) (leftPairAtom (k + 1) p j δ) δ := by
  have hx (r : ℝ) := affinePower_deriv (j + 1) 1 r δ (by simpa only [one_mul] using hX)
  have hy (r : ℝ) := affinePower_deriv (j + 2) 3 r δ hY
  simp only [one_mul,neg_mul,one_mul] at hx
  have hm := ((hasDerivAt_id δ).const_mul 2).const_sub 1
  have hu := (hasDerivAt_id δ).const_sub 1
  interval_cases k
  · have h := (((hm.const_mul p).mul (hx (-p - 1))).add (hy (-p))).add
      (((hu.const_mul (p * j ^ (-p - 1))).sub_const (j ^ (-p))))
    convert h using 1
    · funext d
      unfold leftPairAtom purePeanoB
      simp only [id_eq,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,show -(p + 1) = -p - 1 by ring]
      rw [show j + (1 - d) + (1 - 2 * d) = j + 2 - 3 * d by ring,
        show j + (1 - d) = j + 1 - d by ring]
      ring
    · simp only [leftPairAtom,id_eq,mul_one,show -p - 1 - 1 = -p - 2 by ring,
        show -p - 1 = -p - 1 by rfl]
      ring
  · have h := (((hm.const_mul (p * (p + 1))).mul (hx (-p - 2))).sub
      ((hx (-p - 1)).const_mul (2 * p))).add ((hy (-p - 1)).const_mul (3 * p))
    convert h.sub_const (p * j ^ (-p - 1)) using 1
    simp only [leftPairAtom,id_eq,mul_one,show -p - 2 - 1 = -p - 3 by ring,show -p - 1 - 1 = -p - 2 by ring]
    ring
  · have h := (((hm.const_mul (p + 2)).mul (hx (-p - 3))).sub
      ((hx (-p - 2)).const_mul 4)).add ((hy (-p - 2)).const_mul 9)
    convert h.const_mul (p * (p + 1)) using 1
    simp only [leftPairAtom,id_eq,mul_one,show -p - 3 - 1 = -p - 4 by ring,show -p - 2 - 1 = -p - 3 by ring]
    ring

private theorem leftPairAtom_third_pos {p j δ : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hj : 1 ≤ j) (hδ : 0 ≤ δ) (hD : δ ≤ 1 / 8) :
    0 < leftPairAtom 3 p j δ := by
  let m := 1 - 2 * δ
  let x := j + 1 - δ
  let y := j + 2 - 3 * δ
  have hX : 0 < x := by unfold x; linarith only [hj,hD]
  have hM : 0 < m := by unfold m; linarith only [hD]
  have hR : m / x ≤ 1 / 2 := (div_le_iff₀ hX).mpr (by unfold m x; linarith only [hj,hδ])
  have hPos := lowerLeftPair_response_pos (q := p + 3) (r := m / x)
    (by linarith only [hp]) (by linarith only [hP]) (div_nonneg hM.le hX.le) hR
  have hY : y = x * (1 + m / x) := by unfold y; field_simp [hX.ne']; unfold x m; ring
  have hYZ : 0 ≤ 1 + m / x := by positivity
  have hE : x ^ (-p - 4) = x ^ (-p - 3) / x := by
    rw [← Real.rpow_sub_one hX.ne']
    congr 1
    ring
  change 0 < p * (p + 1) * (p + 2) *
      ((p + 3) * m * x ^ (-p - 4) - 6 * x ^ (-p - 3) + 27 * y ^ (-p - 3))
  rw [hE,hY,Real.mul_rpow hX.le hYZ]
  rw [show -(p + 3) = -p - 3 by ring] at hPos
  have hp₀ := zero_lt_one.trans_le hp
  have hU := mul_pos (Real.rpow_pos_of_pos hX (-p - 3)) hPos
  have hV := mul_pos (show 0 < p * (p + 1) * (p + 2) by positivity) hU
  convert hV using 1 <;> ring

private theorem leftPeano_norm_le {p v x j : ℝ} (hp : 1 ≤ p) (hP : p ≤ 2)
    (hj : 1 ≤ j) (hX : j ≤ x) (hv : 0 < v) (hV : v ≤ 2) :
    ‖purePeanoB p v x‖ ≤ 4 * j ^ (-2 : ℝ) := by
  have hp₀ := zero_lt_one.trans_le hp
  have hj₀ := zero_lt_one.trans_le hj
  have hx := hj₀.trans_le hX
  have hPos : 0 ≤ purePeanoB p v x := by
    rw [purePeanoB_integral hp₀ hv hx]
    apply mul_nonneg (by positivity)
    apply intervalIntegral.integral_nonneg hv.le
    intro t ht
    exact mul_nonneg (sub_nonneg.mpr ht.2)
      (Real.rpow_nonneg (add_nonneg hx.le ht.1) _)
  have h₁ : purePeanoB p v x ≤ v * p * x ^ (-(p + 1)) := by
    have h := Real.rpow_le_rpow_of_nonpos hx (le_add_of_nonneg_right hv.le) (neg_nonpos.mpr hp₀.le)
    unfold purePeanoB
    linarith only [h]
  have h₂ : x ^ (-(p + 1)) ≤ j ^ (-2 : ℝ) :=
    (Real.rpow_le_rpow_of_nonpos hj₀ hX (by linarith only [hp])).trans
      (Real.rpow_le_rpow_of_exponent_le hj (by linarith only [hp]))
  have h₃ : v * p ≤ 4 := (mul_le_mul hV hP hp₀.le (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by norm_num)
  rw [Real.norm_of_nonneg hPos]
  exact h₁.trans (mul_le_mul h₃ h₂ (Real.rpow_nonneg hx.le _) (by norm_num))

private abbrev leftMotionBand := Ioo (-(1 / 4) : ℝ) (1 / 4)

private theorem leftPairAtom_bound {k : ℕ} (hk : k ≤ 3) {p j δ : ℝ}
    (hp : 1 ≤ p) (hP : p ≤ 2) (hj : 1 ≤ j) (hδ : δ ∈ leftMotionBand) :
    ‖leftPairAtom k p j δ‖ ≤ 1800 * j ^ (-2 : ℝ) := by
  let m := 1 - 2 * δ
  let u := 1 - δ
  let x := j + 1 - δ
  let y := j + 2 - 3 * δ
  let B := j ^ (-2 : ℝ)
  have hp₀ := zero_lt_one.trans_le hp
  have hj₀ := zero_lt_one.trans_le hj
  have hM : 0 < m := by unfold m; linarith only [hδ.2]
  have hM' : m ≤ 2 := by unfold m; linarith only [hδ.1]
  have hU : 0 < u := by unfold u; linarith only [hδ.2]
  have hU' : u ≤ 2 := by unfold u; linarith only [hδ.1]
  have hX : j ≤ x := by unfold x; linarith only [hδ.2]
  have hY : j ≤ y := by unfold y; linarith only [hδ.2]
  have hB : 0 ≤ B := Real.rpow_nonneg hj₀.le _
  have hPow (z r : ℝ) (hz : j ≤ z) (hr : r ≤ -2) : ‖z ^ r‖ ≤ B := by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hj₀.trans_le hz).le _)]
    exact (Real.rpow_le_rpow_of_nonpos hj₀ hz (hr.trans (by norm_num))).trans
      (Real.rpow_le_rpow_of_exponent_le hj hr)
  have hx (k : ℝ) (hk : 1 ≤ k) : ‖x ^ (-p - k)‖ ≤ B := hPow _ _ hX (by linarith only [hp,hk])
  have hy (k : ℝ) (hk : 1 ≤ k) : ‖y ^ (-p - k)‖ ≤ B := hPow _ _ hY (by linarith only [hp,hk])
  have hj' : ‖j ^ (-p - 1)‖ ≤ B := hPow _ _ le_rfl (by linarith only [hp])
  have hF : p * (p + 1) ≤ 6 := (mul_le_mul hP (by linarith only [hP] : p + 1 ≤ 3)
    (by positivity) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by norm_num)
  have hG : p * (p + 1) * (p + 2) ≤ 24 :=
    (mul_le_mul hF (by linarith only [hP] : p + 2 ≤ 4) (by positivity)
      (by norm_num : (0 : ℝ) ≤ 6)).trans_eq (by norm_num)
  have hT : p * (p + 1) * m ≤ 12 := (mul_le_mul hF hM' hM.le (by norm_num : (0 : ℝ) ≤ 6)).trans_eq (by norm_num)
  have hCoeff (a b v : ℝ) (ha : 0 ≤ a) (hA : a ≤ b) (hv : ‖v‖ ≤ B) :
      ‖a * v‖ ≤ b * B := by
    rw [norm_mul,Real.norm_of_nonneg ha]
    exact mul_le_mul hA hv (norm_nonneg _) (ha.trans hA)
  have hMix (a b c X Y Z : ℝ) (hX : ‖X‖ ≤ a) (hY : ‖Y‖ ≤ b) (hZ : ‖Z‖ ≤ c) :
      ‖X - Y + Z‖ ≤ a + b + c :=
    (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add hX hY)) hZ)
  interval_cases k
  · change ‖purePeanoB p m (j + u) + purePeanoB p u j‖ ≤ 1800 * B
    have h₁ := leftPeano_norm_le hp hP hj (le_add_of_nonneg_right hU.le) hM hM'
    have h₂ := leftPeano_norm_le hp hP hj (le_refl j) hU hU'
    have h := (norm_add_le _ _).trans (add_le_add h₁ h₂)
    exact h.trans (by linarith only [hB])
  · change ‖p * (p + 1) * m * x ^ (-p - 2) - 2 * p * x ^ (-p - 1) +
          3 * p * y ^ (-p - 1) - p * j ^ (-p - 1)‖ ≤ 1800 * B
    have h₁ := hCoeff _ 12 _ (by positivity) hT (hx 2 (by norm_num))
    have h₂ := hCoeff (2 * p) 4 _ (by positivity) (by linarith only [hP]) (hx 1 le_rfl)
    have h₃ := hCoeff (3 * p) 6 _ (by positivity) (by linarith only [hP]) (hy 1 le_rfl)
    have h₄ := hCoeff _ 2 _ hp₀.le hP hj'
    have h := (norm_sub_le _ _).trans (add_le_add (hMix _ _ _ _ _ _ h₁ h₂ h₃) h₄)
    exact h.trans (by linarith only [hB])
  · change ‖p * (p + 1) * ((p + 2) * m * x ^ (-p - 3) - 4 * x ^ (-p - 2) +
      9 * y ^ (-p - 2))‖ ≤ 1800 * B
    have hM₂ : (p + 2) * m ≤ 8 :=
      (mul_le_mul (by linarith only [hP] : p + 2 ≤ 4) hM' hM.le (by norm_num : (0 : ℝ) ≤ 4)).trans_eq (by norm_num)
    have h₁ := hCoeff _ 8 _ (by positivity) hM₂ (hx 3 (by norm_num))
    have h₂ := hCoeff (4 : ℝ) 4 _ (by norm_num) le_rfl (hx 2 (by norm_num))
    have h₃ := hCoeff (9 : ℝ) 9 _ (by norm_num) le_rfl (hy 2 (by norm_num))
    have h := hMix _ _ _ _ _ _ h₁ h₂ h₃
    rw [norm_mul,Real.norm_of_nonneg (by positivity : 0 ≤ p * (p + 1))]
    apply (mul_le_mul hF h (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)).trans
    linarith only [hB]
  · change ‖p * (p + 1) * (p + 2) * ((p + 3) * m * x ^ (-p - 4) - 6 * x ^ (-p - 3) +
      27 * y ^ (-p - 3))‖ ≤ 1800 * B
    have hM₂ : (p + 3) * m ≤ 10 :=
      (mul_le_mul (by linarith only [hP] : p + 3 ≤ 5) hM' hM.le (by norm_num : (0 : ℝ) ≤ 5)).trans_eq (by norm_num)
    have h₁ := hCoeff _ 10 _ (by positivity) hM₂ (hx 4 (by norm_num))
    have h₂ := hCoeff (6 : ℝ) 6 _ (by norm_num) le_rfl (hx 3 (by norm_num))
    have h₃ := hCoeff (27 : ℝ) 27 _ (by norm_num) le_rfl (hy 3 (by norm_num))
    have h := hMix _ _ _ _ _ _ h₁ h₂ h₃
    rw [norm_mul,Real.norm_of_nonneg (by positivity : 0 ≤ p * (p + 1) * (p + 2))]
    apply (mul_le_mul hG h (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 24)).trans
    linarith only [hB]

private theorem leftPair_dominator : Summable (fun j : ℕ => (1800 : ℝ) * (1 + (j : ℝ)) ^ (-2 : ℝ)) := by
  have h := (powerTail_summable (q := (2 : ℝ)) (by norm_num) (1 : ℕ)).mul_left (1800 : ℝ)
  simpa only [Nat.cast_one] using h

private theorem leftPair_summable {k : ℕ} (hk : k ≤ 3) {p δ : ℝ} (hp : 1 ≤ p) (hP : p ≤ 2)
    (hδ : δ ∈ leftMotionBand) : Summable (fun j : ℕ => leftPairAtom k p (1 + (j : ℝ)) δ) :=
  Summable.of_norm_bounded leftPair_dominator fun j =>
    leftPairAtom_bound hk hp hP (le_add_of_nonneg_right (Nat.cast_nonneg j)) hδ

noncomputable def lowerLeftPairSum (k : ℕ) (p δ : ℝ) : ℝ :=
  ∑' j : ℕ, leftPairAtom k p (1 + (j : ℝ)) δ

theorem lowerLeftPairSum_deriv {k : ℕ} (hk : k < 3) {p δ : ℝ} (hp : 1 ≤ p) (hP : p ≤ 2)
    (hδ : δ ∈ leftMotionBand) :
    HasDerivAt (lowerLeftPairSum k p) (lowerLeftPairSum (k + 1) p δ) δ := by
  exact hasDerivAt_tsum_of_isPreconnected leftPair_dominator isOpen_Ioo (convex_Ioo _ _).isPreconnected
    (fun j x hx => leftPairAtom_deriv hk p (1 + (j : ℝ)) x
      (by linarith only [hx.2,Nat.cast_nonneg (α := ℝ) j])
      (by linarith only [hx.2,Nat.cast_nonneg (α := ℝ) j]))
    (fun j x hx => leftPairAtom_bound (by omega) hp hP (le_add_of_nonneg_right (Nat.cast_nonneg j)) hx)
    hδ (leftPair_summable (by omega) hp hP hδ) hδ


private theorem lowerLeftPairSum_third_nonneg {p δ : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hδ : 0 ≤ δ) (hD : δ ≤ 1 / 8) : 0 ≤ lowerLeftPairSum 3 p δ := by
  unfold lowerLeftPairSum
  apply tsum_nonneg
  intro j
  exact (leftPairAtom_third_pos hp hP (le_add_of_nonneg_right (Nat.cast_nonneg j)) hδ hD).le

private noncomputable def lowerLeftFinite (k : ℕ) (p δ : ℝ) : ℝ :=
  let u := 1 - δ
  let y := 2 - 3 * δ
  match k with
  | 0 => u ^ (-p) - 2 * u ^ (1 - p) + (y ^ (-p) + y ^ (1 - p)) / 3
  | 1 => p * u ^ (-p - 1) - 2 * (p - 1) * u ^ (-p) +
      p * y ^ (-p - 1) + (p - 1) * y ^ (-p)
  | 2 => p * (p + 1) * u ^ (-p - 2) - 2 * p * (p - 1) * u ^ (-p - 1) +
      3 * (p * (p + 1) * y ^ (-p - 2) + p * (p - 1) * y ^ (-p - 1))
  | _ => p * (p + 1) * (p + 2) * u ^ (-p - 3) - 2 * p * (p + 1) * (p - 1) * u ^ (-p - 2) +
      9 * (p * (p + 1) * (p + 2) * y ^ (-p - 3) + p * (p + 1) * (p - 1) * y ^ (-p - 2))

private theorem lowerLeftFinite_deriv {k : ℕ} (hk : k < 3) {p δ : ℝ} (hδ : δ ∈ leftMotionBand) :
    HasDerivAt (lowerLeftFinite k p) (lowerLeftFinite (k + 1) p δ) δ := by
  have hU : 0 < 1 - 1 * δ := by linarith only [hδ.2]
  have hY : 0 < 2 - 3 * δ := by linarith only [hδ.2]
  have hu (r : ℝ) := affinePower_deriv 1 1 r δ hU
  have hy (r : ℝ) := affinePower_deriv 2 3 r δ hY
  simp only [one_mul,neg_mul] at hu
  interval_cases k
  · convert ((hu (-p)).sub ((hu (1 - p)).const_mul 2)).add
      (((hy (-p)).add (hy (1 - p))).div_const 3) using 1
    simp only [lowerLeftFinite,show 1 - p - 1 = -p by ring]
    ring
  · convert ((((hu (-p - 1)).const_mul p).sub ((hu (-p)).const_mul (2 * (p - 1)))).add
      ((hy (-p - 1)).const_mul p)).add ((hy (-p)).const_mul (p - 1)) using 1
    simp only [lowerLeftFinite,show -p - 1 - 1 = -p - 2 by ring]
    ring
  · convert (((hu (-p - 2)).const_mul (p * (p + 1))).sub
      ((hu (-p - 1)).const_mul (2 * p * (p - 1)))).add
      ((((hy (-p - 2)).const_mul (p * (p + 1))).add
        ((hy (-p - 1)).const_mul (p * (p - 1)))).const_mul 3) using 1
    simp only [lowerLeftFinite,show -p - 2 - 1 = -p - 3 by ring,show -p - 1 - 1 = -p - 2 by ring]
    ring

private theorem lowerLeftFinite_third_gt {p δ : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hδ : 0 ≤ δ) (hD : δ ≤ 1 / 8) :
    p * (p + 1) * (p + 2) * (1 - δ) ^ (-p - 3) / 2 < lowerLeftFinite 3 p δ := by
  let u := 1 - δ
  let y := 2 - 3 * δ
  have hu : 0 < u := by unfold u; linarith only [hD]
  have hy : 0 < y := by unfold y; linarith only [hD]
  have hp₀ := zero_lt_one.trans_le hp
  have hp₁ := sub_nonneg.mpr hp
  have hU : u ≤ 1 := by unfold u; linarith only [hδ]
  have h := mul_le_of_le_one_right hp₁ hU
  have hK : 2 * (p - 1) * u < (p + 2) / 2 := by linarith only [h,hP]
  have hA : 0 < p * (p + 1) * u ^ (-p - 3) := by positivity
  have hMul := mul_lt_mul_of_pos_left hK hA
  have hE : u ^ (-p - 2) = u ^ (-p - 3) * u := by
    rw [← Real.rpow_add_one hu.ne']
    congr 1
    ring
  change p * (p + 1) * (p + 2) * u ^ (-p - 3) / 2 <
      p * (p + 1) * (p + 2) * u ^ (-p - 3) - 2 * p * (p + 1) * (p - 1) * u ^ (-p - 2) +
        9 * (p * (p + 1) * (p + 2) * y ^ (-p - 3) + p * (p + 1) * (p - 1) * y ^ (-p - 2))
  rw [hE]
  nlinarith only [hMul,show 0 ≤ p * (p + 1) * (p + 2) * y ^ (-p - 3) +
    p * (p + 1) * (p - 1) * y ^ (-p - 2) by positivity]

noncomputable def lowerLeftCombined (k : ℕ) (p δ : ℝ) : ℝ :=
  lowerLeftFinite k p δ + lowerLeftPairSum k p δ

theorem lowerLeftCombined_deriv {k : ℕ} (hk : k < 3) {p δ : ℝ} (hp : 1 ≤ p) (hP : p ≤ 2)
    (hδ : δ ∈ leftMotionBand) :
    HasDerivAt (lowerLeftCombined k p) (lowerLeftCombined (k + 1) p δ) δ :=
  (lowerLeftFinite_deriv hk hδ).add (lowerLeftPairSum_deriv hk hp hP hδ)

theorem lowerLeftCombined_third_pos {p δ : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hδ : 0 ≤ δ) (hD : δ ≤ 1 / 8) : 0 < lowerLeftCombined 3 p δ := by
  have hp₀ := zero_lt_one.trans_le hp
  have hu : 0 < 1 - δ := by linarith only [hD]
  have hA : 0 < p * (p + 1) * (p + 2) * (1 - δ) ^ (-p - 3) := by positivity
  unfold lowerLeftCombined
  linarith only [lowerLeftPairSum_third_nonneg hp hP hδ hD,lowerLeftFinite_third_gt hp hP hδ hD,hA]


theorem lowerLeftCombined_zero_eq {p δ : ℝ} (hp : 1 ≤ p) (hP : p ≤ 2)
    (hδ : δ ∈ leftMotionBand) :
    lowerLeftCombined 0 p δ = lowerDiagonalLeft p δ + lowerDiagonalKnown p δ := by
  let m := lowerDiagonalMass δ
  let u := 1 - δ
  let y := 2 - 3 * δ
  have hu : 0 < u := by unfold u; linarith only [hδ.2]
  have hm : 0 < m := by unfold m lowerDiagonalMass; linarith only [hδ.2]
  have hy : 0 < y := by unfold y; linarith only [hδ.2]
  have hu₂ : u ≤ 2 := by unfold u; linarith only [hδ.1]
  have hm₂ : m ≤ 2 := by unfold m lowerDiagonalMass; linarith only [hδ.1]
  let a (j : ℕ) := purePeanoB p m (u + (1 + (j : ℝ)))
  let b (j : ℕ) := purePeanoB p u (1 + (j : ℝ))
  have hBound : Summable (fun j : ℕ => (4 : ℝ) * (1 + (j : ℝ)) ^ (-2 : ℝ)) := by
    simpa only [Nat.cast_one] using (powerTail_summable (q := 2) (by norm_num) 1).mul_left (4 : ℝ)
  have hA : Summable a := Summable.of_norm_bounded hBound fun j =>
    leftPeano_norm_le hp hP (le_add_of_nonneg_right (Nat.cast_nonneg j)) (le_add_of_nonneg_left hu.le) hm hm₂
  have hB : Summable b := Summable.of_norm_bounded hBound fun j =>
    leftPeano_norm_le hp hP (le_add_of_nonneg_right (Nat.cast_nonneg j)) le_rfl hu hu₂
  have hSum : lowerLeftPairSum 0 p δ = (∑' j, a j) + ∑' j, b j := by
    unfold lowerLeftPairSum
    have hEq (j : ℕ) : leftPairAtom 0 p (1 + (j : ℝ)) δ = a j + b j := by
      simp only [leftPairAtom,a,b,m,lowerDiagonalMass,u,add_comm]
    simp_rw [hEq]
    exact hA.tsum_add hB
  have hF : lowerLeftFinite 0 p δ = u * purePeanoB p m u + lowerKnownFinite p δ := by
    change u ^ (-p) - 2 * u ^ (1 - p) + (y ^ (-p) + y ^ (1 - p)) / 3 =
      u * purePeanoB p m u + ((p + 1) * u ^ (-p) - (2 * p + 1) * u ^ (1 - p))
    unfold purePeanoB
    rw [show u + m = y by unfold u m lowerDiagonalMass y; ring,
      show -(p + 1) = -p - 1 by ring,Real.rpow_sub_one hu.ne',
      show 1 - p = -p + 1 by ring,Real.rpow_add_one hu.ne',Real.rpow_add_one hy.ne']
    have hM : m = 2 * u - 1 := by unfold m lowerDiagonalMass u; ring
    have hY : y = 3 * u - 1 := by unfold y u; ring
    rw [hM]
    field_simp [hu.ne']
    linear_combination u * y ^ (-p) * hY
  unfold lowerLeftCombined
  rw [hF,hSum]
  unfold lowerDiagonalLeft lowerDiagonalKnown
  rw [lowerKnownSum_zero_eq]
  change _ = (u * purePeanoB p m u + ∑' j, a j) + (lowerKnownFinite p δ + ∑' j, b j)
  ring

end ACS12.GammaMeasure

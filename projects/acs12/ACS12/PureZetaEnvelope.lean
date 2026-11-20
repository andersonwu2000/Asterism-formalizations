import ACS12.PureCMoments

/-! Complete power-tail envelopes for the one-source outer corner. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaDeficit (gamma_exp_integral integrable_gamma_exp)

theorem powerTail_trapezoid_lower {q : ℝ} (hq : 1 < q) {m : ℕ} (hm : 0 < m) :
    ((m : ℝ) ^ (1 - q)) / (q - 1) + ((m : ℝ) ^ (-q)) / 2 <
      powerTail q m := by
  let d : ℝ := m
  have hd : 0 < d := Nat.cast_pos.mpr hm
  have hq₀ : 0 < q := zero_lt_one.trans hq
  have hq₁ : 0 < q - 1 := sub_pos.mpr hq
  have hG : 0 < Real.Gamma q := Real.Gamma_pos_of_pos hq₀
  let f (s : ℝ) := s ^ (q - 1) * (Real.exp (-s * d) / (1 - Real.exp (-s)))
  let A (s : ℝ) := s ^ (q - 2) * Real.exp (-s * d)
  let B (s : ℝ) := s ^ (q - 1) * Real.exp (-s * d)
  have hf : IntegrableOn f (Ioi 0) := boseMoment_integrable hq₁ hm
  have hA : IntegrableOn A (Ioi 0) := by
    simpa only [A, show q - 1 - 1 = q - 2 by ring, neg_mul, mul_comm d] using integrable_gamma_exp hq₁ hd
  have hB : IntegrableOn B (Ioi 0) := by
    simpa only [B, neg_mul, mul_comm d] using integrable_gamma_exp hq₀ hd
  have hI : IntegrableOn (fun s => A s + (1 / 2) * B s) (Ioi 0) :=
    hA.add (hB.const_mul (1 / 2))
  letI : NeZero (volume.restrict (Ioi (0 : ℝ))) := ⟨positiveHalfLine_ne_zero⟩
  have hLt := integral_strict_of_ae_lt (volume.restrict (Ioi (0 : ℝ))) hI hf ?_
  · have hfE : (∫ s : ℝ in Ioi 0, f s) = Real.Gamma q * powerTail q m := by
      simpa only [f, d, sub_add_cancel] using boseMoment_integral hq₁ hm
    have hAE : (∫ s : ℝ in Ioi 0, A s) = Real.Gamma (q - 1) * d ^ (1 - q) := by
      simpa only [A, show q - 1 - 1 = q - 2 by ring, show -(q - 1) = 1 - q by ring,
        neg_mul, mul_comm d] using gamma_exp_integral hq₁ hd
    have hBE : (∫ s : ℝ in Ioi 0, B s) = Real.Gamma q * d ^ (-q) := by
      simpa only [B, neg_mul, mul_comm d] using gamma_exp_integral hq₀ hd
    rw [hfE, integral_add hA (hB.const_mul (1 / 2)), integral_const_mul, hAE, hBE] at hLt
    have hGamma : Real.Gamma (q - 1) = Real.Gamma q / (q - 1) := by
      apply (eq_div_iff hq₁.ne').mpr
      simpa only [sub_add_cancel, mul_comm] using (Real.Gamma_add_one hq₁.ne').symm
    rw [hGamma] at hLt
    apply lt_of_mul_lt_mul_left ?_ hG.le
    refine hLt.trans_le' (le_of_eq ?_)
    dsimp only [d]
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0 < s := hs
    have hH := BoseShape.expHeadFactor_gt_one_add_half hs₀
    have hHead : s⁻¹ + 1 / 2 < (1 - Real.exp (-s))⁻¹ := by
      have hE : (1 - Real.exp (-s))⁻¹ * s = expHeadFactor s := by unfold expHeadFactor; ring
      apply lt_of_mul_lt_mul_right _ hs₀.le
      rw [hE, add_mul, inv_mul_cancel₀ hs₀.ne']
      convert hH using 1 <;> ring
    have hMul := mul_lt_mul_of_pos_left hHead
      (mul_pos (Real.rpow_pos_of_pos hs₀ (q - 1)) (Real.exp_pos (-s * d)))
    have h1 : s ^ (q - 1) * s⁻¹ = s ^ (q - 2) := by
      rw [← div_eq_mul_inv, ← Real.rpow_sub_one hs₀.ne', show q - 1 - 1 = q - 2 by ring]
    dsimp only [f, A, B]
    simp only [div_eq_mul_inv]
    nlinarith only [hMul, congrArg (fun x => x * Real.exp (-s * d)) h1]

theorem powerTail_exponent_antitone {q r : ℝ} (hq : 1 < q) (hqr : q ≤ r)
    {m : ℕ} (hm : 0 < m) : powerTail r m ≤ powerTail q m := by
  apply (powerTail_summable (hq.trans_le hqr) m).tsum_le_tsum _ (powerTail_summable hq m)
  intro j
  apply Real.rpow_le_rpow_of_exponent_le _ (neg_le_neg hqr)
  exact (show (1 : ℝ) ≤ m by exact_mod_cast hm).trans (le_add_of_nonneg_right (Nat.cast_nonneg j))

theorem fifth_rpow_lower {b x : ℝ} {k : ℕ} (hb : 0 < b) (hx : 0 ≤ x)
    (h : x ^ 5 < (b ^ k)⁻¹) : x < b ^ (-(k : ℝ) / 5) := by
  apply (Real.rpow_lt_rpow_iff hx (Real.rpow_nonneg hb.le _) (z := (5 : ℝ)) (by norm_num)).mp
  rw [← Real.rpow_mul hb.le, show -(k : ℝ) / 5 * 5 = -(k : ℝ) by ring,
    Real.rpow_neg hb.le, Real.rpow_natCast, show (5 : ℝ) = (5 : ℕ) by norm_num,
    Real.rpow_natCast]
  exact h

theorem fifth_rpow_upper {b x : ℝ} {k : ℕ} (hb : 0 < b) (hx : 0 ≤ x)
    (h : (b ^ k)⁻¹ < x ^ 5) : b ^ (-(k : ℝ) / 5) < x := by
  apply (Real.rpow_lt_rpow_iff (Real.rpow_nonneg hb.le _) hx (z := (5 : ℝ)) (by norm_num)).mp
  rw [← Real.rpow_mul hb.le, show -(k : ℝ) / 5 * 5 = -(k : ℝ) by ring,
    Real.rpow_neg hb.le, Real.rpow_natCast, show (5 : ℝ) = (5 : ℕ) by norm_num,
    Real.rpow_natCast]
  exact h

theorem pureQ_lower {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    (1097 / 1000) * (p * (p + 1)) < pureQ p := by
  have h₁ : (7179 / 100000 : ℝ) < (2 : ℝ) ^ (-(19 / 5 : ℝ)) := by
    convert fifth_rpow_lower (k := 19) (b := 2) (x := 7179 / 100000)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  have h₂ : (1537 / 100000 : ℝ) < (3 : ℝ) ^ (-(19 / 5 : ℝ)) := by
    convert fifth_rpow_lower (k := 19) (b := 3) (x := 1537 / 100000)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  have h₃ : (2061 / 100000 : ℝ) < (4 : ℝ) ^ (1 - (19 / 5 : ℝ)) := by
    convert fifth_rpow_lower (k := 14) (b := 4) (x := 2061 / 100000)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  have h₄ : (515 / 100000 : ℝ) < (4 : ℝ) ^ (-(19 / 5 : ℝ)) := by
    convert fifth_rpow_lower (k := 19) (b := 4) (x := 515 / 100000)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  have hQ := powerTail_trapezoid_lower (q := (19 / 5 : ℝ)) (m := 4)
    (by norm_num) (by decide)
  have hS (n : ℕ) := powerTail_shift (q := (19 / 5 : ℝ)) (by norm_num) n
  have hE : powerTail (19 / 5) 1 =
      1 + (2 : ℝ) ^ (-(19 / 5 : ℝ)) + (3 : ℝ) ^ (-(19 / 5 : ℝ)) + powerTail (19 / 5) 4 := by
    have h := hS 1
    have h' := hS 2
    have h'' := hS 3
    norm_num at h h' h''
    linarith only [h, h', h'']
  have hX : (1097 / 1000 : ℝ) < powerTail (19 / 5) 1 := by
    rw [hE]
    norm_num at hQ
    linarith only [hQ, h₁, h₂, h₃, h₄]
  have hOrd := powerTail_exponent_antitone (q := p + 2) (r := 19 / 5) (by linarith)
    (by linarith) (by decide : 0 < (1 : ℕ))
  unfold pureQ
  exact mul_lt_mul_of_pos_right (hX.trans_le hOrd) (show 0 < p * (p + 1) by positivity) |>.trans_eq (mul_comm _ _)

theorem pureZ_trapezoid_lower {p : ℝ} (hp : 1 ≤ p) :
    p + (2 : ℝ) ^ (-p) * (1 + p / 4) < pureZ p := by
  have hp₀ := zero_lt_one.trans_le hp
  have h := powerTail_trapezoid_lower (q := p + 1) (m := 2) (by linarith) (by decide)
  have hE := powerTail_shift (q := p + 1) (by linarith) 1
  simp only [Nat.cast_one, Real.one_rpow, show (1 : ℕ) + 1 = 2 by decide] at hE
  rw [hE] at h
  norm_num only [Nat.cast_ofNat] at h
  rw [add_sub_cancel_right, show 1 - (p + 1) = -p by ring, show -(p + 1) = -p - 1 by ring,
    Real.rpow_sub_one (by norm_num : (2 : ℝ) ≠ 0)] at h
  have h' := mul_lt_mul_of_pos_left h hp₀
  unfold pureZ
  have hE' : p * ((2 : ℝ) ^ (-p) / p + (2 : ℝ) ^ (-p) / 2 / 2) =
      (2 : ℝ) ^ (-p) * (1 + p / 4) := by
    field_simp [hp₀.ne']
    ring
  rw [hE'] at h'
  linarith only [h', mul_sub p (powerTail (p + 1) 1) 1]

theorem pureZ_B2_upper {p : ℝ} (hp : 1 ≤ p) :
    pureZ p < p + (2 : ℝ) ^ (-p) * (1 + p / 4 + p * (p + 1) / 48) := by
  have hp₀ := zero_lt_one.trans_le hp
  have h := powerTail_B2 (q := p + 1) (m := 2) (by linarith) (by decide)
  have hE := powerTail_shift (q := p + 1) (by linarith) 1
  simp only [Nat.cast_one, Real.one_rpow, show (1 : ℕ) + 1 = 2 by decide] at hE
  rw [hE] at h
  norm_num only [Nat.cast_ofNat] at h
  rw [add_sub_cancel_right, show 1 - (p + 1) = -p by ring, show -(p + 1) = -p - 1 by ring,
    show -(p + 1 + 1) = -p - 2 by ring, Real.rpow_sub_one (by norm_num : (2 : ℝ) ≠ 0),
    Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_two] at h
  have h' := mul_lt_mul_of_pos_left h hp₀
  unfold pureZ
  have hE' : p * ((2 : ℝ) ^ (-p) / p + (2 : ℝ) ^ (-p) / 2 / 2 +
      (p + 1) / 12 * ((2 : ℝ) ^ (-p) / 2 ^ 2)) =
      (2 : ℝ) ^ (-p) * (1 + p / 4 + p * (p + 1) / 48) := by
    field_simp [hp₀.ne']
    ring
  rw [hE'] at h'
  linarith only [h', mul_sub p (powerTail (p + 1) 1) 1]

theorem two_neg_rpow_chord {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    (2 : ℝ) ^ (-p) ≤ 1 / 2 - (1063 / 4000) * (p - 1) := by
  have hConv := convexOn_rpow_left (b := (2 : ℝ)⁻¹) (by norm_num)
  have hA : 0 ≤ (9 / 5 - p) / (4 / 5) := div_nonneg (sub_nonneg.mpr hP) (by norm_num)
  have hB : 0 ≤ (p - 1) / (4 / 5) := div_nonneg (sub_nonneg.mpr hp) (by norm_num)
  have h := hConv.2 (show (1 : ℝ) ∈ univ from trivial) (show (9 / 5 : ℝ) ∈ univ from trivial)
    hA hB (by ring)
  simp only [smul_eq_mul, mul_one, Real.rpow_one] at h
  rw [show (9 / 5 - p) / (4 / 5) + (p - 1) / (4 / 5) * (9 / 5) = p by ring] at h
  simp_rw [Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)] at h
  have h2 : (2 : ℝ) ^ (-(9 / 5 : ℝ)) < 1437 / 5000 := by
    convert fifth_rpow_upper (k := 9) (b := 2) (x := 1437 / 5000)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  have h3 := mul_le_mul_of_nonneg_left h2.le hB
  linarith only [h, h3]

end ACS12.GammaMeasure

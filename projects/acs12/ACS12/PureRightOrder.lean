import ACS12.PureNativeBasics
import ACS12.LawClip

/-! The same-exponent pure right tail and its low-gap extinction. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaDeficit (lineDensity)

theorem pureRight_nonpos_of_exponent_le {p q u t : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q)
    (hq : q ≤ 2) (ht : 0 < t) (h : pureRight q u t ≤ 0) : pureRight p u t ≤ 0 := by
  let W (s : ℝ) := lineDensity q s * s * Real.exp (-s * t)
  let Q := rightMultiplier (middleA u) (middleZ u)
  let R (s : ℝ) := (Real.Gamma q / Real.Gamma p) * s ^ (p - q)
  let F (a s : ℝ) := lineDensity a s * s * Real.exp (-s * t)
  let G (a s : ℝ) := lineDensity a s * middleRightDensity u s * Real.exp (-s * t)
  have hp₀ := zero_lt_one.trans_le hp
  have hq₀ := hp₀.trans_le hpq
  have hp₂ := hpq.trans hq
  have hθ : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have hFI (a : ℝ) (ha : 1 ≤ a) (ha₂ : a ≤ 2) : IntegrableOn (F a) (Ioi 0) := by
    simpa only [F, lawDensity, sub_zero, one_mul, zero_mul, add_zero, pow_one] using
      lawMoment_integrable (L := 1) ha ha₂ zero_lt_one hθ ht 1
  have hGI (a : ℝ) (ha : 1 ≤ a) (ha₂ : a ≤ 2) : IntegrableOn (G a) (Ioi 0) := by
    simpa only [G, lawRightDensity, lawDensity, sub_zero, one_mul, zero_mul, add_zero] using
      lawRightDensity_integrable (L := 1) (u := u) ha ha₂ zero_lt_one hθ ht
  have hPure (a : ℝ) (ha : 1 ≤ a) (ha₂ : a ≤ 2) :
      (∫ s : ℝ in Ioi 0, G a s) = pureRight a u t := by
    rw [← lawRightTest_zero (L := 1) ha ha₂ zero_lt_one ht]
    simp only [G, lawRightTest, signedLaplace, lawRightDensity, lawDensity, sub_zero,
      one_mul, zero_mul, add_zero]
  have hE (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) : W s * Q s = G q s := by
    dsimp only [W, Q, G]
    rw [middleRightDensity_eq hs]
    ring
  have hDensity (s : ℝ) (hs : 0 < s) : lineDensity q s * R s = lineDensity p s := by
    unfold lineDensity R
    calc
      _ = (s ^ (q - 1) * s ^ (p - q)) / Real.Gamma p := by
        field_simp [(Real.Gamma_pos_of_pos hq₀).ne']
      _ = _ := by rw [← Real.rpow_add hs, show q - 1 + (p - q) = p - 1 by ring]
  have hF (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) : W s * R s = F p s := by
    change _ = lineDensity p s * s * Real.exp (-s * t)
    rw [← hDensity s hs]
    dsimp only [W]
    ring
  have hG (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) : W s * Q s * R s = G p s := by
    rw [mul_right_comm, hF s hs]
    dsimp only [F, Q, G]
    rw [middleRightDensity_eq hs]
    ring
  have hQI : IntegrableOn (fun s => W s * Q s) (Ioi 0) := (hGI q (hp.trans hpq) hq).congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hE s hs).symm)
  have hRI : IntegrableOn (fun s => W s * R s) (Ioi 0) := (hFI p hp hp₂).congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hF s hs).symm)
  have hPI : IntegrableOn (fun s => W s * Q s * R s) (Ioi 0) := (hGI p hp hp₂).congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hG s hs).symm)
  have hPos (s : ℝ) (hs : 0 < s) : 0 < W s :=
    mul_pos (mul_pos (lineDensity_pos hq₀ hs) hs) (Real.exp_pos _)
  have hK : 0 ≤ Real.Gamma q / Real.Gamma p :=
    div_nonneg (Real.Gamma_pos_of_pos hq₀).le (Real.Gamma_pos_of_pos hp₀).le
  have hRA : AntitoneOn R (Ioi 0) := by
    intro a ha b hb hab
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ha hab (sub_nonpos.mpr hpq)) hK
  have hQ₀ : (∫ s : ℝ in Ioi 0, W s * Q s) ≤ 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioi hE, hPure q (hp.trans hpq) hq]
    exact h
  have hBound := integral_antitone_product_nonpos (hFI q (hp.trans hpq) hq) hQI hRI hPI hPos
    (fun s hs => mul_nonneg hK (Real.rpow_nonneg hs.le _))
    (rightMultiplier_mono ((middleA_le u).trans (by norm_num))) hRA hQ₀
  rwa [setIntegral_congr_fun measurableSet_Ioi hG, hPure p hp hp₂] at hBound

theorem pureRight_native_pos {p u : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hu : 1 / 2 ≤ u) :
    0 < pureRight p u u := by
  have hu₀ : 0 < u := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hu
  by_contra! h
  have hP := pureRight_nonpos_of_exponent_le le_rfl hp hp₂ hu₀ h
  rw [pureRight_one_at_u hu₀] at hP
  have hN := (div_le_iff₀ (by positivity : 0 < 25 * u * (1 + u) ^ 2)).mp hP
  simp only [zero_mul] at hN
  have hU := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hu 2
  nlinarith only [hN, hU, hu]

private theorem cutoff_at_upper {u : ℝ} (hu : 0 < u) (hu' : u ≤ 1 / 2) :
    pureRight (9 / 5) u (5 * u / 3) < 0 := by
  let t := 5 * u / 3
  have ht : 0 < t := by dsimp only [t]; positivity
  have h := pureRight_scaled (p := 9 / 5) (u := u) ht
  have hZ : (9 / 5 : ℝ) * middleZ u / t - 1 = (162 * u - 274) / 625 := by
    dsimp only [t]
    unfold middleZ middleA
    field_simp [hu.ne']
    ring
  have hA : (9 / 5 : ℝ) * middleA u / (t + 1) = (162 / 125) * (u * (2 - u) / (3 + 5 * u)) := by
    dsimp only [t]
    unfold middleA
    field_simp
    ring
  have hR : t / (t + 1) ≤ 5 / 11 := by
    apply (div_le_iff₀ (by positivity : 0 < t + 1)).mpr
    dsimp only [t]
    linarith
  have hPow : (5 / 11 : ℝ) ^ (9 / 5 : ℝ) < 1 / 4 := by
    apply (Real.rpow_lt_rpow_iff (by positivity) (by norm_num) (z := 5) (by norm_num)).mp
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 5 / 11),
      show (9 / 5 : ℝ) * 5 = (9 : ℕ) by norm_num, show (5 : ℝ) = (5 : ℕ) by norm_num,
      Real.rpow_natCast, Real.rpow_natCast]
    norm_num
  have hT : (t / (t + 1)) ^ (9 / 5 : ℝ) ≤ 1 / 4 :=
    (Real.rpow_le_rpow (div_nonneg ht.le (by positivity)) hR (by norm_num)).trans hPow.le
  have hA' : u * (2 - u) / (3 + 5 * u) ≤ 3 / 22 := by
    apply (div_le_iff₀ (by positivity : 0 < 3 + 5 * u)).mpr
    nlinarith only [mul_nonneg (sub_nonneg.mpr hu') (show 0 ≤ 18 - 22 * u by linarith)]
  have hPos : 0 ≤ 1 + (162 / 125) * (u * (2 - u) / (3 + 5 * u)) := by
    have hU : 0 ≤ 2 - u := by linarith
    positivity
  have hB := mul_le_mul hT
    (show 1 + (162 / 125) * (u * (2 - u) / (3 + 5 * u)) ≤ 1 + (162 / 125) * (3 / 22) by
      linarith only [hA']) hPos (by norm_num : (0 : ℝ) ≤ 1 / 4)
  rw [hZ, hA] at h
  by_contra! hNeg
  have hNonneg := mul_nonneg hNeg (Real.rpow_nonneg ht.le (9 / 5))
  linarith only [h, hB, hu', hNonneg]

theorem pureRight_low_gap_nonpos {p u : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hu : 0 < u) (hu' : u ≤ 1 / 2) : pureRight p u (5 * u / 3) ≤ 0 :=
  pureRight_nonpos_of_exponent_le hp hP (by norm_num) (by positivity) (cutoff_at_upper hu hu').le

theorem pureRight_low_gap_tail_zero {p L u t q : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hL : 0 < L) (hu : 0 < u) (hu' : u ≤ 1 / 2) (hq : 0 < q) (hArg : 5 * u / 3 ≤ t + q) :
    samplingTail (lawRightClip p L 0 u) t q = 0 := by
  have hp₂ := hP.trans (by norm_num : (9 / 5 : ℝ) ≤ 2)
  have hθ : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have hx : 0 < 5 * u / 3 := by positivity
  have hCut : lawRightClip p L 0 u (5 * u / 3) = 0 := by
    rw [lawRightClip, lawRightTest_zero hp hp₂ hL hx, max_eq_left (pureRight_low_gap_nonpos hp hP hu hu')]
  have hK (j : ℕ) : lawRightClip p L 0 u (t + ((j + 1 : ℕ) : ℝ) * q) = 0 := by
    have hj : 5 * u / 3 ≤ t + ((j + 1 : ℕ) : ℝ) * q := by
      push_cast
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) j) hq.le]
    apply le_antisymm _ (le_max_left _ _)
    exact (lawRightClip_antitone hp hp₂ hL hθ hx (hx.trans_le hj) hj).trans_eq hCut
  simp only [samplingTail, hK, tsum_zero, mul_zero]

end ACS12.GammaMeasure

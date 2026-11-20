import ACS12.PureZetaEnvelope
import ACS12.PureClipPrice

/-! One-source unit value and its complete correlated clipping budget. -/

namespace ACS12.GammaMeasure

open Set

noncomputable def outerUnitValue (p : ℝ) : ℝ :=
  (81 / 100) * (p - 1) * pureZ p - (6 / 25) * pureQ p - 19 / 100

private noncomputable def clipPriceBase (p : ℝ) : ℝ :=
  (7 / 4) * Real.exp (-(p + 1) * Real.log ((7 / 4) * (p + 1)))

private theorem clipPriceBase_eq {p : ℝ} (hp : 1 ≤ p) :
    clipPriceBase p = ((7 / 4) * (p + 1)) ^ (-p) / (p + 1) := by
  let b := (7 / 4 : ℝ) * (p + 1)
  have hb : 0 < b := by dsimp only [b]; positivity
  have h : p + 1 ≠ 0 := by positivity
  change (7 / 4 : ℝ) * Real.exp (-(p + 1) * Real.log b) = b ^ (-p) / (p + 1)
  rw [mul_comm (-(p + 1)), ← Real.rpow_def_of_pos hb,
    show -(p + 1) = -p - 1 by ring, Real.rpow_sub_one hb.ne']
  dsimp only [b]
  field_simp [h]

private theorem clipPriceBase_convex : ConvexOn ℝ (Icc 1 (9 / 5)) clipPriceBase := by
  let b (p : ℝ) := (7 / 4) * (p + 1)
  let L (p : ℝ) := 1 + Real.log (b p)
  have hB (p : ℝ) (hp : 1 ≤ p) : 0 < b p := by dsimp only [b]; positivity
  have hL (p : ℝ) (hp : 1 ≤ p) : HasDerivAt L (1 / (p + 1)) p := by
    have h := ((hasDerivAt_id p).add_const 1).const_mul (7 / 4)
    convert ((Real.hasDerivAt_log (hB p hp).ne').comp p h).const_add 1 using 1
    simp only [id_eq, b, mul_one]
    field_simp [(show p + 1 ≠ 0 by positivity)]
  have hD (p : ℝ) (hp : 1 ≤ p) :
      HasDerivAt clipPriceBase (-clipPriceBase p * L p) p := by
    have hB' := ((hasDerivAt_id p).add_const 1).const_mul (7 / 4)
    have hLog := (Real.hasDerivAt_log (hB p hp).ne').comp p hB'
    convert ((((hasDerivAt_id p).add_const 1).neg.mul hLog).exp).const_mul (7 / 4) using 1
    simp only [clipPriceBase, L, b, id_eq, mul_one, Pi.mul_apply, Pi.neg_apply, Function.comp_apply]
    field_simp [(show p + 1 ≠ 0 by positivity)]
    ring
  have hD₂ (p : ℝ) (hp : 1 ≤ p) :
      HasDerivAt (fun q => -clipPriceBase q * L q)
        (clipPriceBase p * ((L p) ^ 2 - 1 / (p + 1))) p := by
    convert ((hD p hp).neg.mul (hL p hp)) using 1
    simp only [Pi.neg_apply]
    ring
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
    (fun p hp => (hD p hp.1).continuousAt.continuousWithinAt)
    (fun p hp => (hD p (interior_subset hp).1).hasDerivWithinAt)
    (fun p hp => (hD₂ p (interior_subset hp).1).hasDerivWithinAt)
  intro p hp
  have hp₀ : 1 ≤ p := (interior_subset hp).1
  have hLog : 0 ≤ Real.log (b p) := Real.log_nonneg (by dsimp only [b]; linarith)
  have hInv : 1 / (p + 1) ≤ 1 / 2 :=
    div_le_div_of_nonneg_left zero_le_one (by norm_num) (by linarith)
  apply mul_nonneg (by unfold clipPriceBase; positivity)
  dsimp only [L]
  nlinarith only [hLog, hInv, sq_nonneg (Real.log (b p))]

theorem outerClipPrice_le_chord {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    outerClipPrice p ≤ 17 / 100 - (73 / 400) * (p - 1) := by
  have hA : 0 ≤ (9 / 5 - p) / (4 / 5) := div_nonneg (sub_nonneg.mpr hP) (by norm_num)
  have hB : 0 ≤ (p - 1) / (4 / 5) := div_nonneg (sub_nonneg.mpr hp) (by norm_num)
  have h := clipPriceBase_convex.2
    (show (1 : ℝ) ∈ Icc 1 (9 / 5) by constructor <;> norm_num)
    (show (9 / 5 : ℝ) ∈ Icc 1 (9 / 5) by constructor <;> norm_num) hA hB (by ring)
  simp only [smul_eq_mul, mul_one] at h
  rw [show (9 / 5 - p) / (4 / 5) + (p - 1) / (4 / 5) * (9 / 5) = p by ring] at h
  have hC : 1 + 2 * p / (7 * (p + 2)) ≤ 151 / 133 := by
    have hRat : 2 * p / (7 * (p + 2)) ≤ 18 / 133 := by
      apply (div_le_iff₀ (by positivity : 0 < 7 * (p + 2))).mpr
      linarith only [hP]
    linarith only [hRat]
  have hM : outerClipPrice p ≤ (151 / 133) * clipPriceBase p := by
    unfold outerClipPrice
    rw [← clipPriceBase_eq hp]
    exact (mul_le_mul_of_nonneg_left hC (by unfold clipPriceBase; positivity)).trans_eq (mul_comm _ _)
  have h1 : (151 / 133) * clipPriceBase 1 ≤ 17 / 100 := by
    rw [clipPriceBase_eq le_rfl, Real.rpow_neg (by norm_num), Real.rpow_one]
    norm_num
  have h2 : (151 / 133) * clipPriceBase (9 / 5) ≤ 3 / 125 := by
    rw [clipPriceBase_eq (by norm_num), show (7 / 4 : ℝ) * (9 / 5 + 1) = 49 / 10 by norm_num]
    have hR : (49 / 10 : ℝ) ^ (-(9 / 5 : ℝ)) < 29 / 500 := by
      convert fifth_rpow_upper (k := 9) (b := 49 / 10) (x := 29 / 500)
        (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
    norm_num only [show (9 / 5 : ℝ) + 1 = 14 / 5 by norm_num]
    linarith only [hR]
  have h' := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 151 / 133)
  have h₁ := mul_le_mul_of_nonneg_left h1 hA
  have h₂ := mul_le_mul_of_nonneg_left h2 hB
  linarith only [hM, h', h₁, h₂]

theorem outerUnit_margin {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    outerUnitValue p + outerClipPrice p + (4452 / 12500) * (9 / 5 - p) + 33 / 1000 < 0 := by
  let t := p - 1
  have ht : 0 ≤ t := sub_nonneg.mpr hp
  have ht' : t ≤ 4 / 5 := by dsimp only [t]; linarith
  have h1 : t ≤ 1 := ht'.trans (by norm_num)
  have h₂ : t ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ ht h1 2
  have h₃ : t ^ 3 ≤ 1 := by simpa using pow_le_pow_left₀ ht h1 3
  have hZ := (pureZ_B2_upper hp).le.trans (add_le_add_right
    (mul_le_mul_of_nonneg_right (two_neg_rpow_chord hp hP)
      (show 0 ≤ 1 + p / 4 + p * (p + 1) / 48 by positivity)) p)
  have hU := mul_le_mul_of_nonneg_left hZ
    (show 0 ≤ (81 / 100) * (p - 1) by positivity)
  have hQ := mul_le_mul_of_nonneg_left (pureQ_lower hp hP).le (by norm_num : (0 : ℝ) ≤ 6 / 25)
  have hT := outerClipPrice_le_chord hp hP
  have hPoly : 0 ≤ -(28701 / 6400000) * t ^ 3 - (1997379 / 32000000) * t ^ 2 +
      (27624567 / 80000000) * t + 28087067 / 100000000 := by
    linarith only [ht, h₂, h₃]
  have hBound := mul_nonneg (sub_nonneg.mpr ht') hPoly
  unfold outerUnitValue
  change (81 / 100) * t * pureZ p - (6 / 25) * pureQ p - 19 / 100 +
    outerClipPrice p + (4452 / 12500) * (9 / 5 - p) + 33 / 1000 < 0
  have hE : p = 1 + t := by dsimp only [t]; ring
  rw [hE] at hU hQ hT ⊢
  nlinarith only [hU, hQ, hT, hBound]

theorem pureK_unit_bound {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    (p - 15 / 8) * pureZ p - (12 / 25) * pureQ p + (12 / 25) * p + 15 / 8 ≤ 4 / 25 := by
  have hR : (1 / 4 : ℝ) ≤ (2 : ℝ) ^ (-p) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show -(2 : ℝ) ≤ -p by linarith)
    rw [Real.rpow_neg (by norm_num), Real.rpow_two] at h
    convert h using 1 <;> norm_num
  have hZ := (add_le_add_right
    (mul_le_mul_of_nonneg_right hR (show 0 ≤ 1 + p / 4 by positivity)) p).trans
      (pureZ_trapezoid_lower hp).le
  have hZ' := mul_le_mul_of_nonpos_left hZ (show p - 15 / 8 ≤ 0 by linarith)
  have hQ := mul_le_mul_of_nonneg_left (pureQ_lower hp hP).le (by norm_num : (0 : ℝ) ≤ 12 / 25)
  have hProd := mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hP)
  nlinarith only [hZ', hQ, hProd, hp, hP]

end ACS12.GammaMeasure

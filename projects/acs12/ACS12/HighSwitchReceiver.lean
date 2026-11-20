import ACS12.HighEnvelopeExponent

/-! The complete correlated moving-switch receiver on the formal containing rectangle. -/
namespace ACS12.Pressure

open Set

private theorem weighted_strict_average {a b x y X Y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (hx : x < X) (hy : y < Y) :
    a * x + b * y < a * X + b * Y := by
  rcases ha.eq_or_lt with h | h
  · have ha₀ : a = 0 := h.symm
    have hb₁ : b = 1 := by linarith only [hab,ha₀]
    simpa only [ha₀,hb₁,zero_mul,zero_add,one_mul] using hy
  · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hx h) (mul_le_mul_of_nonneg_left hy.le hb)

theorem highPressureSwitch_gap {p : ℝ} (hp : 2 ≤ p) (hP : p ≤ 4) :
    highPressureEnvelope p (highPressureSwitch p) ≤ highUnitAffine p - 1 / 2560 := by
  let b := (p - 2) / 2
  let a := 1 - b
  let R₂ : ℝ := 4213 / 1920
  let R₄ : ℝ := 549 / 320
  let R₀ := highPressureSwitch p
  have hb : 0 ≤ b := by unfold b; linarith only [hp]
  have hb₁ : b ≤ 1 := by unfold b; linarith only [hP]
  have ha : 0 ≤ a := sub_nonneg.mpr hb₁
  have hab : a + b = 1 := by unfold a; ring
  have hpE : a * 2 + b * 4 = p := by unfold a b; ring
  have hRE : a * R₂ + b * R₄ = R₀ := by unfold a b R₂ R₄ R₀ highPressureSwitch; ring
  have hR₀ : 0 < R₀ := by unfold R₀ highPressureSwitch; linarith only [hP]
  have hR₀U : R₀ ≤ 33 / 10 := by unfold R₀ highPressureSwitch; linarith only [hp]
  have hC := (highPressureEnvelope_convex_exponent hR₀ hR₀U).2
    (show (2 : ℝ) ∈ Icc 2 4 by norm_num) (show (4 : ℝ) ∈ Icc 2 4 by norm_num) ha hb hab
  simp only [smul_eq_mul,hpE] at hC
  have hC₂ := (highPressureEnvelope_convex_radial (p := 2) (by norm_num)).2
    (show R₂ ∈ Ioi 0 by norm_num [R₂]) (show R₄ ∈ Ioi 0 by norm_num [R₄]) ha hb hab
  have hC₄ := (highPressureEnvelope_convex_radial (p := 4) (by norm_num)).2
    (show R₂ ∈ Ioi 0 by norm_num [R₂]) (show R₄ ∈ Ioi 0 by norm_num [R₄]) ha hb hab
  simp only [smul_eq_mul,hRE] at hC₂ hC₄
  have hBilinear :
      highPressureEnvelope p R₀ ≤
        a ^ 2 * highPressureEnvelope 2 R₂ + b ^ 2 * highPressureEnvelope 4 R₄ +
          a * b * (highPressureEnvelope 2 R₄ + highPressureEnvelope 4 R₂) := by
    have h₂ := mul_le_mul_of_nonneg_left hC₂ ha
    have h₄ := mul_le_mul_of_nonneg_left hC₄ hb
    nlinarith only [hC,h₂,h₄]
  have hEndpoint₂ := mul_le_mul_of_nonneg_left highSwitch_corner_two_two.le (sq_nonneg a)
  have hEndpoint₄ := mul_le_mul_of_nonneg_left highSwitch_corner_four_four.le (sq_nonneg b)
  have hCross := mul_le_mul_of_nonneg_left
    (add_le_add highSwitch_corner_two_four.le highSwitch_corner_four_two.le) (mul_nonneg ha hb)
  have hBound : highPressureEnvelope p R₀ ≤
      a ^ 2 * (highUnitAffine 2 - 1 / 80) + b ^ 2 * (highUnitAffine 4 - 1 / 80) + a * b * (7 / 3) := by
    change a ^ 2 * highPressureEnvelope 2 R₂ ≤ _ at hEndpoint₂
    change b ^ 2 * highPressureEnvelope 4 R₄ ≤ _ at hEndpoint₄
    change a * b * (highPressureEnvelope 2 R₄ + highPressureEnvelope 4 R₂) ≤ _ at hCross
    nlinarith only [hBilinear,hEndpoint₂,hEndpoint₄,hCross]
  have hQuarter : a * b ≤ (1 / 4 : ℝ) := by
    have h := sq_nonneg (a - b)
    nlinarith only [h,congrArg (fun z : ℝ => z ^ 2) hab]
  have hPay :
      a ^ 2 * (highUnitAffine 2 - 1 / 80) + b ^ 2 * (highUnitAffine 4 - 1 / 80) + a * b * (7 / 3) ≤
        highUnitAffine p - 1 / 2560 := by
    have hp' : p = 2 + 2 * b := by unfold b; ring
    unfold highUnitAffine
    rw [hp']
    have haE : a = 1 - b := rfl
    rw [haE] at hQuarter ⊢
    nlinarith only [hQuarter]
  exact hBound.trans hPay

theorem highPressureEnvelope_upper_boundary {p : ℝ} (hp : 2 ≤ p) (hP : p ≤ 4) :
    highPressureEnvelope p (33 / 10) < (33 / 10) - (11 - p) / 10 := by
  let b := (p - 2) / 2
  let a := 1 - b
  have hb : 0 ≤ b := by unfold b; linarith only [hp]
  have ha : 0 ≤ a := by unfold a b; linarith only [hP]
  have hab : a + b = 1 := by unfold a; ring
  have hpE : a * 2 + b * 4 = p := by unfold a b; ring
  have h := (highPressureEnvelope_convex_exponent (R := 33 / 10) (by norm_num) le_rfl).2
    (show (2 : ℝ) ∈ Icc 2 4 by norm_num) (show (4 : ℝ) ∈ Icc 2 4 by norm_num) ha hb hab
  simp only [smul_eq_mul,hpE] at h
  have hPay := weighted_strict_average ha hb hab highSwitch_boundary_two highSwitch_boundary_four
  have hEq : a * ((33 / 10) - (11 - 2) / 10) + b * ((33 / 10) - (11 - 4) / 10) =
      (33 / 10) - (11 - p) / 10 := by unfold a b; ring
  exact h.trans_lt (hPay.trans_eq hEq)

theorem highPressureEnvelope_lt_lower {p R : ℝ} (hp : 2 ≤ p) (hP : p ≤ 4)
    (hR : 1 ≤ R) (hRU : R ≤ 33 / 10) :
    highPressureEnvelope p R < max (highUnitAffine p) (R - (11 - p) / 10) := by
  let R₀ := highPressureSwitch p
  let R₁ : ℝ := 33 / 10
  let J := (11 - p) / 10
  have hR₀ : 0 < R₀ := by unfold R₀ highPressureSwitch; linarith only [hP]
  have hR₀R₁ : R₀ < R₁ := by unfold R₀ R₁ highPressureSwitch; linarith only [hp]
  have hSwitch := (highPressureSwitch_gap hp hP).trans_lt (sub_lt_self _ (by norm_num : (0 : ℝ) < 1 / 2560))
  change highPressureEnvelope p R₀ < highUnitAffine p at hSwitch
  have hMeet : R₀ - J = highUnitAffine p := by unfold R₀ J highPressureSwitch highUnitAffine; ring
  rcases le_or_gt R R₀ with h | h
  · have hM := highPressureEnvelope_mono_radial hp (show R ∈ Ioi 0 from zero_lt_one.trans_le hR) hR₀ h
    exact (hM.trans_lt hSwitch).trans_le (le_max_left _ _)
  · let b := (R - R₀) / (R₁ - R₀)
    let a := 1 - b
    have hDen : 0 < R₁ - R₀ := sub_pos.mpr hR₀R₁
    have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr h.le) hDen.le
    have hb₁ : b ≤ 1 := (div_le_one hDen).mpr (by unfold R₁; linarith only [hRU])
    have ha : 0 ≤ a := sub_nonneg.mpr hb₁
    have hab : a + b = 1 := by unfold a; ring
    have hRE : a * R₀ + b * R₁ = R := by unfold a b; field_simp [hDen.ne']; ring
    have hC := (highPressureEnvelope_convex_radial hp).2 hR₀
      (show R₁ ∈ Ioi 0 by norm_num [R₁]) ha hb hab
    simp only [smul_eq_mul,hRE] at hC
    have hLeft : highPressureEnvelope p R₀ < R₀ - J := by rwa [hMeet]
    have hRight : highPressureEnvelope p R₁ < R₁ - J := highPressureEnvelope_upper_boundary hp hP
    have hPay := weighted_strict_average ha hb hab hLeft hRight
    have hEq : a * (R₀ - J) + b * (R₁ - J) = R - J := by
      nlinarith only [hRE,congrArg (· * J) hab]
    exact (hC.trans_lt (hPay.trans_eq hEq)).trans_le (le_max_right _ _)

end ACS12.Pressure

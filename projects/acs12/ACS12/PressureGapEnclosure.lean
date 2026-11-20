import ACS12.PressureUnitD
import ACS12.PressureGapRatio

/-! The same full two-gap enclosure throughout the actual physical band. -/
namespace ACS12.Pressure

open Set

noncomputable def sourceGapTail (v : ℝ) : ℝ := 1 / 27 - (487 / (27000 * pressureContrastCap)) * v

noncomputable def sourceGapLower (z : ℝ) : ℝ :=
  Real.exp (-(5 / 14) * ((9 / 5) * z)) * canonicalGapLower ((9 / 5) * z)

noncomputable def sourceGapUpper (z : ℝ) : ℝ :=
  Real.exp (-z) * canonicalGapUpper ((9 / 5) * z)

theorem pressureContrastCap_pos : 0 < pressureContrastCap := by
  unfold pressureContrastCap
  exact Real.log_pos (by norm_num)

theorem sourceGapTail_bounds {v : ℝ} (hv : 0 ≤ v) (hL : v ≤ pressureContrastCap) :
    0 < sourceGapTail v ∧ sourceGapTail v ≤ 1 / 27 := by
  have hC : 0 < 487 / (27000 * pressureContrastCap) := by have := pressureContrastCap_pos; positivity
  have hE : 487 / (27000 * pressureContrastCap) * pressureContrastCap = (487 / 27000 : ℝ) := by
    field_simp [pressureContrastCap_pos.ne']
  have hU := mul_le_mul_of_nonneg_left hL hC.le
  have hLo := mul_nonneg hC.le hv
  unfold sourceGapTail
  constructor <;> linarith only [hU,hLo,hE]

private theorem sourceGapLower_pos {z : ℝ} (hz : 0 < z) : 0 < sourceGapLower z := by
  unfold sourceGapLower canonicalGapLower
  positivity

private theorem sourceGapUpper_eq {z : ℝ} (hz : 0 < z) (hL : (9 / 5) * z ≤ pressureContrastCap) :
    sourceGapUpper z = sourceGapLower z * gapRatio ((9 / 5) * z) := by
  let v := (9 / 5 : ℝ) * z
  have hv : 0 < v := by unfold v; positivity
  have hv₂ : v ^ 2 ≤ 2 := by
    have hB : v ≤ 111 / 80 := hL.trans (pressureContrastCap_lt.le.trans_eq (by unfold canonicalV; rfl))
    exact (pow_le_pow_left₀ hv.le hB 2).trans (by norm_num)
  have hD : 1 - v ^ 2 / 90 ≠ 0 := ne_of_gt (by linarith only [hv₂])
  have hB : 1 + v ^ 2 / 10 ≠ 0 := by positivity
  have hQ : 1 + (887 / 3920 : ℝ) * v ^ 2 ≠ 0 := by positivity
  have hE : Real.exp (-(5 / 14) * v) * Real.exp (-(25 / 126) * v) = Real.exp (-z) := by
    rw [← Real.exp_add]
    congr 1
    unfold v
    ring
  change Real.exp (-z) * ((5 / 42) * v ^ 2 * (1 + (37877 / 1000188 - 1 / 90) * v ^ 2) / (1 - v ^ 2 / 90)) =
    (Real.exp (-(5 / 14) * v) * ((45 / 392) * v ^ 2 * (1 + v ^ 2 / 10) / (1 + (887 / 3920) * v ^ 2))) *
      ((28 / 27) * Real.exp (-(25 / 126) * v) *
        ((1 + (37877 / 1000188 - 1 / 90) * v ^ 2) * (1 + (887 / 3920) * v ^ 2) /
          ((1 - (1 / 90) * v ^ 2) * (1 + (1 / 10) * v ^ 2))))
  let C := (45 / 392 : ℝ) * v ^ 2 * (1 + v ^ 2 / 10) / (1 + (887 / 3920) * v ^ 2)
  let D := (5 / 42 : ℝ) * v ^ 2 * (1 + (37877 / 1000188 - 1 / 90) * v ^ 2) / (1 - v ^ 2 / 90)
  let R := ((1 + (37877 / 1000188 - 1 / 90 : ℝ) * v ^ 2) * (1 + (887 / 3920) * v ^ 2)) /
    ((1 - (1 / 90) * v ^ 2) * (1 + (1 / 10) * v ^ 2))
  change Real.exp (-z) * D =
    (Real.exp (-(5 / 14) * v) * C) * ((28 / 27) * Real.exp (-(25 / 126) * v) * R)
  have hRat : D = C * ((28 / 27) * R) := by
    unfold D C R
    rw [show (1 / 90 : ℝ) * v ^ 2 = v ^ 2 / 90 by ring,show (1 / 10 : ℝ) * v ^ 2 = v ^ 2 / 10 by ring]
    have h90 : (90 : ℝ) - v ^ 2 ≠ 0 := ne_of_gt (by linarith only [hv₂])
    have h10 : (10 : ℝ) + v ^ 2 ≠ 0 := by positivity
    have h3920 : (3920 : ℝ) + 887 * v ^ 2 ≠ 0 := by positivity
    field_simp [hD,hB,hQ,h90,h10,h3920]
    ring
  calc
    _ = (Real.exp (-(5 / 14) * v) * Real.exp (-(25 / 126) * v)) * D := by rw [hE]
    _ = _ := by rw [hRat]; ring

theorem pressureUnitGap_enclosure {p z : ℝ} (hp : 9 / 5 ≤ p) (hp₂ : p ≤ 2)
    (hz : 0 < z) (hL : (9 / 5) * z ≤ pressureContrastCap) :
    0 < sourceGapLower z ∧ sourceGapLower z ≤ unitGapG p z ∧
      unitGapD p z ≤ sourceGapLower z * (1 + sourceGapTail ((9 / 5) * z)) := by
  let v := (9 / 5 : ℝ) * z
  have hv : 0 < v := by unfold v; positivity
  have hV : v ≤ 111 / 80 := hL.trans pressureContrastCap_lt.le
  have hv₂ : v ^ 2 ≤ 2 := (pow_le_pow_left₀ hv.le hV 2).trans (by norm_num)
  have hZ : z ≤ 4 / 5 := by unfold v at hV; linarith only [hV]
  have hD := unitGapD_anti hz hZ
  have hG := unitGapG_mono (by norm_num : (0 : ℝ) < 9 / 5) hp hz.le
  have hG₀ : unitGapG (9 / 5) z = Real.exp (-(5 / 14) * v) * canonicalGapG v := by
    unfold unitGapG canonicalGapG v
    norm_num
    ring_nf
  have hD₀ : unitGapD (9 / 5) z = Real.exp (-z) * canonicalGapD v := by
    unfold unitGapD canonicalGapD v
    norm_num
    ring_nf
  have hR := gapRatio_le_chord hv.le hL
  have hRT : gapRatio v ≤ 1 + sourceGapTail v := by unfold sourceGapTail; linarith only [hR]
  have hU := sourceGapLower_pos hz
  refine ⟨hU,?_,?_⟩
  · apply le_trans _ hG
    rw [hG₀]
    exact mul_le_mul_of_nonneg_left (canonicalGapLower_lt hv hv₂).le (Real.exp_pos _).le
  · apply (hD ⟨le_rfl,by norm_num⟩ ⟨hp,hp₂⟩ hp).trans
    change unitGapD (9 / 5) z ≤ _
    rw [hD₀]
    have h := mul_le_mul_of_nonneg_left (canonicalGapD_le_upper hv.le hv₂) (Real.exp_pos (-z)).le
    change _ ≤ sourceGapUpper z at h
    rw [sourceGapUpper_eq hz hL] at h
    exact h.trans (mul_le_mul_of_nonneg_left hRT hU.le)

theorem pressureUnitGap_difference_le {p z : ℝ} (hp : 9 / 5 ≤ p) (hp₂ : p ≤ 2)
    (hz : 0 < z) (hL : (9 / 5) * z ≤ pressureContrastCap) :
    unitGapD p z - unitGapG p z ≤ (27 / 1960) * z ^ 2 := by
  let v := (9 / 5 : ℝ) * z
  have hv : 0 < v := by unfold v; positivity
  obtain ⟨hU,hG,hD⟩ := pressureUnitGap_enclosure hp hp₂ hz hL
  have hC := (sourceGapTail_bounds hv.le hL).2
  have hE : sourceGapLower z ≤ (45 / 392) * v ^ 2 := by
    have hExp : Real.exp (-(5 / 14) * v) ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hv.le)
    have hR : (1 + v ^ 2 / 10) / (1 + (887 / 3920) * v ^ 2) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      nlinarith only [sq_nonneg v]
    change Real.exp (-(5 / 14) * v) * ((45 / 392) * v ^ 2 * (1 + v ^ 2 / 10) /
      (1 + (887 / 3920) * v ^ 2)) ≤ _
    rw [mul_div_assoc]
    have hF := mul_le_of_le_one_right (show 0 ≤ (45 / 392 : ℝ) * v ^ 2 by positivity) hR
    exact (mul_le_mul_of_nonneg_left hF (Real.exp_pos _).le).trans
      (mul_le_of_le_one_left (by positivity) hExp)
  have h := sub_le_sub hD hG
  have hPay : sourceGapLower z * sourceGapTail v ≤ (45 / 392) * v ^ 2 * (1 / 27) :=
    mul_le_mul hE hC (sourceGapTail_bounds hv.le hL).1.le (by positivity)
  have hEq : (45 / 392 : ℝ) * v ^ 2 * (1 / 27) = (27 / 1960) * z ^ 2 := by unfold v; ring
  rw [hEq] at hPay
  change _ ≤ sourceGapLower z * (1 + sourceGapTail v) - sourceGapLower z at h
  nlinarith only [h,hPay]

end ACS12.Pressure


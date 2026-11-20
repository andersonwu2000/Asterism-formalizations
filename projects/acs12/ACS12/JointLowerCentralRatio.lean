import ACS12.JointLowerNativeStream

/-! Signed derivative estimates for every omitted central correction in the lower native tail. -/
namespace ACS12.GammaMeasure

open Set

private theorem centralRatio_lower_at {q₀ q x m J K : ℝ}
    (hq₀ : 4 ≤ q₀) (hq : q₀ ≤ q) (hx : 0 < x) (hxU : x ≤ 8 / 23)
    (hm : 0 < m) (hm₁ : m ≤ 1) (hJ : 5 / 2 ≤ J)
    (hJx : (1 - x) / m = J * x)
    (hL : K * (q₀ - 1 - (q₀ + 1) * (2 / 7)) ≤
      2 * (q₀ + 1) * (5 / 7) * (q₀ - 1 - (q₀ + 2) * (2 / 7)))
    (hR : ∀ x ∈ Icc (2 / 7 : ℝ) (8 / 23),
      K * (q₀ - 1 - (q₀ + 1) * x) ≤ 5 * (q₀ + 1) * x * (q₀ - 1 - (q₀ + 2) * x)) :
    K ≤ 2 * (q + 1) * ((1 - x) / m) * ((q - 1 - (q + 2) * x) / (q - 1 - (q + 1) * x)) := by
  let D (v t : ℝ) := v - 1 - (v + 1) * t
  have hS (v t : ℝ) (hv : 4 ≤ v) (ht : t ≤ 8 / 23) : 0 < D v t := by
    unfold D
    nlinarith only [mul_nonneg (sub_nonneg.mpr hv) (show 0 ≤ 1 - t by linarith only [ht]),ht]
  have hN (v t : ℝ) (hv : 4 ≤ v) (ht : t ≤ 8 / 23) : 0 < v - 1 - (v + 2) * t := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hv) (show 0 ≤ 1 - t by linarith only [ht]),ht]
  have hEq (v t : ℝ) (hD : 0 < D v t) :
      (v - 1 - (v + 2) * t) / D v t = 1 - t / D v t := by
    rw [show v - 1 - (v + 2) * t = D v t - t by unfold D; ring,
      sub_div,div_self hD.ne']
  have hDQ := hS q x (hq₀.trans hq) hxU
  have hD₀ := hS q₀ x hq₀ hxU
  have hRat : (q₀ - 1 - (q₀ + 2) * x) / D q₀ x ≤ (q - 1 - (q + 2) * x) / D q x := by
    rw [hEq _ _ hD₀,hEq _ _ hDQ]
    apply sub_le_sub_left
    apply div_le_div_of_nonneg_left hx.le hD₀
    unfold D
    nlinarith only [mul_nonneg (sub_nonneg.mpr hq) (show 0 ≤ 1 - x by linarith only [hxU])]
  have hMx : 0 < (1 - x) / m := div_pos (by linarith only [hxU]) hm
  have hQpos : 0 ≤ 2 * (q₀ + 1) := by linarith only [hq₀]
  have hRat₀ : 0 ≤ (q₀ - 1 - (q₀ + 2) * x) / D q₀ x :=
    (div_pos (hN _ _ hq₀ hxU) hD₀).le
  calc
    K ≤ 2 * (q₀ + 1) * ((1 - x) / m) * ((q₀ - 1 - (q₀ + 2) * x) / D q₀ x) := by
      by_cases hCut : x ≤ 2 / 7
      · have hD₂ := hS q₀ (2 / 7) hq₀ (by norm_num)
        have hRat₂ : (q₀ - 1 - (q₀ + 2) * (2 / 7)) / D q₀ (2 / 7) ≤
            (q₀ - 1 - (q₀ + 2) * x) / D q₀ x := by
          rw [hEq _ _ hD₂,hEq _ _ hD₀]
          apply sub_le_sub_left
          have hDM : D q₀ (2 / 7) ≤ D q₀ x := by
            unfold D
            have h := mul_le_mul_of_nonneg_left hCut (show 0 ≤ q₀ + 1 by linarith only [hq₀])
            linarith only [h]
          exact (div_le_div_of_nonneg_right hCut hD₀.le).trans
            (div_le_div_of_nonneg_left (by norm_num) hD₂ hDM)
        have hMX : 5 / 7 ≤ (1 - x) / m := by
          apply (le_div_iff₀ hm).mpr
          linarith only [hCut,hm₁]
        calc
          K ≤ (2 * (q₀ + 1) * (5 / 7)) *
              ((q₀ - 1 - (q₀ + 2) * (2 / 7)) / D q₀ (2 / 7)) := by
            rw [← mul_div_assoc]
            exact (le_div_iff₀ hD₂).mpr hL
          _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hMX hQpos) hRat₂
            (div_nonneg (hN _ _ hq₀ (by norm_num)).le hD₂.le) (mul_nonneg hQpos hMx.le)
      · rw [hJx,← mul_div_assoc]
        apply (le_div_iff₀ hD₀).mpr
        have h := hR x ⟨le_of_not_ge hCut,hxU⟩
        have hJx' := mul_le_mul_of_nonneg_right hJ hx.le
        have h' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJx' hQpos) (hN _ _ hq₀ hxU).le
        unfold D
        nlinarith only [h,h']
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right (by linarith only [hq]) hMx.le) hRat
      hRat₀ (mul_nonneg (by linarith only [hq₀,hq]) hMx.le)

theorem centralOddRatio_lower {q x m J : ℝ} (hq : 4 ≤ q) (hx : 0 < x) (hxU : x ≤ 8 / 23)
    (hm : 0 < m) (hm₁ : m ≤ 1) (hJ : 5 / 2 ≤ J) (hJx : (1 - x) / m = J * x) :
    (450 / 77 : ℝ) ≤ 2 * (q + 1) * ((1 - x) / m) *
      ((q - 1 - (q + 2) * x) / (q - 1 - (q + 1) * x)) := by
  apply centralRatio_lower_at (q₀ := 4) (J := J) le_rfl hq hx hxU hm hm₁ hJ hJx
  · norm_num
  · intro x hx
    have h := mul_nonneg (sub_nonneg.mpr hx.1)
      (show 0 ≤ 4725 / 77 - 150 * x by linarith only [hx.2])
    nlinarith only [h]

theorem centralEvenRatio_lower {q x m J : ℝ} (hq : 5 ≤ q) (hx : 0 < x) (hxU : x ≤ 8 / 23)
    (hm : 0 < m) (hm₁ : m ≤ 1) (hJ : 5 / 2 ≤ J) (hJx : (1 - x) / m = J * x) :
    (15 / 2 : ℝ) ≤ 2 * (q + 1) * ((1 - x) / m) *
      ((q - 1 - (q + 2) * x) / (q - 1 - (q + 1) * x)) := by
  apply centralRatio_lower_at (q₀ := 5) (J := J) (by norm_num) hq hx hxU hm hm₁ hJ hJx
  · norm_num
  · intro x hx
    have h := mul_nonneg (sub_nonneg.mpr hx.1)
      (show 0 ≤ 105 - 210 * x by linarith only [hx.2])
    nlinarith only [h]

end ACS12.GammaMeasure


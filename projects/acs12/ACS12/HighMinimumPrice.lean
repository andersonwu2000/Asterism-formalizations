import ACS12.HighOccupiedCoefficient

/-! The whole occupied-neighbor Gamma price under its original mass and gap caps. -/
namespace ACS12.Pressure

open Set

theorem highOccupied_ratio_lt {p κ : ℝ} (hp : 2 ≤ p) (hκ : 0 < κ) (hκP : κ ≤ p + 1) :
    p * κ / (1 + κ ^ (1 / (p + 1))) ^ (p + 1) < 5 / 12 := by
  let ν := p + 1
  let v := κ ^ (1 / ν)
  let u := ν ^ (1 / ν)
  have hp₀ : 0 < p := by linarith only [hp]
  have hν : 0 < ν := by unfold ν; linarith only [hp]
  have hv : 0 < v := Real.rpow_pos_of_pos hκ _
  have hu : 0 < u := Real.rpow_pos_of_pos hν _
  have hvu : v ≤ u := Real.rpow_le_rpow hκ.le hκP (by positivity : 0 ≤ 1 / ν)
  have hFrac : v / (1 + v) ≤ u / (1 + u) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [hvu]
  have hPow := Real.rpow_le_rpow (div_nonneg hv.le (by positivity)) hFrac hν.le
  have hEval (x : ℝ) (hx : 0 < x) :
      (x ^ (1 / ν) / (1 + x ^ (1 / ν))) ^ ν = x / (1 + x ^ (1 / ν)) ^ ν := by
    rw [Real.div_rpow (Real.rpow_pos_of_pos hx _).le (by positivity),
      ← Real.rpow_mul hx.le,one_div_mul_cancel hν.ne',Real.rpow_one]
  change (κ ^ (1 / ν) / (1 + κ ^ (1 / ν))) ^ ν ≤ (ν ^ (1 / ν) / (1 + ν ^ (1 / ν))) ^ ν at hPow
  rw [hEval κ hκ,hEval ν hν] at hPow
  have h := mul_le_mul_of_nonneg_left hPow hp₀.le
  have hC := occupiedCoefficient_lt (ν := ν) (by unfold ν; linarith only [hp])
  unfold occupiedCoefficient at hC
  have hνE : ν - 1 = p := by unfold ν; ring
  rw [hνE] at hC
  change p * κ / (1 + κ ^ (1 / ν)) ^ ν < 5 / 12
  have hLe : p * κ / (1 + κ ^ (1 / ν)) ^ ν ≤ p * ν / (1 + ν ^ (1 / ν)) ^ ν := by
    simpa only [mul_div_assoc] using h
  exact hLe.trans_lt hC

noncomputable def highMinimumUnitPrice (p y : ℝ) : ℝ :=
  (p + 5 / 12) * y + (2 + y / 2) ^ (-p)

theorem highMinimumNeighborPrice_le_unit {p a r g t : ℝ} (hp : 2 ≤ p)
    (ha : 0 < a) (hr : a ≤ r) (hRatio : r / a ≤ p + 1)
    (ht : 0 < t) (hGap : t * (r / a) ^ (1 / (p + 1)) ≤ g) :
    highMinimumNeighborPrice p a r g t ≤ highMinimumUnitPrice p (a / t) := by
  let ν := p + 1
  let κ := r / a
  let u := κ ^ (1 / ν)
  let y := a / t
  have hp₀ : 0 < p := by linarith only [hp]
  have hν : 0 < ν := by unfold ν; positivity
  have hr₀ : 0 < r := ha.trans_le hr
  have hκ : 0 < κ := div_pos hr₀ ha
  have hκ₁ : 1 ≤ κ := (one_le_div ha).mpr hr
  have hu : 0 < u := Real.rpow_pos_of_pos hκ _
  have hu₁ : 1 ≤ u := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow zero_le_one hκ₁ (show 0 ≤ 1 / ν by positivity)
  have hy : 0 < y := div_pos ha ht
  have hR : r = κ * a := by unfold κ; rw [div_mul_cancel₀ _ ha.ne']
  have hG : t * (1 + u) ≤ t + g := by
    change t * u ≤ g at hGap
    linarith only [hGap]
  have hB : t * (2 + y / 2) ≤ t + g + r / 2 := by
    have hPay : t * y = a := by unfold y; field_simp [ht.ne']
    have hMinGap : t ≤ g := by
      have h := mul_le_mul_of_nonneg_left hu₁ ht.le
      change t * u ≤ g at hGap
      linarith only [h,hGap]
    nlinarith only [hPay,hMinGap,hr]
  have hTerm (q b : ℝ) (hb : 0 < b) :
      t ^ p * (t * b) ^ (-q) = (t ^ p * t ^ (-q)) * b ^ (-q) := by
    rw [Real.mul_rpow ht.le hb.le]
    ring
  have hPowers : t ^ p * t ^ (-ν) = t⁻¹ := by
    rw [← Real.rpow_add ht,show p + -ν = -1 by unfold ν; ring,Real.rpow_neg_one]
  have hSecond :
      p * r * t ^ p * (t + g) ^ (-(p + 1)) ≤
        (p * κ / (1 + u) ^ ν) * y := by
    have hT := Real.rpow_le_rpow_of_nonpos (show 0 < t * (1 + u) by positivity) hG (neg_nonpos.mpr hν.le)
    have h := mul_le_mul_of_nonneg_left hT (show 0 ≤ p * r * t ^ p by positivity)
    change p * r * t ^ p * (t + g) ^ (-ν) ≤ _
    calc
      _ ≤ p * r * t ^ p * (t * (1 + u)) ^ (-ν) := h
      _ = p * r * ((t ^ p * t ^ (-ν)) * (1 + u) ^ (-ν)) := by
        rw [← hTerm ν (1 + u) (by positivity)]
        ring
      _ = _ := by rw [hPowers,Real.rpow_neg (by positivity : 0 ≤ 1 + u),hR]; unfold y; ring
  have hThird :
      t ^ p * (t + g + r / 2) ^ (-p) ≤ (2 + y / 2) ^ (-p) := by
    have hT := Real.rpow_le_rpow_of_nonpos (show 0 < t * (2 + y / 2) by positivity) hB (neg_nonpos.mpr hp₀.le)
    have h := mul_le_mul_of_nonneg_left hT (Real.rpow_nonneg ht.le p)
    calc
      _ ≤ t ^ p * (t * (2 + y / 2)) ^ (-p) := h
      _ = _ := by
        rw [hTerm p (2 + y / 2) (by positivity),← Real.rpow_add ht,add_neg_cancel,Real.rpow_zero,one_mul]
  have hCoef := highOccupied_ratio_lt hp hκ hRatio
  change p * κ / (1 + u) ^ ν < 5 / 12 at hCoef
  have hSecond' := hSecond.trans (mul_le_mul_of_nonneg_right hCoef.le hy.le)
  unfold highMinimumNeighborPrice highMinimumUnitPrice
  change p * a / t + p * r * t ^ p * (t + g) ^ (-(p + 1)) +
    t ^ p * (t + g + r / 2) ^ (-p) ≤ (p + 5 / 12) * y + (2 + y / 2) ^ (-p)
  have hA : p * a / t = p * y := by unfold y; ring
  rw [hA]
  linarith only [hSecond',hThird]

end ACS12.Pressure

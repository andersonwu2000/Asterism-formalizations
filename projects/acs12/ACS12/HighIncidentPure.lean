import ACS12.JointFarMotion

/-! The full reference A/B ratio needed at the original high-source entrance. -/
namespace ACS12.GammaMeasure

open Set

private theorem incident_log_gt {t : ℝ} (ht : 0 < t) :
    2 / (2 * t + 1) < Real.log ((1 + t) / t) := by
  let z := (2 * t + 1)⁻¹
  have hz : 0 < z := inv_pos.mpr (by positivity)
  have hz₁ : z < 1 := (inv_lt_one₀ (by positivity)).mpr (by linarith only [ht])
  have h := Real.sum_range_le_log_div hz.le hz₁ 2
  have hE : (1 + z) / (1 - z) = (1 + t) / t := by
    unfold z
    field_simp [ht.ne',show 2 * t + 1 ≠ 0 by positivity]
    ring
  rw [hE] at h
  norm_num [Finset.sum_range_succ] at h
  have hZ := pow_pos hz 3
  change 2 * z < _
  linarith only [h,hZ]

theorem highIncident_purePeano_ratio {p t : ℝ} (hp : 2 ≤ p) (hp₄ : p ≤ 4)
    (ht : 0 < t) (htU : t ≤ 5 / 8) :
    t * purePeanoB p 1 t < ((p + 4) / 2) * purePeanoA p 1 t := by
  let v := 1 + t
  let x := v / t
  let a := 1 / (2 * v)
  let b := 1 / 2 + 2 / v
  let c := 2 + t
  let L := Real.log x
  let P (q : ℝ) := a * q ^ 2 + b * q + c
  let P' (q : ℝ) := 2 * a * q + b
  let F (q : ℝ) := (q + 4) / 2 - q + t - farPolyPower a b c x q
  let D (q : ℝ) := -(1 / 2) - farPolyPowerD a b c x q
  have hv : 0 < v := by unfold v; positivity
  have hx : 0 < x := div_pos hv ht
  have hLt : 2 / (2 * t + 1) < L := incident_log_gt ht
  have hL : 0 < L := (show 0 < 2 / (2 * t + 1) by positivity).trans hLt
  have hD (q : ℝ) : HasDerivAt F (D q) q := by
    have h := (hasDerivAt_id q).const_mul (-(1 / 2))
    convert (h.const_add (2 + t)).sub (farPolyPower_deriv a b c hx) using 1
    · funext y
      unfold F
      simp only [id_eq,Pi.sub_apply]
      ring
    · unfold D
      ring
  have hDD (q : ℝ) : HasDerivAt D (-farPolyPowerDD a b c x q) q :=
    (farPolyPowerD_deriv a b c hx).const_sub (-(1 / 2))
  have hPositive (q : ℝ) (hq : q ∈ Icc (2 : ℝ) 4) : 0 ≤ farPolyPowerDD a b c x q := by
    have hq₀ : 0 < q := by linarith only [hq.1]
    have ha : 0 < a := by unfold a; positivity
    have hb : 0 < b := by unfold b; positivity
    have hc : 0 < c := by unfold c; positivity
    have hP : 0 < P q := by unfold P; positivity
    have hR : 0 < q ^ 2 + 3 * q - 1 - (3 * q + 5) * t := by
      have h₁ := mul_le_mul_of_nonneg_left htU (show 0 ≤ 3 * q + 5 by positivity)
      have h₂ := mul_nonneg (sub_nonneg.mpr hq.1) (show 0 ≤ q + 2 by positivity)
      linarith only [h₁,h₂,hq.1]
    have hEq : 2 * v * (P q - (2 * t + 1) * P' q) = q ^ 2 + 3 * q - 1 - (3 * q + 5) * t := by
      unfold P P' a b c
      field_simp [hv.ne']
      unfold v
      ring
    have hPP : (2 * t + 1) * P' q < P q := by
      have h := pos_of_mul_pos_right (hEq.symm ▸ hR) (mul_pos zero_lt_two hv).le
      linarith only [h]
    have hTP := mul_lt_mul_of_pos_right hLt hP
    have hT : 2 * P' q < (2 / (2 * t + 1)) * P q := by
      have he := mul_lt_mul_of_pos_left hPP (show 0 < 2 / (2 * t + 1) by positivity)
      rw [show (2 / (2 * t + 1)) * ((2 * t + 1) * P' q) = 2 * P' q by field_simp [show 2 * t + 1 ≠ 0 by positivity]] at he
      exact he
    have hB := mul_nonneg hL.le (sub_nonneg.mpr (hT.trans hTP).le)
    unfold farPolyPowerDD
    apply mul_nonneg _ (Real.rpow_nonneg hx.le _)
    change 0 ≤ 2 * a - 2 * L * P' q + L ^ 2 * P q
    nlinarith only [ha,hB]
  have hC : ConcaveOn ℝ (Icc 2 4) F := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
      (fun q _ => (hD q).continuousAt.continuousWithinAt)
      (fun q _ => (hD q).hasDerivWithinAt)
      (fun q _ => (hDD q).hasDerivWithinAt)
    exact fun q hq => neg_nonpos.mpr (hPositive q (interior_subset hq))
  have hF₂ : F 2 = (1 + 4 * t - 3 * t ^ 2) / v ^ 3 := by
    unfold F farPolyPower a b c x
    rw [Real.rpow_neg hx.le,Real.rpow_two]
    have hv' : v ≠ 0 := hv.ne'
    unfold x
    field_simp [ht.ne',hv']
    unfold v
    ring
  have hF₄ : F 4 = t * (1 + 5 * t + 10 * t ^ 2 - 10 * t ^ 3) / v ^ 5 := by
    unfold F farPolyPower a b c x
    rw [Real.rpow_neg hx.le,show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,Real.rpow_natCast]
    unfold x
    field_simp [ht.ne',hv.ne']
    unfold v
    ring
  have h₀ : 0 < F 2 := by
    rw [hF₂]
    have h := mul_nonneg ht.le (show 0 ≤ 4 - 3 * t by linarith only [htU])
    exact div_pos (by nlinarith only [h]) (pow_pos hv _)
  have h₁ : 0 < F 4 := by
    rw [hF₄]
    have h := mul_nonneg (sq_nonneg t) (show 0 ≤ 10 - 10 * t by linarith only [htU])
    exact div_pos (mul_pos ht (by nlinarith only [h,ht])) (pow_pos hv _)
  let z := (p - 2) / 2
  have hz : 0 ≤ z := div_nonneg (sub_nonneg.mpr hp) (by norm_num)
  have hz₁ : 0 ≤ 1 - z := by unfold z; linarith only [hp₄]
  have hJ := hC.2 (show (2 : ℝ) ∈ Icc 2 4 by norm_num)
    (show (4 : ℝ) ∈ Icc 2 4 by norm_num) hz₁ hz (by ring)
  simp only [smul_eq_mul] at hJ
  rw [show (1 - z) * 2 + z * 4 = p by unfold z; ring] at hJ
  have hF : 0 < F p := by
    have hMin : 0 < min (F 2) (F 4) := lt_min h₀ h₁
    have h := add_le_add (mul_le_mul_of_nonneg_left (min_le_left (F 2) (F 4)) hz₁)
      (mul_le_mul_of_nonneg_left (min_le_right (F 2) (F 4)) hz)
    rw [← add_mul,sub_add_cancel,one_mul] at h
    exact hMin.trans_le (h.trans hJ)
  have hN : t ^ p * (((p + 4) / 2) * purePeanoA p 1 t - t * purePeanoB p 1 t) = F p := by
    have hShift : v ^ (-(p + 1)) = v ^ (-p) / v := by
      rw [show -(p + 1) = -p - 1 by ring,Real.rpow_sub_one hv.ne']
    have hLeft : t ^ (-(p + 1)) = t ^ (-p) / t := by
      rw [show -(p + 1) = -p - 1 by ring,Real.rpow_sub_one ht.ne']
    have hM : t ^ p * t ^ (-p) = 1 := by rw [← Real.rpow_add ht,add_neg_cancel,Real.rpow_zero]
    have hX : t ^ p * v ^ (-p) = x ^ (-p) := by
      unfold x
      rw [Real.div_rpow hv.le ht.le,Real.rpow_neg ht.le,div_inv_eq_mul,mul_comm]
    unfold purePeanoA purePeanoB F farPolyPower
    simp only [one_mul]
    rw [show t + 1 = v by unfold v; ring]
    change t ^ p * (((p + 4) / 2) * (t ^ (-p) - v ^ (-p) - p * v ^ (-(p + 1))) -
      t * (p * t ^ (-(p + 1)) - t ^ (-p) + v ^ (-p))) = _
    rw [hShift,hLeft]
    have h : t ^ p * (((p + 4) / 2) * (t ^ (-p) - v ^ (-p) - p * (v ^ (-p) / v)) -
        t * (p * (t ^ (-p) / t) - t ^ (-p) + v ^ (-p))) =
        (t ^ p * t ^ (-p)) * ((p + 4) / 2 - p + t) -
          (t ^ p * v ^ (-p)) * ((p + 4) / 2 * (1 + p / v) + t) := by field_simp [ht.ne',hv.ne']; ring
    rw [h,hM,hX,one_mul]
    unfold a b c
    ring
  have h := hN.symm ▸ hF
  exact sub_pos.mp (pos_of_mul_pos_right h (Real.rpow_nonneg ht.le _))

end ACS12.GammaMeasure

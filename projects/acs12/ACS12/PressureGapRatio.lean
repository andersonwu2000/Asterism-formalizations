import ACS12.PressureCanonicalGapD
import ACS12.PressureDebitChord

/-! The full auxiliary ratio and its actual contrast chord. -/
namespace ACS12.Pressure

open Set

private noncomputable def gapH : ℝ := 37877 / 1000188 - 1 / 90
private noncomputable def gapQ : ℝ := 887 / 3920
private noncomputable def gapK : ℝ := 1 / 90
private noncomputable def gapB : ℝ := 1 / 10

noncomputable def gapRatio (v : ℝ) : ℝ :=
  (28 / 27) * Real.exp (-(25 / 126) * v) *
    ((1 + gapH * v ^ 2) * (1 + gapQ * v ^ 2) / ((1 - gapK * v ^ 2) * (1 + gapB * v ^ 2)))

private noncomputable def logQuad (c v : ℝ) : ℝ := Real.log (1 + c * v ^ 2)
private noncomputable def logQuadD (c v : ℝ) : ℝ := 2 * c * v / (1 + c * v ^ 2)
private noncomputable def logQuadDD (c v : ℝ) : ℝ := 2 * c * (1 - c * v ^ 2) / (1 + c * v ^ 2) ^ 2

private theorem logQuad_deriv (c v : ℝ) (h : 0 < 1 + c * v ^ 2) :
    HasDerivAt (logQuad c) (logQuadD c v) v := by
  have hd := (((hasDerivAt_id v).pow 2).const_mul c).const_add 1
  convert hd.log h.ne' using 1
  norm_num [logQuadD]
  ring

private theorem logQuadD_deriv (c v : ℝ) (h : 0 < 1 + c * v ^ 2) :
    HasDerivAt (logQuadD c) (logQuadDD c v) v := by
  have hd := (((hasDerivAt_id v).pow 2).const_mul c).const_add 1
  convert ((hasDerivAt_id v).const_mul (2 * c)).div hd h.ne' using 1
  norm_num [logQuadDD]
  field_simp [h.ne']
  ring

private noncomputable def logGapRatio (v : ℝ) : ℝ :=
  Real.log (28 / 27) - (25 / 126) * v + logQuad gapH v + logQuad gapQ v -
    logQuad (-gapK) v - logQuad gapB v

private theorem gap_ratio_factors {v : ℝ} (hV : v ^ 2 ≤ 2) :
    0 < 1 + gapH * v ^ 2 ∧ 0 < 1 + gapQ * v ^ 2 ∧
      0 < 1 + (-gapK) * v ^ 2 ∧ 0 < 1 + gapB * v ^ 2 := by
  have hH : 0 < gapH := by norm_num [gapH]
  have hQ : 0 < gapQ := by norm_num [gapQ]
  have hB : 0 < gapB := by norm_num [gapB]
  refine ⟨by positivity,by positivity,?_,by positivity⟩
  unfold gapK
  linarith only [hV]

private theorem logGapRatio_convex : ConvexOn ℝ (Icc 0 (Real.sqrt 2)) logGapRatio := by
  let D (v : ℝ) := -(25 / 126) + logQuadD gapH v + logQuadD gapQ v - logQuadD (-gapK) v - logQuadD gapB v
  let E (v : ℝ) := logQuadDD gapH v + logQuadDD gapQ v - logQuadDD (-gapK) v - logQuadDD gapB v
  have hV (v : ℝ) (hv : v ∈ Icc 0 (Real.sqrt 2)) : v ^ 2 ≤ 2 := by
    simpa only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] using pow_le_pow_left₀ hv.1 hv.2 2
  have hD (v : ℝ) (hv : v ∈ Icc 0 (Real.sqrt 2)) : HasDerivAt logGapRatio (D v) v := by
    obtain ⟨hh,hq,hk,hb⟩ := gap_ratio_factors (hV v hv)
    have h := (((hasDerivAt_id v).const_mul (25 / 126 : ℝ)).const_sub (Real.log (28 / 27)))
    convert ((((h.add (logQuad_deriv gapH v hh)).add (logQuad_deriv gapQ v hq)).sub
      (logQuad_deriv (-gapK) v hk)).sub (logQuad_deriv gapB v hb)) using 1
    simp only [D,mul_one]
  have hE (v : ℝ) (hv : v ∈ Icc 0 (Real.sqrt 2)) : HasDerivAt D (E v) v := by
    obtain ⟨hh,hq,hk,hb⟩ := gap_ratio_factors (hV v hv)
    convert (((((logQuadD_deriv gapH v hh).const_add (-(25 / 126))).add (logQuadD_deriv gapQ v hq)).sub
      (logQuadD_deriv (-gapK) v hk)).sub (logQuadD_deriv gapB v hb)) using 1
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
    (fun v hv => (hD v hv).continuousAt.continuousWithinAt)
    (fun v hv => (hD v (interior_subset hv)).hasDerivWithinAt)
    (fun v hv => (hE v (interior_subset hv)).hasDerivWithinAt)
  intro v hv
  have hv' := interior_subset hv
  have hw := hV v hv'
  obtain ⟨hh,hq,hk,hb⟩ := gap_ratio_factors hw
  have hH : 0 ≤ logQuadDD gapH v := by
    unfold logQuadDD gapH
    apply div_nonneg _ (by positivity)
    have h : (0 : ℝ) ≤ 1 - (37877 / 1000188 - 1 / 90) * v ^ 2 := by linarith only [hw]
    exact mul_nonneg (by norm_num) h
  have hK : logQuadDD (-gapK) v ≤ 0 := by
    unfold logQuadDD gapK
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (by nlinarith only [sq_nonneg v])) (by positivity)
  have hQB : logQuadDD gapB v ≤ logQuadDD gapQ v := by
    unfold logQuadDD
    apply (div_le_div_iff₀ (sq_pos_of_pos hb) (sq_pos_of_pos hq)).mpr
    have hPoly : (0 : ℝ) ≤ 1 - (gapQ + gapB) * v ^ 2 - 3 * gapQ * gapB * v ^ 4 := by
      have h4 := pow_le_pow_left₀ (sq_nonneg v) hw 2
      unfold gapQ gapB
      nlinarith only [hw,h4]
    have hEq : 2 * gapQ * (1 - gapQ * v ^ 2) * (1 + gapB * v ^ 2) ^ 2 -
        2 * gapB * (1 - gapB * v ^ 2) * (1 + gapQ * v ^ 2) ^ 2 =
        (2 * (gapQ - gapB)) * (1 - (gapQ + gapB) * v ^ 2 - 3 * gapQ * gapB * v ^ 4) := by ring
    exact sub_nonneg.mp (hEq ▸ mul_nonneg (by norm_num [gapQ,gapB]) hPoly)
  unfold E
  linarith only [hH,hK,hQB]

private theorem exp_logGapRatio {v : ℝ} (hV : v ^ 2 ≤ 2) : Real.exp (logGapRatio v) = gapRatio v := by
  obtain ⟨hh,hq,hk,hb⟩ := gap_ratio_factors hV
  unfold logGapRatio gapRatio logQuad
  rw [Real.exp_sub,Real.exp_sub,Real.exp_add,Real.exp_add,Real.exp_sub,
    Real.exp_log (by norm_num : (0 : ℝ) < 28 / 27),Real.exp_log hh,Real.exp_log hq,Real.exp_log hk,Real.exp_log hb]
  rw [show -(25 / 126 : ℝ) * v = -((25 / 126) * v) by ring,Real.exp_neg]
  simp only [div_eq_mul_inv,mul_inv_rev,sub_eq_add_neg,neg_mul]
  ring

private theorem pressureContrastCap_bounds :
    (138629 / 100000 : ℝ) < pressureContrastCap ∧ pressureContrastCap < 138630 / 100000 := by
  unfold pressureContrastCap
  rw [show (4 : ℝ) = 2 * 2 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
  constructor
  · linarith only [Real.log_two_gt_d9]
  · linarith only [Real.log_two_lt_d9]

private theorem gapRatio_far_lt : gapRatio pressureContrastCap < 1019 / 1000 := by
  let L := pressureContrastCap
  let a : ℝ := 138629 / 100000
  let b : ℝ := 138630 / 100000
  have hLo : a ≤ L := pressureContrastCap_bounds.1.le
  have hHi : L ≤ b := pressureContrastCap_bounds.2.le
  have ha : 0 < a := by norm_num [a]
  have hb : 0 < b := by norm_num [b]
  have hL := ha.trans_le hLo
  have hL₀ := pow_le_pow_left₀ ha.le hLo 2
  have hL₁ := pow_le_pow_left₀ hL.le hHi 2
  have hE : Real.exp (-(25 / 126) * L) ≤ 10000 / 13166 := by
    have h := Real.sum_le_exp_of_nonneg (x := (25 / 126) * a) (by positivity) 8
    norm_num [a,Finset.sum_range_succ,Nat.factorial] at h
    have hExp : (13166 / 10000 : ℝ) ≤ Real.exp ((25 / 126) * L) :=
      (by linarith only [h] : (13166 / 10000 : ℝ) ≤ Real.exp ((25 / 126) * a)).trans
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hLo (by norm_num)))
    rw [neg_mul,Real.exp_neg,← one_div,show (10000 / 13166 : ℝ) = 1 / (13166 / 10000) by norm_num]
    exact div_le_div_of_nonneg_left zero_le_one (by norm_num) hExp
  let P (v : ℝ) := (1 + gapH * v ^ 2) * (1 + gapQ * v ^ 2)
  let D (x y : ℝ) := (1 - gapK * x ^ 2) * (1 + gapB * y ^ 2)
  have hH : 0 ≤ gapH := by norm_num [gapH]
  have hQ : 0 ≤ gapQ := by norm_num [gapQ]
  have hK : 0 ≤ gapK := by norm_num [gapK]
  have hB : 0 ≤ gapB := by norm_num [gapB]
  have hPB : P L ≤ P b := by
    unfold P
    gcongr
  have hD : 0 < D b a := by norm_num [D,a,b,gapK,gapB]
  have hDL : D b a ≤ D L L := by
    have h₁ : 1 - gapK * b ^ 2 ≤ 1 - gapK * L ^ 2 :=
      sub_le_sub_left (mul_le_mul_of_nonneg_left hL₁ hK) 1
    have h₂ : 1 + gapB * a ^ 2 ≤ 1 + gapB * L ^ 2 :=
      add_le_add_right (mul_le_mul_of_nonneg_left hL₀ hB) 1
    have h₀ : 0 ≤ 1 - gapK * L ^ 2 := (by norm_num [gapK,b] : (0 : ℝ) ≤ 1 - gapK * b ^ 2).trans h₁
    exact mul_le_mul h₁ h₂ (by positivity) h₀
  have hR := div_le_div₀ (show 0 ≤ P b by unfold P; positivity) hPB hD hDL
  have hRL : 0 ≤ P L / D L L := div_nonneg (by unfold P; positivity) (hD.le.trans hDL)
  change (28 / 27) * Real.exp (-(25 / 126) * L) * (P L / D L L) < 1019 / 1000
  have h := mul_le_mul (mul_le_mul_of_nonneg_left hE (by norm_num : (0 : ℝ) ≤ 28 / 27)) hR hRL (by norm_num)
  exact h.trans_lt (by norm_num [P,D,a,b,gapH,gapQ,gapK,gapB])

theorem gapRatio_le_chord {v : ℝ} (hv : 0 ≤ v) (hL : v ≤ pressureContrastCap) :
    gapRatio v ≤ 28 / 27 - (487 / (27000 * pressureContrastCap)) * v := by
  let L := pressureContrastCap
  have hL₀ : 0 < L := (by norm_num : (0 : ℝ) < 138629 / 100000).trans pressureContrastCap_bounds.1
  have hL₂ : L ^ 2 ≤ 2 := by
    have h := pow_le_pow_left₀ hL₀.le pressureContrastCap_bounds.2.le 2
    exact h.trans (by norm_num)
  have hS : L ≤ Real.sqrt 2 := (Real.le_sqrt hL₀.le (by norm_num)).mpr hL₂
  have hC := logGapRatio_convex.subset (show Icc 0 L ⊆ Icc 0 (Real.sqrt 2) from fun x hx =>
    ⟨hx.1,hx.2.trans hS⟩) (convex_Icc _ _)
  let b := v / L
  have hb : 0 ≤ b := div_nonneg hv hL₀.le
  have hb₁ : b ≤ 1 := (div_le_one hL₀).mpr hL
  have h := hC.2 ⟨le_rfl,hL₀.le⟩ ⟨hL₀.le,le_rfl⟩ (sub_nonneg.mpr hb₁) hb (sub_add_cancel 1 b)
  have hE : b * L = v := div_mul_cancel₀ v hL₀.ne'
  simp only [smul_eq_mul,mul_zero,zero_add,hE] at h
  have hJ := convexOn_exp.2 (mem_univ (logGapRatio 0)) (mem_univ (logGapRatio L))
    (sub_nonneg.mpr hb₁) hb (sub_add_cancel 1 b)
  simp only [smul_eq_mul] at hJ
  have hR := (Real.exp_le_exp.mpr h).trans hJ
  have hv₂ := (pow_le_pow_left₀ hv hL 2).trans hL₂
  rw [exp_logGapRatio hv₂,exp_logGapRatio (by norm_num : (0 : ℝ) ^ 2 ≤ 2),exp_logGapRatio hL₂] at hR
  have h₀ : gapRatio 0 = 28 / 27 := by norm_num [gapRatio]
  rw [h₀] at hR
  have hF : gapRatio L < 1019 / 1000 := gapRatio_far_lt
  have hR' := hR.trans (add_le_add_right (mul_le_mul_of_nonneg_left hF.le hb) _)
  have hB : (487 / (27000 * L)) * v = (487 / 27000) * b := by unfold b; ring
  change _ ≤ 28 / 27 - (487 / (27000 * L)) * v
  rw [hB]
  linarith only [hR']

end ACS12.Pressure


import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The two scalar rows of the quartic payment on the finite mass support. -/
namespace ACS12.NativeCells

open Set

noncomputable section

/-- The intercept of the quartic payment. -/
def quarticPaymentIntercept (x u : ℝ) : ℝ :=
  (149 / 50) * (u * Real.log u - u + 1) -
    (1 + (15 / 2) * (13 / 400)) * (u - 1 - Real.log u) -
    ((31 / 10) * x + (25 / 2) * (13 / 400) * x ^ 2) * (u - 1) ^ 2

/-- The slope of the quartic payment. -/
def quarticPaymentSlope (x u : ℝ) : ℝ :=
  u * Real.log u - u + 1 - 8 * (69 / 1250) * (u - 1 - Real.log u) -
    ((27 / 2) * (69 / 1250) + (43 / 24) * (u + 2)) * x ^ 2 * (u - 1) ^ 2

private theorem between_derivative {f d : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ z > 0, HasDerivAt f (d z) z) (ha : 0 < a) (hab : a < b) :
    ∃ c ∈ Ioo a b, d c = (f b - f a) / (b - a) := by
  obtain ⟨c, hc, h⟩ := exists_deriv_eq_slope f hab
    (fun z hz => (hf z (ha.trans_le hz.1)).continuousAt.continuousWithinAt)
    (fun z hz => (hf z (ha.trans hz.1)).differentiableAt.differentiableWithinAt)
  exact ⟨c, hc, (hf c (ha.trans hc.1)).deriv.symm.trans h⟩

/-- Positive endpoint values and positive scaled curvature at a double contact
suffice when the scaled curvature is concave. An interior nonpositive value
would force nonpositive curvature between two positive curvature values. -/
private theorem support_pos {f d dd K : ℝ → ℝ} {a b u : ℝ}
    (ha : 0 < a) (hau : a ≤ u) (hub : u ≤ b)
    (hf : ∀ z > 0, HasDerivAt f (d z) z)
    (hd : ∀ z > 0, HasDerivAt d (dd z) z)
    (hK : ∀ z > 0, K z = z ^ 2 * dd z) (hconc : ConcaveOn ℝ (Ioi 0) K)
    (hk : 0 < K 1) (hf₁ : f 1 = 0) (hd₁ : d 1 = 0)
    (hfa : 0 < f a) (hfb : 0 < f b) (hne : u ≠ 1) : 0 < f u := by
  by_contra! hbad
  have hau' : a < u := lt_of_le_of_ne hau (by intro h; rw [h] at hfa; linarith)
  have hub' : u < b := lt_of_le_of_ne hub (by intro h; rw [← h] at hfb; linarith)
  have hu : 0 < u := ha.trans hau'
  rcases lt_or_gt_of_ne hne with hLeft | hRight
  · obtain ⟨c, hc, hdc⟩ := between_derivative hf ha hau'
    obtain ⟨e, he, hde⟩ := between_derivative hf hu hLeft
    have hc' : 0 < c := ha.trans hc.1
    have he' : 0 < e := hu.trans he.1
    have hdc' : d c < 0 := by
      rw [hdc]
      exact div_neg_of_neg_of_pos (by linarith) (sub_pos.mpr hau')
    have hde' : 0 ≤ d e := by
      rw [hde, hf₁]
      exact div_nonneg (by linarith) (sub_nonneg.mpr hLeft.le)
    have hce : c < e := hc.2.trans he.1
    obtain ⟨v, hv, hddv⟩ := between_derivative hd hc' hce
    obtain ⟨w, hw, hddw⟩ := between_derivative hd he' he.2
    have hv' : 0 < v := hc'.trans hv.1
    have hw' : 0 < w := he'.trans hw.1
    have hKv : 0 < K v := by
      rw [hK v hv', hddv]
      exact mul_pos (sq_pos_of_pos hv') (div_pos (by linarith) (sub_pos.mpr hce))
    have hKw : K w ≤ 0 := by
      rw [hK w hw', hddw, hd₁]
      exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) <|
        div_nonpos_of_nonpos_of_nonneg (by linarith) (sub_nonneg.mpr he.2.le)
    have hmin := hconc.min_le_of_mem_Icc (mem_Ioi.mpr hv') (mem_Ioi.mpr zero_lt_one)
      (show w ∈ Icc v 1 from ⟨(hv.2.trans hw.1).le, hw.2.le⟩)
    exact (not_lt_of_ge hKw) ((lt_min hKv hk).trans_le hmin)
  · obtain ⟨c, hc, hdc⟩ := between_derivative hf zero_lt_one hRight
    obtain ⟨e, he, hde⟩ := between_derivative hf hu hub'
    have hc' : 0 < c := zero_lt_one.trans hc.1
    have hdc' : d c ≤ 0 := by
      rw [hdc, hf₁]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (sub_nonneg.mpr hRight.le)
    have hde' : 0 < d e := by
      rw [hde]
      exact div_pos (by linarith) (sub_pos.mpr hub')
    have hce : c < e := hc.2.trans he.1
    obtain ⟨w, hw, hddw⟩ := between_derivative hd zero_lt_one hc.1
    obtain ⟨v, hv, hddv⟩ := between_derivative hd hc' hce
    have hw' : 0 < w := zero_lt_one.trans hw.1
    have hv' : 0 < v := hc'.trans hv.1
    have hKw : K w ≤ 0 := by
      rw [hK w hw', hddw, hd₁]
      exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) <|
        div_nonpos_of_nonpos_of_nonneg (by linarith) (sub_nonneg.mpr hc.1.le)
    have hKv : 0 < K v := by
      rw [hK v hv', hddv]
      exact mul_pos (sq_pos_of_pos hv') (div_pos (by linarith) (sub_pos.mpr hce))
    have hmin := hconc.min_le_of_mem_Icc (mem_Ioi.mpr zero_lt_one) (mem_Ioi.mpr hv')
      (show w ∈ Icc 1 v from ⟨hw.1.le, (hw.2.trans hv.1).le⟩)
    exact (not_lt_of_ge hKw) ((lt_min hk hKv).trans_le hmin)

private def massEntropy (u : ℝ) : ℝ := u * Real.log u - u + 1
private def massDebit (u : ℝ) : ℝ := u - 1 - Real.log u

private theorem massEntropy_deriv {u : ℝ} (hu : 0 < u) :
    HasDerivAt massEntropy (Real.log u) u := by
  unfold massEntropy
  convert (((hasDerivAt_id u).mul (Real.hasDerivAt_log hu.ne')).sub
    (hasDerivAt_id u)).add_const 1 using 1
  simp [hu.ne']

private theorem massDebit_deriv {u : ℝ} (hu : 0 < u) :
    HasDerivAt massDebit (1 - u⁻¹) u := by
  simpa [massDebit, one_div] using
    ((hasDerivAt_id u).sub_const 1).sub (Real.hasDerivAt_log hu.ne')

private def paymentRow (P Q A B u : ℝ) : ℝ :=
  P * massEntropy u - Q * massDebit u - (A + B * (u + 2)) * (u - 1) ^ 2

private def paymentFirst (P Q A B u : ℝ) : ℝ :=
  P * Real.log u - Q * (1 - u⁻¹) - 2 * A * (u - 1) - 3 * B * (u ^ 2 - 1)

private def paymentSecond (P Q A B u : ℝ) : ℝ :=
  P / u - Q / u ^ 2 - 2 * A - 6 * B * u

private def paymentCurvature (P Q A B u : ℝ) : ℝ :=
  P * u - Q - 2 * A * u ^ 2 - 6 * B * u ^ 3

private theorem paymentRow_deriv (P Q A B : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (paymentRow P Q A B) (paymentFirst P Q A B u) u := by
  have hcost := (((hasDerivAt_id u).add_const 2).const_mul B |>.const_add A).mul
    (((hasDerivAt_id u).sub_const 1).pow 2)
  unfold paymentRow paymentFirst
  convert (((massEntropy_deriv hu).const_mul P).sub
    ((massDebit_deriv hu).const_mul Q)).sub hcost using 1
  simp only [id_eq, Pi.pow_apply]
  ring

private theorem paymentFirst_deriv (P Q A B : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (paymentFirst P Q A B) (paymentSecond P Q A B u) u := by
  have hd := (hasDerivAt_inv hu.ne').const_sub 1
  have hA := ((hasDerivAt_id u).sub_const 1).const_mul (2 * A)
  have hB := (((hasDerivAt_id u).pow 2).sub_const 1).const_mul (3 * B)
  unfold paymentFirst paymentSecond
  convert ((((Real.hasDerivAt_log hu.ne').const_mul P).sub
    (hd.const_mul Q)).sub hA).sub hB using 1
  simp only [id_eq, div_eq_mul_inv]
  ring

private theorem paymentCurvature_concave (P Q A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ConcaveOn ℝ (Ioi 0) (paymentCurvature P Q A B) := by
  let F (u : ℝ) := P - 4 * A * u - 18 * B * u ^ 2
  let G (u : ℝ) := -(4 * A + 36 * B * u)
  have hF (u : ℝ) : HasDerivAt (paymentCurvature P Q A B) (F u) u := by
    unfold paymentCurvature F
    convert ((((hasDerivAt_id u).const_mul P).sub_const Q).sub
      ((hasDerivAt_pow 2 u).const_mul (2 * A))).sub
      ((hasDerivAt_pow 3 u).const_mul (6 * B)) using 1
    norm_num
    ring
  have hG (u : ℝ) : HasDerivAt F (G u) u := by
    unfold F G
    convert (((hasDerivAt_id u).const_mul (4 * A)).const_sub P).sub
      ((hasDerivAt_pow 2 u).const_mul (18 * B)) using 1
    norm_num
    ring
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ioi 0) (f' := F) (f'' := G)
  · exact fun u _ => (hF u).continuousAt.continuousWithinAt
  · exact fun u _ => (hF u).hasDerivWithinAt
  · exact fun u _ => (hG u).hasDerivWithinAt
  · intro u hu
    have hu' : 0 ≤ u := (mem_Ioi.mp (interior_subset hu)).le
    exact neg_nonpos.mpr (by positivity)

private theorem paymentRow_pos {P Q A B a b u : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : 0 < a) (hau : a ≤ u) (hub : u ≤ b)
    (hunit : 0 < P - Q - 2 * A - 6 * B) (haRow : 0 < paymentRow P Q A B a)
    (hbRow : 0 < paymentRow P Q A B b) (hne : u ≠ 1) :
    0 < paymentRow P Q A B u := by
  apply support_pos ha hau hub (fun z => paymentRow_deriv P Q A B)
    (fun z => paymentFirst_deriv P Q A B) _
    (paymentCurvature_concave P Q A B hA hB) _ _ _ haRow hbRow hne
  · intro z hz
    unfold paymentCurvature paymentSecond
    field_simp [hz.ne']
  · simpa [paymentCurvature] using hunit
  · simp [paymentRow, massEntropy, massDebit]
  · simp [paymentFirst]

private theorem log_five_upper : Real.log 5 < 3219 / 2000 := by
  have h := Real.log_div_le_sum_range_add (x := 2 / 3) (by norm_num) (by norm_num) 24
  norm_num [Finset.sum_range_succ] at h
  linarith only [h]

private theorem log_five_fourths_lower : (11157 / 50000 : ℝ) < Real.log (5 / 4) := by
  have h := Real.sum_range_le_log_div (x := 1 / 9) (by norm_num) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h
  linarith only [h]

private def capRow (P Q l m s : ℝ) : ℝ :=
  P * massEntropy s - Q * massDebit s - (l * s + m) * (1 - 1 / s) ^ 2

private def capFirst (P Q l m s : ℝ) : ℝ :=
  P * Real.log s - Q * (1 - s⁻¹) - l + (l - 2 * m) / s ^ 2 + 2 * m / s ^ 3

private def capCurvature (P Q l m s : ℝ) : ℝ :=
  P * s ^ 3 - Q * s ^ 2 - 2 * (l - 2 * m) * s - 6 * m

private theorem capRow_deriv (P Q l m : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (capRow P Q l m) (capFirst P Q l m s) s := by
  have hcost := (((hasDerivAt_id s).const_mul l).add_const m).mul
    (((hasDerivAt_inv hs.ne').const_sub 1).pow 2)
  unfold capRow capFirst
  simp only [one_div]
  convert (((massEntropy_deriv hs).const_mul P).sub
    ((massDebit_deriv hs).const_mul Q)).sub hcost using 1
  simp only [id_eq, Pi.pow_apply, Nat.reduceSub, pow_one]
  ring_nf
  field_simp [hs.ne']
  ring

private theorem capFirst_deriv (P Q l m : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (capFirst P Q l m) (capCurvature P Q l m s / s ^ 4) s := by
  have h₂ := ((hasDerivAt_pow 2 s).inv (pow_ne_zero 2 hs.ne')).const_mul (l - 2 * m)
  have h₃ := ((hasDerivAt_pow 3 s).inv (pow_ne_zero 3 hs.ne')).const_mul (2 * m)
  unfold capFirst capCurvature
  simp only [div_eq_mul_inv]
  convert (((((Real.hasDerivAt_log hs.ne').const_mul P).sub
    (((hasDerivAt_inv hs.ne').const_sub 1).const_mul Q)).sub_const l).add h₂).add h₃ using 1
  norm_num
  field_simp [hs.ne']
  ring

/-- The cubic scaled curvature has a positive constant term and nonnegative
remaining Taylor coefficients at the base of the cap ray. -/
private theorem capRow_pos {P Q l m s : ℝ} (hP : 0 ≤ P) (hs : 5 / 4 ≤ s)
    (hJ₀ : 0 < capCurvature P Q l m (5 / 4))
    (hJ₁ : 0 ≤ 3 * P * (5 / 4) ^ 2 - 2 * Q * (5 / 4) - 2 * (l - 2 * m))
    (hJ₂ : 0 ≤ 3 * P * (5 / 4) - Q)
    (hE : 0 < capRow P Q l m (5 / 4)) (hD : 0 < capFirst P Q l m (5 / 4)) :
    0 < capRow P Q l m s := by
  have hbase : (0 : ℝ) < 5 / 4 := by norm_num
  have hJ (z : ℝ) (hz : 5 / 4 ≤ z) : 0 < capCurvature P Q l m z := by
    have hδ : 0 ≤ z - 5 / 4 := sub_nonneg.mpr hz
    have hEq : capCurvature P Q l m z =
        capCurvature P Q l m (5 / 4) +
        (3 * P * (5 / 4) ^ 2 - 2 * Q * (5 / 4) - 2 * (l - 2 * m)) * (z - 5 / 4) +
        (3 * P * (5 / 4) - Q) * (z - 5 / 4) ^ 2 + P * (z - 5 / 4) ^ 3 := by
      unfold capCurvature
      ring
    rw [hEq]
    positivity
  have hmonoD : StrictMonoOn (capFirst P Q l m) (Ici (5 / 4)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
    · exact fun z hz =>
        (capFirst_deriv P Q l m (hbase.trans_le hz)).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Ici, mem_Ioi] at hz
      have hz' := hbase.trans hz
      rw [(capFirst_deriv P Q l m hz').deriv]
      exact div_pos (hJ z hz.le) (by positivity)
  have hmono : StrictMonoOn (capRow P Q l m) (Ici (5 / 4)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
    · exact fun z hz =>
        (capRow_deriv P Q l m (hbase.trans_le hz)).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Ici, mem_Ioi] at hz
      rw [(capRow_deriv P Q l m (hbase.trans hz)).deriv]
      exact hD.trans (hmonoD (mem_Ici.mpr le_rfl) (mem_Ici.mpr hz.le) hz)
  exact hE.trans_le (hmono.monotoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr hs) hs)

private theorem intercept_cap_pos {s : ℝ} (hs : 5 / 4 ≤ s) :
    0 < capRow (149 / 50) (1 + (15 / 2) * (13 / 400))
      ((31 / 10) / 4) ((25 / 2) * (13 / 400) / 16) s := by
  apply capRow_pos (by norm_num) hs
  · norm_num [capCurvature]
  · norm_num
  · norm_num
  · norm_num [capRow, massEntropy, massDebit]
    linarith only [log_five_fourths_lower]
  · norm_num [capFirst]
    linarith only [log_five_fourths_lower]

private theorem slope_cap_pos {s : ℝ} (hs : 5 / 4 ≤ s) :
    0 < capRow 1 (8 * (69 / 1250)) ((43 / 24) / 16)
      ((2 * (43 / 24) + (27 / 2) * (69 / 1250)) / 16) s := by
  apply capRow_pos (by norm_num) hs
  · norm_num [capCurvature]
  · norm_num
  · norm_num
  · norm_num [capRow, massEntropy, massDebit]
    linarith only [log_five_fourths_lower]
  · norm_num [capFirst]
    linarith only [log_five_fourths_lower]

private theorem intercept_eq_row (x u : ℝ) :
    quarticPaymentIntercept x u =
      paymentRow (149 / 50) (1 + (15 / 2) * (13 / 400))
        ((31 / 10) * x + (25 / 2) * (13 / 400) * x ^ 2) 0 u := by
  simp [quarticPaymentIntercept, paymentRow, massEntropy, massDebit]

private theorem slope_eq_row (x u : ℝ) :
    quarticPaymentSlope x u =
      paymentRow 1 (8 * (69 / 1250)) ((27 / 2) * (69 / 1250) * x ^ 2)
        ((43 / 24) * x ^ 2) u := by
  unfold quarticPaymentSlope paymentRow massEntropy massDebit
  ring

/-- The two quartic payment rows are strictly positive on the mass support
away from the common unit contact. -/
theorem quarticPayment_pos {x u : ℝ} (hx : 0 < x) (hx5 : x ≤ 1 / 5) (hu : 1 / 5 ≤ u)
    (hcap : x * u ≤ 1 / 4) (hne : u ≠ 1) :
    0 < quarticPaymentIntercept x u ∧ 0 < quarticPaymentSlope x u := by
  let s : ℝ := 1 / (4 * x)
  have h4x : 0 < 4 * x := by positivity
  have hs : (5 / 4 : ℝ) ≤ s := by
    dsimp only [s]
    apply (le_div_iff₀ h4x).mpr
    linarith
  have hus : u ≤ s := by
    dsimp only [s]
    apply (le_div_iff₀ h4x).mpr
    linarith only [hcap]
  have hsPos : 0 < s := (by norm_num : (0 : ℝ) < 5 / 4).trans_le hs
  have hxS : x = 1 / (4 * s) := by
    dsimp only [s]
    field_simp [hx.ne']
  have hxsq : x ^ 2 ≤ (1 / 5 : ℝ) ^ 2 := pow_le_pow_left₀ hx.le hx5 2
  have hlog : Real.log (1 / 5 : ℝ) = -Real.log 5 := by rw [one_div, Real.log_inv]
  constructor
  · rw [intercept_eq_row]
    refine paymentRow_pos (by positivity) le_rfl (by norm_num) hu hus ?_ ?_ ?_ hne
    · linarith only [hx5, hxsq]
    · norm_num [paymentRow, massEntropy, massDebit, hlog]
      linarith only [log_five_upper, hx5, hxsq]
    · have hEq : quarticPaymentIntercept x s =
          capRow (149 / 50) (1 + (15 / 2) * (13 / 400))
            ((31 / 10) / 4) ((25 / 2) * (13 / 400) / 16) s := by
        rw [hxS]
        unfold quarticPaymentIntercept capRow massEntropy massDebit
        field_simp [hsPos.ne']
        ring
      rw [← intercept_eq_row, hEq]
      exact intercept_cap_pos hs
  · rw [slope_eq_row]
    refine paymentRow_pos (by positivity) (by positivity) (by norm_num) hu hus ?_ ?_ ?_ hne
    · linarith only [hxsq]
    · norm_num [paymentRow, massEntropy, massDebit, hlog]
      linarith only [log_five_upper, hxsq]
    · have hEq : quarticPaymentSlope x s =
          capRow 1 (8 * (69 / 1250)) ((43 / 24) / 16)
            ((2 * (43 / 24) + (27 / 2) * (69 / 1250)) / 16) s := by
        rw [hxS]
        unfold quarticPaymentSlope capRow massEntropy massDebit
        field_simp [hsPos.ne']
        ring
      rw [← slope_eq_row, hEq]
      exact slope_cap_pos hs

end

end ACS12.NativeCells

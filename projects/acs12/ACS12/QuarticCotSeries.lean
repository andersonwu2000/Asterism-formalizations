import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.NumberTheory.ZetaValues

/-! The logarithmic sine slope and curvature as convergent cotangent series. -/
namespace ACS12.NativeCells

open Set Filter
open scoped Topology

noncomputable def quarticLogSinc (y : ℝ) : ℝ := Real.log (Real.sin (Real.pi*y)/y)

noncomputable def quarticLogSincSlope (y : ℝ) : ℝ :=
  Real.pi*Real.cos (Real.pi*y)/Real.sin (Real.pi*y)-1/y

noncomputable def quarticLogSincCurvature (y : ℝ) : ℝ :=
  1/y^2-Real.pi^2/(Real.sin (Real.pi*y))^2

private theorem quarticSin_pos {y : ℝ} (hy : 0 < y) (hY : y < 1/2) :
    0 < Real.sin (Real.pi*y) := by
  apply Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hy)
  nlinarith only [Real.pi_pos,mul_lt_mul_of_pos_left hY Real.pi_pos]

theorem quarticLogSinc_hasDerivAt {y : ℝ} (hy : 0 < y) (hY : y < 1/2) :
    HasDerivAt quarticLogSinc (quarticLogSincSlope y) y := by
  have hSin := quarticSin_pos hy hY
  have hd := hasDerivAt_id y
  have hDiv := (hd.const_mul Real.pi).sin.div hd hy.ne'
  have h := hDiv.log (div_pos hSin hy).ne'
  convert h using 1
  simp only [quarticLogSincSlope,Pi.div_apply,id_eq,mul_one]
  field_simp [hy.ne',hSin.ne']

theorem quarticLogSincSlope_hasDerivAt {y : ℝ} (hy : 0 < y) (hY : y < 1/2) :
    HasDerivAt quarticLogSincSlope (quarticLogSincCurvature y) y := by
  have hSin := quarticSin_pos hy hY
  have hd := hasDerivAt_id y
  have hPi := hd.const_mul Real.pi
  have h := ((hPi.cos.const_mul Real.pi).div hPi.sin hSin.ne').sub ((hasDerivAt_const y (1:ℝ)).div hd hy.ne')
  convert h using 1
  simp only [quarticLogSincCurvature,id_eq,mul_one,zero_mul,zero_sub]
  have hTrig : Real.pi*(-Real.sin (Real.pi*y)*Real.pi)*Real.sin (Real.pi*y) -
      Real.pi*Real.cos (Real.pi*y)*(Real.cos (Real.pi*y)*Real.pi) = -Real.pi^2 := by
    linear_combination -(Real.pi^2)*Real.sin_sq_add_cos_sq (Real.pi*y)
  rw [hTrig]
  ring

noncomputable def quarticCotTerm (n : ℕ) (y : ℝ) : ℝ :=
  2*y/(((n:ℝ)+1)^2-y^2)

noncomputable def quarticCotCurvatureTerm (n : ℕ) (y : ℝ) : ℝ :=
  2*(((n:ℝ)+1)^2+y^2)/(((n:ℝ)+1)^2-y^2)^2

private theorem quarticCot_den_lower (n : ℕ) {y : ℝ} (hy : y ∈ Ioo (-(1/2):ℝ) (1/2)) :
    (3/4)*((n:ℝ)+1)^2 ≤ ((n:ℝ)+1)^2-y^2 := by
  have hN : 1 ≤ ((n:ℝ)+1)^2 := by nlinarith only [sq_nonneg (n:ℝ),Nat.cast_nonneg (α := ℝ) n]
  have hY : y^2 ≤ 1/4 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hy.2.le) (show 0 ≤ 1/2+y by linarith only [hy.1])]
  linarith only [hN,hY]

private theorem quarticCotTerm_deriv (n : ℕ) {y : ℝ} (hy : y ∈ Ioo (-(1/2):ℝ) (1/2)) :
    HasDerivAt (quarticCotTerm n) (quarticCotCurvatureTerm n y) y := by
  have hDen : 0 < ((n:ℝ)+1)^2-y^2 :=
    (mul_pos (by norm_num) (by positivity)).trans_le (quarticCot_den_lower n hy)
  have hd := hasDerivAt_id y
  have h := (hd.const_mul 2).div ((hd.pow 2).const_sub (((n:ℝ)+1)^2)) hDen.ne'
  convert h using 1
  simp only [quarticCotCurvatureTerm,id_eq,Pi.pow_apply,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one]
  field_simp [hDen.ne']
  ring

private theorem quarticCot_curvature_bound (n : ℕ) {y : ℝ} (hy : y ∈ Ioo (-(1/2):ℝ) (1/2)) :
    ‖quarticCotCurvatureTerm n y‖ ≤ 5/((n:ℝ)+1)^2 := by
  let r := ((n:ℝ)+1)^2
  have hr : 0 < r := by unfold r; positivity
  have hD : (3/4)*r ≤ r-y^2 := quarticCot_den_lower n hy
  have hD₀ : 0 < r-y^2 := (mul_pos (by norm_num) hr).trans_le hD
  have hNum : 2*(r+y^2) ≤ (5/2)*r := by linarith only [hD]
  have hDen := pow_le_pow_left₀ (by positivity : 0 ≤ (3/4)*r) hD 2
  unfold quarticCotCurvatureTerm
  change ‖2*(r+y^2)/(r-y^2)^2‖ ≤ 5/r
  rw [Real.norm_of_nonneg (by positivity)]
  apply (div_le_div_iff₀ (pow_pos hD₀ _) hr).mpr
  nlinarith only [mul_le_mul_of_nonneg_right hNum hr.le,hDen,sq_nonneg r]

private theorem quarticCot_inverse_square_hasSum :
    HasSum (fun n : ℕ => 1/((n:ℝ)+1)^2) (Real.pi^2/6) := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simpa [Nat.cast_add,Finset.sum_range_succ] using h

private theorem quarticCot_majorant_summable : Summable (fun n : ℕ => 5/((n:ℝ)+1)^2) := by
  simpa only [mul_one_div,mul_one] using quarticCot_inverse_square_hasSum.summable.mul_left (5:ℝ)

theorem quarticCotTerm_summable {y : ℝ} (hy : 0 < y) (hY : y < 1/2) :
    Summable (fun n => quarticCotTerm n y) := by
  have h0 : (0:ℝ) ∈ Ioo (-(1/2):ℝ) (1/2) := by norm_num
  have hS : Summable (fun n => quarticCotTerm n 0) := by simp [quarticCotTerm]
  have hMem : y ∈ Ioo (-(1/2):ℝ) (1/2) := ⟨(by norm_num : (-(1/2):ℝ) < 0).trans hy,hY⟩
  exact summable_of_summable_hasDerivAt_of_isPreconnected quarticCot_majorant_summable isOpen_Ioo
    (convex_Ioo _ _).isPreconnected (fun n _ h => quarticCotTerm_deriv n h)
    (fun n _ h => quarticCot_curvature_bound n h) h0 hS hMem

theorem quarticCotCurvatureTerm_summable {y : ℝ} (hy : 0 < y) (hY : y < 1/2) :
    Summable (fun n => quarticCotCurvatureTerm n y) := by
  have hMem : y ∈ Ioo (-(1/2):ℝ) (1/2) := ⟨(by norm_num : (-(1/2):ℝ) < 0).trans hy,hY⟩
  exact Summable.of_norm_bounded quarticCot_majorant_summable (fun n => quarticCot_curvature_bound n hMem)

theorem quarticCotCurvatureTerm_zero_hasSum :
    HasSum (fun n => quarticCotCurvatureTerm n 0) (Real.pi^2/3) := by
  convert quarticCot_inverse_square_hasSum.mul_left (2:ℝ) using 1
  · funext n
    unfold quarticCotCurvatureTerm
    simp only [zero_pow (by decide : (2:ℕ)≠0),add_zero,sub_zero]
    field_simp [show (n:ℝ)+1 ≠ 0 by positivity]
  · ring

theorem quarticCotCurvatureTerm_tsum_zero :
    (∑' n, quarticCotCurvatureTerm n 0) = Real.pi^2/3 := quarticCotCurvatureTerm_zero_hasSum.tsum_eq

theorem quarticLogSincSlope_eq_neg_tsum {y : ℝ} (hy : 0 < y) (hY : y < 1/2) :
    quarticLogSincSlope y = -(∑' n, quarticCotTerm n y) := by
  have hz : (y:ℂ) ∈ Complex.integerComplement := by
    intro hz
    obtain ⟨k,hk⟩ := hz
    have hR := congrArg Complex.re hk
    simp only [Complex.intCast_re,Complex.ofReal_re] at hR
    have hk₀ : (0:ℤ) < k := by exact_mod_cast (show (0:ℝ) < (k:ℝ) by linarith only [hy,hR])
    have hk₁ : 1 ≤ k := by omega
    have hkR : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk₁
    linarith only [hY,hR,hkR]
  have hBoth : y ∈ Ioo (-(1/2):ℝ) (1/2) := ⟨(by norm_num : (-(1/2):ℝ) < 0).trans hy,hY⟩
  have hTerm (n : ℕ) : cotTerm (y:ℂ) n = -(quarticCotTerm n y:ℂ) := by
    have hn : (1:ℝ) ≤ (n:ℝ)+1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
    have hm : y-((n:ℝ)+1) ≠ 0 := by linarith only [hY,hn]
    have hp : y+((n:ℝ)+1) ≠ 0 := by positivity
    have hDen : 0 < ((n:ℝ)+1)^2-y^2 :=
      (mul_pos (by norm_num) (by positivity)).trans_le (quarticCot_den_lower n hBoth)
    have hR : 1/(y-((n:ℝ)+1))+1/(y+((n:ℝ)+1)) = -quarticCotTerm n y := by
      unfold quarticCotTerm
      field_simp [hm,hp,hDen.ne']
      ring
    unfold cotTerm
    exact_mod_cast hR
  have hC := cot_series_rep' hz
  change (Real.pi:ℂ)*Complex.cot ((Real.pi:ℂ)*(y:ℂ))-1/(y:ℂ) = ∑' n, cotTerm (y:ℂ) n at hC
  simp_rw [hTerm, ← Complex.ofReal_neg] at hC
  rw [← Complex.ofReal_tsum,tsum_neg,Complex.cot_eq_cos_div_sin] at hC
  apply Complex.ofReal_injective
  simpa only [quarticLogSincSlope, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_cos, Complex.ofReal_sin, mul_div_assoc] using hC

theorem quarticLogSincCurvature_eq_neg_tsum {y : ℝ} (hy : 0 < y) (hY : y < 1/2) :
    quarticLogSincCurvature y = -(∑' n, quarticCotCurvatureTerm n y) := by
  have h0 : (0:ℝ) ∈ Ioo (-(1/2):ℝ) (1/2) := by norm_num
  have hS : Summable (fun n => quarticCotTerm n 0) := by simp [quarticCotTerm]
  have hMem : y ∈ Ioo (-(1/2):ℝ) (1/2) := ⟨(by norm_num : (-(1/2):ℝ) < 0).trans hy,hY⟩
  have hD := (hasDerivAt_tsum_of_isPreconnected quarticCot_majorant_summable isOpen_Ioo
    (convex_Ioo _ _).isPreconnected (fun n _ h => quarticCotTerm_deriv n h)
    (fun n _ h => quarticCot_curvature_bound n h) h0 hS hMem).neg
  have hEq : (fun z => -(∑' n, quarticCotTerm n z)) =ᶠ[𝓝 y] quarticLogSincSlope := by
    filter_upwards [isOpen_Ioo.mem_nhds (show y ∈ Ioo (0:ℝ) (1/2) from ⟨hy,hY⟩)] with z hz
    exact (quarticLogSincSlope_eq_neg_tsum hz.1 hz.2).symm
  exact (quarticLogSincSlope_hasDerivAt hy hY).unique (hD.congr_of_eventuallyEq hEq.symm)

end ACS12.NativeCells

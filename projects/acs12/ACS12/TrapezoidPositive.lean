import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! The upper error of a unit trapezoid uses only positive curvature. -/

namespace ACS12

open MeasureTheory Set intervalIntegral

theorem trapezoidalError_unit_eq {f d e : ℝ → ℝ} {a : ℝ}
    (hf : ∀ x ∈ Icc a (a + 1), HasDerivAt f (d x) x)
    (hd : ∀ x ∈ Icc a (a + 1), HasDerivAt d (e x) x)
    (he : ContinuousOn e (Icc a (a + 1))) :
    trapezoidal_error f 1 a (a + 1) =
      ∫ x in a..a + 1, ((x - a) * (a + 1 - x) / 2) * e x := by
  let b := a + 1
  let K (x : ℝ) := (x - a) * (b - x) / 2
  let D (x : ℝ) := (a + b) / 2 - x
  have hab : a ≤ b := by dsimp only [b]; linarith
  have hK (x : ℝ) : HasDerivAt K (D x) x := by
    have h := hasDerivAt_id x
    convert ((h.sub_const a).mul (h.const_sub b)).div_const 2 using 1
    dsimp only [D, id_eq]
    ring
  have hD (x : ℝ) : HasDerivAt D (-1) x := by
    simpa only [D] using (hasDerivAt_id x).const_sub ((a + b) / 2)
  have hKc : Continuous K := by dsimp only [K]; fun_prop
  have hDc : Continuous D := by dsimp only [D]; fun_prop
  have hF : ContinuousOn f (Icc a b) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hCd : ContinuousOn d (Icc a b) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hId := hDc.intervalIntegrable (μ := volume) a b
  have hI₁ := hCd.intervalIntegrable_of_Icc (μ := volume) hab
  have hI₂ := he.intervalIntegrable_of_Icc (μ := volume) hab
  have hI₃ : IntervalIntegrable (fun x : ℝ => (-1 : ℝ)) volume a b := intervalIntegral.intervalIntegrable_const
  have hSub : Ioo (min a b) (max a b) ⊆ Icc a b := by
    rw [min_eq_left hab, max_eq_right hab]
    exact Ioo_subset_Icc_self
  have hParts₁ := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hKc.continuousOn (by rwa [uIcc_of_le hab]) (fun x _ => hK x) (fun x hx => hd x (hSub hx)) hId hI₂
  have hParts₂ := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hDc.continuousOn (by rwa [uIcc_of_le hab]) (fun x _ => hD x) (fun x hx => hf x (hSub hx)) hI₃ hI₁
  symm
  change (∫ x in a..b, K x * e x) = _
  rw [hParts₁, hParts₂]
  simp only [K, sub_self, zero_mul, mul_zero, zero_div, zero_sub]
  have hFa : D a = 1 / 2 := by dsimp only [D, b]; ring
  have hFb : D b = -(1 / 2) := by dsimp only [D, b]; ring
  have hNeg : (∫ x in a..b, (-1 : ℝ) * f x) = -(∫ x in a..b, f x) := by simp
  rw [hFa, hFb, hNeg, trapezoidal_error, trapezoidal_integral_one]
  dsimp only [b]
  ring

theorem trapezoidalError_unit_le {f d e : ℝ → ℝ} {a : ℝ}
    (hf : ∀ x ∈ Icc a (a + 1), HasDerivAt f (d x) x)
    (hd : ∀ x ∈ Icc a (a + 1), HasDerivAt d (e x) x)
    (he : ContinuousOn e (Icc a (a + 1))) :
    trapezoidal_error f 1 a (a + 1) ≤
      (1 / 8) * ∫ x in a..a + 1, max 0 (e x) := by
  let b := a + 1
  let K (x : ℝ) := (x - a) * (b - x) / 2
  have hab : a ≤ b := by dsimp only [b]; linarith
  have hKc : Continuous K := by dsimp only [K]; fun_prop
  have hMc : ContinuousOn (fun x => max 0 (e x)) (Icc a b) :=
    continuous_max.comp_continuousOn (continuousOn_const.prodMk he)
  have hBound (x : ℝ) (hx : x ∈ Icc a b) : K x * e x ≤ (1 / 8) * max 0 (e x) := by
    have hk₀ : 0 ≤ K x := div_nonneg (mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2)) (by norm_num)
    have hk₁ : K x ≤ 1 / 8 := by dsimp only [K, b]; nlinarith only [sq_nonneg (x - a - 1 / 2)]
    exact (mul_le_mul_of_nonneg_left (le_max_right 0 (e x)) hk₀).trans
      (mul_le_mul_of_nonneg_right hk₁ (le_max_left 0 (e x)))
  have hInt := integral_mono_on hab ((hKc.continuousOn.mul he).intervalIntegrable_of_Icc (μ := volume) hab)
    ((continuousOn_const.mul hMc).intervalIntegrable_of_Icc (μ := volume) hab) hBound
  change (∫ x in a..b, K x * e x) ≤ (∫ x in a..b, (1 / 8) * max 0 (e x)) at hInt
  rw [intervalIntegral.integral_const_mul] at hInt
  rw [trapezoidalError_unit_eq hf hd he]
  exact hInt

theorem trapezoidalError_unit_le_of_second_le {f d e : ℝ → ℝ} {a M : ℝ}
    (hf : ∀ x ∈ Icc a (a + 1), HasDerivAt f (d x) x)
    (hd : ∀ x ∈ Icc a (a + 1), HasDerivAt d (e x) x)
    (he : ContinuousOn e (Icc a (a + 1))) (hM : ∀ x ∈ Icc a (a + 1), e x ≤ M) :
    trapezoidal_error f 1 a (a + 1) ≤ M / 12 := by
  let b := a + 1
  let K (x : ℝ) := (x - a) * (b - x) / 2
  let P (x : ℝ) := (x - a) ^ 2 / 4 - (x - a) ^ 3 / 6
  have hab : a ≤ b := by dsimp only [b]; linarith
  have hKc : Continuous K := by dsimp only [K]; fun_prop
  have hP (x : ℝ) : HasDerivAt P (K x) x := by
    have h := (hasDerivAt_id x).sub_const a
    convert ((h.pow 2).div_const 4).sub ((h.pow 3).div_const 6) using 1
    norm_num [K, b, id_eq] <;> ring
  have hKI := hKc.intervalIntegrable (μ := volume) a b
  have hE : (∫ x in a..b, K x) = 1 / 12 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hP x) hKI]
    simp only [P, b, add_sub_cancel_left, sub_self]
    norm_num
  have hBound (x : ℝ) (hx : x ∈ Icc a b) : K x * e x ≤ M * K x := by
    rw [mul_comm M]
    exact mul_le_mul_of_nonneg_left (hM x hx)
      (div_nonneg (mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2)) (by norm_num))
  have hInt := integral_mono_on hab ((hKc.continuousOn.mul he).intervalIntegrable_of_Icc (μ := volume) hab)
    (hKI.const_mul M) hBound
  change (∫ x in a..b, K x * e x) ≤ (∫ x in a..b, M * K x) at hInt
  rw [trapezoidalError_unit_eq hf hd he]
  exact hInt.trans_eq (by rw [intervalIntegral.integral_const_mul, hE]; ring)


theorem trapezoidalError_unit_ge {f d e : ℝ → ℝ} {a : ℝ}
    (hf : ∀ x ∈ Icc a (a + 1), HasDerivAt f (d x) x)
    (hd : ∀ x ∈ Icc a (a + 1), HasDerivAt d (e x) x)
    (he : ContinuousOn e (Icc a (a + 1))) :
    -(1 / 8) * (∫ x in a..a + 1, max 0 (-e x)) ≤ trapezoidal_error f 1 a (a + 1) := by
  have h := trapezoidalError_unit_le (fun x hx => (hf x hx).neg) (fun x hx => (hd x hx).neg) he.neg
  rw [trapezoidalError_unit_eq (fun x hx => (hf x hx).neg) (fun x hx => (hd x hx).neg) he.neg] at h
  change (∫ x in a..a + 1, ((x - a) * (a + 1 - x) / 2) * (-e x)) ≤ _ at h
  simp only [mul_neg,intervalIntegral.integral_neg] at h
  rw [trapezoidalError_unit_eq hf hd he]
  linarith only [h]


/-- The error of the left unit sample is bounded by total downward variation. -/
theorem leftSample_error_le {f d : ℝ → ℝ} {a : ℝ}
    (hf : ∀ x ∈ Icc a (a + 1), HasDerivAt f (d x) x)
    (hd : ContinuousOn d (Icc a (a + 1))) :
    f a - (∫ x in a..a + 1, f x) ≤ ∫ x in a..a + 1, max 0 (-d x) := by
  let b := a + 1
  let K (x : ℝ) := b - x
  have hab : a ≤ b := le_add_of_nonneg_right zero_le_one
  have hK (x : ℝ) : HasDerivAt K (-1) x := (hasDerivAt_id x).const_sub b
  have hKC : Continuous K := by unfold K; fun_prop
  have hC : ContinuousOn f (Icc a b) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hdI := hd.intervalIntegrable_of_Icc (μ := volume) hab
  have hSub : Ioo (min a b) (max a b) ⊆ Icc a b := by
    rw [min_eq_left hab,max_eq_right hab]
    exact Ioo_subset_Icc_self
  have hI := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hKC.continuousOn (by rwa [uIcc_of_le hab]) (fun x _ => hK x) (fun x hx => hf x (hSub hx))
    (intervalIntegral.intervalIntegrable_const (c := (-1 : ℝ))) hdI
  have hEq : f a - (∫ x in a..b, f x) = ∫ x in a..b, K x * (-d x) := by
    have hKa : K a = 1 := by dsimp only [K,b]; ring
    have hKb : K b = 0 := sub_self b
    rw [hKa,hKb,zero_mul,one_mul,zero_sub] at hI
    simp only [neg_one_mul,intervalIntegral.integral_neg] at hI
    simp only [mul_neg,intervalIntegral.integral_neg]
    linarith only [hI]
  rw [hEq]
  apply integral_mono_on hab
    ((hKC.continuousOn.mul hd.neg).intervalIntegrable_of_Icc hab)
    ((continuous_max.comp_continuousOn (continuousOn_const.prodMk hd.neg)).intervalIntegrable_of_Icc hab)
  intro x hx
  have hK₀ : 0 ≤ K x := sub_nonneg.mpr hx.2
  have hK₁ : K x ≤ 1 := by dsimp only [K,b]; linarith only [hx.1]
  exact (mul_le_mul_of_nonneg_left (le_max_right 0 (-d x)) hK₀).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hK₁ (le_max_left 0 (-d x)))

end ACS12

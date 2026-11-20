import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Fourier normalization of the positive Poisson kernel on the line. -/

namespace ACS12.Poisson

open MeasureTheory Set
open scoped FourierTransform

noncomputable def kernel (a x : ℝ) : ℝ := a / (Real.pi * (a ^ 2 + x ^ 2))

theorem kernel_pos {a : ℝ} (ha : 0 < a) (x : ℝ) : 0 < kernel a x := by
  unfold kernel
  positivity

theorem integrable_kernel {a : ℝ} (ha : 0 < a) : Integrable (kernel a) := by
  have hi := ((integrable_comp_mul_left_iff (fun x : ℝ => (1 + x ^ 2)⁻¹)
    (inv_ne_zero ha.ne')).mpr integrable_inv_one_add_sq).const_mul (1 / (Real.pi * a))
  apply hi.congr
  refine Filter.Eventually.of_forall fun x => ?_
  have hx : 0 < a ^ 2 + x ^ 2 := by positivity
  dsimp only [kernel]
  field_simp [ha.ne', Real.pi_ne_zero, hx.ne']

noncomputable def damping (a t : ℝ) : ℝ := Real.exp (-a * |t|)

theorem integrable_damping {a : ℝ} (ha : 0 < a) : Integrable (damping a) := by
  have hi := integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) 0
  have hj := integrableOn_exp_mul_Iic ha 0
  have hleft : IntegrableOn (damping a) (Iic 0) := by
    refine hj.congr_fun ?_ measurableSet_Iic
    intro x hx
    unfold damping
    rw [abs_of_nonpos hx, mul_neg, neg_mul, neg_neg]
  have hright : IntegrableOn (damping a) (Ioi 0) := by
    refine hi.congr_fun ?_ measurableSet_Ioi
    intro x hx
    unfold damping
    rw [abs_of_pos hx]
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact hleft.union hright

private theorem exponential_pair {a : ℝ} (ha : 0 < a) (x : ℝ) :
    (-1 : ℂ) / (-(a : ℂ) + (x : ℂ) * Complex.I) -
      1 / (-(a : ℂ) - (x : ℂ) * Complex.I) =
      ((2 * a / (a ^ 2 + x ^ 2) : ℝ) : ℂ) := by
  have h₁ : (-(a : ℂ) + (x : ℂ) * Complex.I) ≠ 0 := by
    intro hz
    have h := congrArg Complex.re hz
    simp [Complex.mul_re] at h
    exact ha.ne' h
  have h₂ : (-(a : ℂ) - (x : ℂ) * Complex.I) ≠ 0 := by
    intro hz
    have h := congrArg Complex.re hz
    simp [Complex.mul_re] at h
    exact ha.ne' h
  have hProd : (-(a : ℂ) + (x : ℂ) * Complex.I) * (-(a : ℂ) - (x : ℂ) * Complex.I) =
      (a : ℂ) ^ 2 + (x : ℂ) ^ 2 := by
    linear_combination -((x : ℂ) ^ 2) * Complex.I_sq
  push_cast
  rw [← hProd]
  field_simp [h₁, h₂]
  ring

theorem integral_damping_exp {a : ℝ} (ha : 0 < a) (x : ℝ) :
    (∫ t : ℝ, (damping a t : ℂ) * Complex.exp ((x : ℂ) * (t : ℂ) * Complex.I)) =
      ((2 * a / (a ^ 2 + x ^ 2) : ℝ) : ℂ) := by
  let f (t : ℝ) := (damping a t : ℂ) * Complex.exp ((x : ℂ) * (t : ℂ) * Complex.I)
  have hf : Integrable f := by
    refine (integrable_damping ha).mono' (by unfold f damping; fun_prop) ?_
    exact Filter.Eventually.of_forall fun t => by
      dsimp only [f]
      have hD : 0 ≤ damping a t := (Real.exp_pos _).le
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hD, Complex.norm_exp]
      simp [Complex.mul_re, Complex.mul_im]
  let cp : ℂ := -(a : ℂ) + (x : ℂ) * Complex.I
  let cn : ℂ := (a : ℂ) + (x : ℂ) * Complex.I
  have hcp : cp.re < 0 := by simpa [cp, Complex.mul_re] using ha
  have hcn : 0 < cn.re := by simpa [cn, Complex.mul_re] using ha
  have hpE : (∫ t : ℝ in Ioi 0, f t) = ∫ t : ℝ in Ioi 0, Complex.exp (cp * t) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only [f, damping, cp]
    rw [abs_of_pos ht, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hnE : (∫ t : ℝ in Iic 0, f t) = ∫ t : ℝ in Iic 0, Complex.exp (cn * t) := by
    apply setIntegral_congr_fun measurableSet_Iic
    intro t ht
    dsimp only [f, damping, cn]
    rw [abs_of_nonpos ht, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hsplit := setIntegral_union (Iic_disjoint_Ioi le_rfl)
    (measurableSet_Ioi (a := (0 : ℝ))) hf.integrableOn hf.integrableOn
  rw [Iic_union_Ioi, Measure.restrict_univ] at hsplit
  change (∫ t : ℝ, f t) = _
  rw [hsplit, hnE, hpE, integral_exp_mul_complex_Ioi hcp, integral_exp_mul_complex_Iic hcn]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [show cn = -(-(a : ℂ) - (x : ℂ) * Complex.I) by dsimp [cn]; ring, div_neg, add_comm,
    ← sub_eq_add_neg]
  exact exponential_pair ha x

/-- The Poisson law has the exact characteristic function exp(-a |t|). -/
theorem integral_kernel_exp {a : ℝ} (ha : 0 < a) (t : ℝ) :
    (∫ x : ℝ, (kernel a x : ℂ) * Complex.exp ((x : ℂ) * (t : ℂ) * Complex.I)) =
      (damping a t : ℂ) := by
  let f (x : ℝ) := (damping a x : ℂ)
  let c := 2 * Real.pi
  have hc : 0 < c := by dsimp [c]; positivity
  have hf : Integrable f := (integrable_damping ha).ofReal
  have hFc : 𝓕 f = fun w : ℝ => ((c * kernel a (c * w) : ℝ) : ℂ) := by
    funext w
    rw [Real.fourier_real_eq_integral_exp_smul]
    have hE := integral_damping_exp ha (-c * w)
    have hEq :
        (∫ x : ℝ, Complex.exp (↑(-2 * Real.pi * x * w) * Complex.I) • f x) =
        ∫ x : ℝ, (damping a x : ℂ) * Complex.exp ((↑(-c * w) : ℂ) * (x : ℂ) * Complex.I) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp only [f, smul_eq_mul, mul_comm _ (↑(damping a x) : ℂ)]
        congr 2
        dsimp only [c]
        push_cast
        ring
    rw [hEq, hE]
    congr 1
    unfold kernel
    have h₀ : 0 < a ^ 2 + (c * w) ^ 2 := by positivity
    rw [neg_mul, neg_sq]
    dsimp only [c] at h₀ ⊢
    field_simp [Real.pi_ne_zero, h₀.ne']
  have hFi : Integrable (𝓕 f) := by
    rw [hFc]
    exact (((integrable_comp_mul_left_iff (kernel a) hc.ne').mpr
      (integrable_kernel ha)).const_mul c).ofReal
  have hCont : Continuous f := by unfold f damping; fun_prop
  have h := hf.fourierInv_fourier_eq hFi (hCont.continuousAt (x := t))
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul, hFc] at h
  let g (x : ℝ) := (kernel a x : ℂ) * Complex.exp ((x : ℂ) * (t : ℂ) * Complex.I)
  have he :
      (∫ x : ℝ, Complex.exp (↑(-2 * Real.pi * x * -t) * Complex.I) •
        (↑(c * kernel a (c * x)) : ℂ)) =
      (c : ℂ) * ∫ x : ℝ, g (c * x) := by
    calc
      _ = ∫ x : ℝ, (c : ℂ) * g (c * x) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          dsimp only [g, c]
          rw [smul_eq_mul]
          push_cast
          rw [show ((-2 : ℂ) * ↑Real.pi * ↑x * -↑t) = 2 * ↑Real.pi * ↑x * ↑t by ring]
          ring
      _ = _ := integral_const_mul (μ := volume) (c : ℂ) (fun x : ℝ => g (c * x))
  rw [he, Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr hc)] at h
  change (c : ℂ) * (((c⁻¹ : ℝ) : ℂ) * (∫ y : ℝ, g y)) = f t at h
  rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hc.ne', Complex.ofReal_one, one_mul] at h
  exact h

end ACS12.Poisson

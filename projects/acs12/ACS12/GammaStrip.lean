import ACS12.GammaMeasure
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Fourier.Inversion

/-! The beta profile on its open strip and bounds on compact substrips. -/

namespace ACS12.GammaMeasure

open MeasureTheory Set Filter
open scoped Topology FourierTransform

private noncomputable def stripBase (z : ℂ) : ℂ := 2 * Complex.cosh (z / 2)

noncomputable def stripProfile (p : ℝ) (z : ℂ) : ℂ :=
  stripBase z ^ ((-p : ℝ) : ℂ)

private theorem stripBase_re (z : ℂ) :
    (stripBase z).re = 2 * Real.cosh (z.re / 2) * Real.cos (z.im / 2) := by
  have hdiv : z / 2 = ((z.re / 2 : ℝ) : ℂ) + ((z.im / 2 : ℝ) : ℂ) * Complex.I := by
    rw [Complex.ofReal_div, Complex.ofReal_div]
    push_cast
    calc
      z / 2 = ((z.re : ℂ) + (z.im : ℂ) * Complex.I) / 2 := by
        rw [Complex.re_add_im]
      _ = _ := by ring
  rw [stripBase, hdiv, Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I,
    ← Complex.ofReal_cosh, ← Complex.ofReal_cos, ← Complex.ofReal_sinh, ← Complex.ofReal_sin]
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, sub_zero, add_zero]
  ring

private theorem stripBase_re_pos {z : ℂ} (hz : |z.im| < Real.pi) :
    0 < (stripBase z).re := by
  have hc : 0 < Real.cos (z.im / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [(abs_lt.mp hz).1, (abs_lt.mp hz).2]
  rw [stripBase_re]
  exact mul_pos (mul_pos (by norm_num) (Real.cosh_pos _)) hc

theorem stripProfile_differentiableAt (p : ℝ) {z : ℂ} (hz : |z.im| < Real.pi) :
    DifferentiableAt ℂ (stripProfile p) z := by
  apply DifferentiableAt.cpow_const (f := stripBase)
  · unfold stripBase
    fun_prop
  · exact Complex.mem_slitPlane_iff.mpr (Or.inl (stripBase_re_pos hz))

theorem stripProfile_real (p x : ℝ) :
    stripProfile p x = (betaProfile p x : ℂ) := by
  rw [betaProfile_eq_cosh, Complex.ofReal_cpow (by positivity), stripProfile, stripBase]
  push_cast
  rfl

theorem stripProfile_imaginary (p y : ℝ) (hy : |y| < Real.pi) :
    stripProfile p ((y : ℂ) * Complex.I) = ((2 * Real.cos (y / 2)) ^ (-p) : ℝ) := by
  have hc : 0 < Real.cos (y / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [(abs_lt.mp hy).1, (abs_lt.mp hy).2]
  rw [Complex.ofReal_cpow (by positivity), stripProfile, stripBase,
    show (y : ℂ) * Complex.I / 2 = ((y / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.cosh_mul_I]
  push_cast
  rfl

private theorem exp_le_two_cosh (x : ℝ) :
    Real.exp (|x| / 2) ≤ 2 * Real.cosh (x / 2) := by
  rw [show |x| / 2 = |x / 2| by rw [abs_div, abs_of_pos (by norm_num : 0 < (2 : ℝ))],
    ← Real.cosh_abs (x := x / 2),
    Real.cosh_eq]
  linarith [Real.exp_pos (-|x / 2|)]

theorem norm_stripProfile_le {p r : ℝ} (hp : 0 < p) (hr : r < Real.pi) {z : ℂ}
    (hz : |z.im| ≤ r) :
    ‖stripProfile p z‖ ≤ (Real.cos (r / 2)) ^ (-p) * Real.exp (-(p / 2) * |z.re|) := by
  have hr0 : 0 ≤ r := (abs_nonneg _).trans hz
  have hc : 0 < Real.cos (r / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have hc_le : Real.cos (r / 2) ≤ Real.cos (z.im / 2) := by
    rw [← Real.cos_abs (z.im / 2), abs_div, abs_of_pos (show 0 < (2 : ℝ) by norm_num)]
    exact Real.antitoneOn_cos ⟨by positivity, by linarith⟩ ⟨by positivity, by linarith⟩
      (by linarith)
  have hb : Real.cos (r / 2) * Real.exp (|z.re| / 2) ≤ ‖stripBase z‖ := by
    calc
      _ ≤ Real.cos (r / 2) * (2 * Real.cosh (z.re / 2)) :=
        mul_le_mul_of_nonneg_left (exp_le_two_cosh _) hc.le
      _ ≤ (stripBase z).re := by
        rw [stripBase_re, mul_comm (Real.cos (r / 2))]
        exact mul_le_mul_of_nonneg_left hc_le (by positivity)
      _ ≤ _ := Complex.re_le_norm _
  rw [stripProfile, Complex.norm_cpow_real]
  calc
    _ ≤ (Real.cos (r / 2) * Real.exp (|z.re| / 2)) ^ (-p) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hb (neg_nonpos.mpr hp.le)
    _ = _ := by rw [Real.mul_rpow hc.le (Real.exp_pos _).le, ← Real.exp_mul]; congr 2; ring

private noncomputable def stripKernel (p t : ℝ) (z : ℂ) : ℂ :=
  stripProfile p z * Complex.exp ((t : ℂ) * z * Complex.I)

private theorem stripKernel_differentiableAt (p t : ℝ) {z : ℂ} (hz : |z.im| < Real.pi) :
    DifferentiableAt ℂ (stripKernel p t) z :=
  (stripProfile_differentiableAt p hz).mul (by fun_prop)

private theorem norm_stripKernel_le {p r : ℝ} (hp : 0 < p) (hr : r < Real.pi) (t : ℝ)
    {z : ℂ} (hz : |z.im| ≤ r) :
    ‖stripKernel p t z‖ ≤
      ((Real.cos (r / 2)) ^ (-p) * Real.exp (|t| * r)) * Real.exp (-(p / 2) * |z.re|) := by
  have he : ‖Complex.exp ((t : ℂ) * z * Complex.I)‖ ≤ Real.exp (|t| * r) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, zero_sub, add_zero]
    calc
      _ ≤ |t * z.im| := neg_le_abs _
      _ ≤ _ := by rw [abs_mul]; gcongr
  have hcos : 0 ≤ Real.cos (r / 2) := by
    apply (Real.cos_pos_of_mem_Ioo ?_).le
    have hr0 : 0 ≤ r := (abs_nonneg _).trans hz
    constructor <;> linarith [Real.pi_pos]
  rw [stripKernel, norm_mul]
  calc
    _ ≤ ((Real.cos (r / 2)) ^ (-p) * Real.exp (-(p / 2) * |z.re|)) *
        Real.exp (|t| * r) :=
      mul_le_mul (norm_stripProfile_le hp hr hz) he (norm_nonneg _)
        (mul_nonneg (Real.rpow_nonneg hcos _) (Real.exp_pos _).le)
    _ = _ := by ring

private theorem integrable_exp_neg_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ => Real.exp (-a * |x|)) := by
  have left : IntegrableOn (fun x : ℝ => Real.exp (-a * |x|)) (Iic 0) :=
    (integrableOn_exp_mul_Iic ha 0).congr_fun
      (fun x hx => by rw [abs_of_nonpos (mem_Iic.mp hx)]; ring_nf) measurableSet_Iic
  have right : IntegrableOn (fun x : ℝ => Real.exp (-a * |x|)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0).congr_fun
      (fun x hx => by rw [abs_of_pos (mem_Ioi.mp hx)]) measurableSet_Ioi
  simpa only [Iic_union_Ioi, integrableOn_univ] using left.union right

private theorem stripKernel_line_integrable {p : ℝ} (hp : 0 < p) (t : ℝ)
    {y : ℝ} (hy : |y| < Real.pi) :
    Integrable (fun x : ℝ => stripKernel p t ((x : ℂ) + (y : ℂ) * Complex.I)) := by
  have hc : Continuous (fun x : ℝ => stripKernel p t ((x : ℂ) + (y : ℂ) * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (stripKernel_differentiableAt p t
      (by simpa [Complex.mul_im] using hy)).continuousAt.comp (by fun_prop)
  refine ((integrable_exp_neg_abs (show 0 < p / 2 by positivity)).const_mul
    ((Real.cos (|y| / 2)) ^ (-p) * Real.exp (|t| * |y|))).mono' hc.aestronglyMeasurable ?_
  exact Eventually.of_forall fun x => by
    simpa [Complex.mul_re, Complex.mul_im] using
      norm_stripKernel_le hp hy t
        (z := (x : ℂ) + (y : ℂ) * Complex.I) (by simp [Complex.mul_im])

private theorem abs_le_of_mem_uIcc_zero {y s : ℝ} (hs : s ∈ uIcc 0 y) : |s| ≤ |y| := by
  apply abs_le.mpr
  rcases mem_uIcc.mp hs with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
  · rw [abs_of_nonneg (h₀.trans h₁)]
    constructor <;> linarith
  · rw [abs_of_nonpos (h₀.trans h₁)]
    constructor <;> linarith

private theorem stripKernel_vertical_limit {p : ℝ} (hp : 0 < p) (t : ℝ)
    {y : ℝ} (hy : |y| < Real.pi) (sign : ℝ) (hsign : |sign| = 1) :
    Tendsto (fun X : ℝ => ∫ s in 0..y, stripKernel p t ((sign * X : ℝ) + (s : ℂ) * Complex.I))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let C := (Real.cos (|y| / 2)) ^ (-p) * Real.exp (|t| * |y|)
  have hlim : Tendsto (fun X : ℝ => Real.exp (-(p / 2) * X)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by linarith : -(p / 2) < 0))
  have hlim' : Tendsto (fun X : ℝ => C * Real.exp (-(p / 2) * X) * |y|) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using (hlim.const_mul C).mul_const |y|
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with X hX
  conv_rhs => rw [show |y| = |y - 0| by rw [sub_zero]]
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro s hs
  have h := norm_stripKernel_le hp hy t
    (z := ((sign * X : ℝ) : ℂ) + (s : ℂ) * Complex.I)
    (by simpa [Complex.mul_im] using abs_le_of_mem_uIcc_zero (uIoc_subset_uIcc hs))
  simpa [C, Complex.mul_re, Complex.mul_im, abs_mul, hsign, abs_of_nonneg hX] using h

/-- The Fourier integrand has the same integral along every horizontal
line inside the strip. -/
private theorem stripKernel_integral_shift {p : ℝ} (hp : 0 < p) (t : ℝ) {y : ℝ} (hy : |y| < Real.pi) :
    (∫ x : ℝ, stripKernel p t (x : ℂ)) =
      ∫ x : ℝ, stripKernel p t ((x : ℂ) + (y : ℂ) * Complex.I) := by
  have h0 : |(0 : ℝ)| < Real.pi := by simpa using Real.pi_pos
  have lower := intervalIntegral_tendsto_integral
    (stripKernel_line_integrable hp t h0) tendsto_neg_atTop_atBot tendsto_id
  have upper := intervalIntegral_tendsto_integral
    (stripKernel_line_integrable hp t hy) tendsto_neg_atTop_atBot tendsto_id
  have right := stripKernel_vertical_limit hp t hy 1 (by norm_num)
  have left := stripKernel_vertical_limit hp t hy (-1) (by norm_num)
  have hlim := (((lower.sub upper).add (right.const_smul Complex.I)).sub
    (left.const_smul Complex.I))
  have hzero : ∀ X : ℝ,
      (∫ x : ℝ in -X..X, stripKernel p t ((x : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)) -
        (∫ x : ℝ in -X..X, stripKernel p t ((x : ℂ) + (y : ℂ) * Complex.I)) +
        Complex.I • (∫ s in 0..y, stripKernel p t ((1 * X : ℝ) + (s : ℂ) * Complex.I)) -
        Complex.I • (∫ s in 0..y, stripKernel p t (((-1) * X : ℝ) + (s : ℂ) * Complex.I)) = 0 := by
    intro X
    have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      (stripKernel p t) ⟨-X, 0⟩ ⟨X, y⟩ (by
        intro z hz
        exact (stripKernel_differentiableAt p t
          ((abs_le_of_mem_uIcc_zero hz.2).trans_lt hy)).differentiableWithinAt)
    simpa using hrect
  have h := tendsto_nhds_unique (hlim.congr hzero) tendsto_const_nhds
  exact sub_eq_zero.mp (by simpa using h)

private theorem stripKernel_on_line (p t x y : ℝ) :
    stripKernel p t ((x : ℂ) + (y : ℂ) * Complex.I) =
      (Real.exp (-t * y) : ℂ) *
        (stripProfile p ((x : ℂ) + (y : ℂ) * Complex.I) *
          Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) := by
  have he : (t : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) * Complex.I =
      ((-t * y : ℝ) : ℂ) + (t : ℂ) * (x : ℂ) * Complex.I := by
    push_cast
    calc
      _ = (t : ℂ) * (x : ℂ) * Complex.I + (t : ℂ) * (y : ℂ) * (Complex.I * Complex.I) := by
        ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [stripKernel, he, Complex.exp_add, Complex.ofReal_exp]
  ring

private theorem stripProfile_integral_exp {p : ℝ} (hp : 0 < p) (t : ℝ)
    {y : ℝ} (hy : |y| < Real.pi) :
    (∫ x : ℝ, stripProfile p ((x : ℂ) + (y : ℂ) * Complex.I) *
      Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) =
        (Real.exp (t * y) : ℂ) *
          (↑(‖Complex.Gamma ((p / 2 : ℝ) + (t : ℂ) * Complex.I)‖ ^ 2) : ℂ) /
            Complex.Gamma (p : ℂ) := by
  have h := stripKernel_integral_shift hp t hy
  simp_rw [stripKernel_on_line] at h
  have h' := h.trans (integral_const_mul (μ := volume) (Real.exp (-t * y) : ℂ) (fun x : ℝ =>
    stripProfile p ((x : ℂ) + (y : ℂ) * Complex.I) *
      Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)))
  have h₀ : (∫ x : ℝ, stripKernel p t (x : ℂ)) =
      (↑(‖Complex.Gamma ((p / 2 : ℝ) + (t : ℂ) * Complex.I)‖ ^ 2) : ℂ) /
        Complex.Gamma (p : ℂ) := by
    simpa only [stripKernel, stripProfile_real] using gamma_product_fourier hp t
  rw [h₀] at h'
  have hprod : (Real.exp (t * y) : ℂ) * (Real.exp (-t * y) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, show t * y + -t * y = 0 by ring]
    simp
  rw [mul_div_assoc, h', ← mul_assoc, hprod, one_mul]
  rfl

private theorem stripProfile_integral_density {p : ℝ} (hp : 0 < p) (t : ℝ)
    {y : ℝ} (hy : |y| < Real.pi) :
    (∫ x : ℝ, stripProfile p ((x : ℂ) + (y : ℂ) * Complex.I) *
      Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) =
        ((Real.pi / (2 : ℝ) ^ (p - 1) * (gammaDensity p t * Real.exp (t * y)) : ℝ) : ℂ) := by
  rw [stripProfile_integral_exp hp t hy, Complex.Gamma_ofReal,
    ← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_inj, gammaDensity]
  field_simp [Real.pi_ne_zero, (Real.Gamma_pos_of_pos hp).ne',
    (Real.rpow_pos_of_pos (by norm_num : 0 < (2 : ℝ)) (p - 1)).ne']

theorem continuous_gammaDensity {p : ℝ} (hp : 0 < p) : Continuous (gammaDensity p) := by
  have hg : Continuous (fun t : ℝ => Complex.Gamma ((p / 2 : ℝ) + (t : ℂ) * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (Complex.continuousAt_Gamma _ ?_).comp (by fun_prop)
    intro n h
    have hr := congrArg Complex.re h
    simp [Complex.mul_re] at hr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  unfold gammaDensity
  exact (continuous_const.mul (hg.norm.pow 2)).div_const _

private theorem norm_stripProfile_integral_le {p r : ℝ} (hp : 0 < p) (hr : r < Real.pi)
    (t y : ℝ) (hy : |y| ≤ r) :
    ‖∫ x : ℝ, stripProfile p ((x : ℂ) + (y : ℂ) * Complex.I) *
      Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)‖ ≤
        (Real.cos (r / 2)) ^ (-p) * ∫ x : ℝ, Real.exp (-(p / 2) * |x|) := by
  let C := (Real.cos (r / 2)) ^ (-p)
  rw [← integral_const_mul C (fun x : ℝ => Real.exp (-(p / 2) * |x|))]
  refine norm_integral_le_of_norm_le ((integrable_exp_neg_abs (by positivity : 0 < p / 2)).const_mul C)
    (Eventually.of_forall fun x => ?_)
  have h := norm_stripProfile_le hp hr
    (z := (x : ℂ) + (y : ℂ) * Complex.I) (by simpa [Complex.mul_im] using hy)
  simpa [C, Complex.mul_re, Complex.mul_im, norm_mul, Complex.norm_exp] using h

theorem gammaDensity_exp_bound {p r : ℝ} (hp : 0 < p) (hr : r < Real.pi) (hr₀ : 0 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, gammaDensity p t ≤ C * Real.exp (-r * |t|) := by
  let B := (Real.cos (r / 2)) ^ (-p) * ∫ x : ℝ, Real.exp (-(p / 2) * |x|)
  let A := Real.pi / (2 : ℝ) ^ (p - 1)
  have hA : 0 < A := div_pos Real.pi_pos (Real.rpow_pos_of_pos (by norm_num) _)
  have hB : 0 ≤ B :=
    (norm_nonneg _).trans (norm_stripProfile_integral_le hp hr 0 0 (by simpa))
  refine ⟨B / A, div_nonneg hB hA.le, fun t => ?_⟩
  let y := if 0 ≤ t then r else -r
  have hy : |y| = r := by
    dsimp only [y]
    split_ifs <;> simp [abs_of_nonneg hr₀]
  have hty : t * y = r * |t| := by
    dsimp only [y]
    split_ifs with ht
    · rw [abs_of_nonneg ht, mul_comm]
    · rw [abs_of_neg (lt_of_not_ge ht)]
      ring
  have h := norm_stripProfile_integral_le hp hr t y hy.le
  rw [stripProfile_integral_density hp t (hy ▸ hr), Complex.norm_real,
    Real.norm_of_nonneg (mul_nonneg hA.le
      (mul_nonneg (gammaDensity_pos hp t).le (Real.exp_pos _).le)), hty] at h
  have h' : gammaDensity p t * Real.exp (r * |t|) ≤ B / A :=
    (le_div_iff₀ hA).mpr (by simpa only [mul_comm _ A] using h)
  calc
    gammaDensity p t ≤ (B / A) / Real.exp (r * |t|) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr h'
    _ = _ := by rw [div_eq_mul_inv, ← Real.exp_neg]; congr 2; ring

theorem gammaDensity_exp_integrable {p y : ℝ} (hp : 0 < p) (hy : |y| < Real.pi) :
    Integrable (fun t : ℝ => gammaDensity p t * Real.exp (t * y)) := by
  obtain ⟨r, hyr, hr⟩ := exists_between hy
  obtain ⟨C, hC, hbound⟩ := gammaDensity_exp_bound hp hr ((abs_nonneg _).trans hyr.le)
  refine ((integrable_exp_neg_abs (sub_pos.mpr hyr)).const_mul C).mono'
    ((continuous_gammaDensity hp).mul (by fun_prop)).aestronglyMeasurable ?_
  exact Eventually.of_forall fun t => by
    rw [Real.norm_of_nonneg (mul_nonneg (gammaDensity_pos hp t).le (Real.exp_pos _).le)]
    calc
      _ ≤ (C * Real.exp (-r * |t|)) * Real.exp (t * y) :=
        mul_le_mul_of_nonneg_right (hbound t) (Real.exp_pos _).le
      _ ≤ C * Real.exp (-(r - |y|) * |t|) := by
        rw [mul_assoc, ← Real.exp_add]
        apply mul_le_mul_of_nonneg_left _ hC
        apply Real.exp_le_exp.mpr
        have h : t * y ≤ |t| * |y| := by
          rw [← abs_mul]
          exact le_abs_self _
        linarith

private theorem fourier_stripProfile {p : ℝ} (hp : 0 < p) {y : ℝ} (hy : |y| < Real.pi)
    (w : ℝ) :
    𝓕 (fun x : ℝ => stripProfile p ((x : ℂ) + (y : ℂ) * Complex.I)) w =
      ((Real.pi / (2 : ℝ) ^ (p - 1) *
        (gammaDensity p (-2 * Real.pi * w) * Real.exp ((-2 * Real.pi * w) * y)) : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  convert stripProfile_integral_density hp (-2 * Real.pi * w) hy using 1
  congr 1
  ext x
  rw [smul_eq_mul, mul_comm]
  congr 2
  push_cast
  ring

/-- The Gamma density integrates against an exponential exactly throughout
the strip used by the physical chord and by the cell kernels. -/
theorem gammaDensity_exp_moment {p y : ℝ} (hp : 0 < p) (hy : |y| < Real.pi) :
    (∫ t : ℝ, gammaDensity p t * Real.exp (t * y)) = (Real.cos (y / 2)) ^ (-p) := by
  let f (x : ℝ) := stripProfile p ((x : ℂ) + (y : ℂ) * Complex.I)
  let g (t : ℝ) : ℝ := gammaDensity p t * Real.exp (t * y)
  let a := Real.pi / (2 : ℝ) ^ (p - 1)
  let b := -2 * Real.pi
  have hb : b < 0 := by dsimp [b]; linarith [Real.pi_pos]
  have hg : Integrable g := gammaDensity_exp_integrable hp hy
  have hf : Integrable f := by simpa [f, stripKernel] using stripKernel_line_integrable hp 0 hy
  have hF : 𝓕 f = fun w : ℝ => ((a * g (b * w) : ℝ) : ℂ) :=
    funext (fourier_stripProfile hp hy)
  have hFi : Integrable (𝓕 f) := by
    rw [hF]
    exact (((integrable_comp_mul_left_iff g hb.ne).mpr hg).const_mul a).ofReal
  have hc : ContinuousAt f 0 := by
    exact (stripProfile_differentiableAt p (by simpa [Complex.mul_im] using hy)).continuousAt.comp
      (by fun_prop)
  have hi := hf.fourierInv_fourier_eq hFi hc
  rw [Real.fourierInv_eq_fourier_neg, neg_zero, Real.fourier_real_eq_integral_exp_smul] at hi
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul, hF] at hi
  change (∫ w : ℝ, ((a * g (b * w) : ℝ) : ℂ)) =
    stripProfile p (((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I) at hi
  rw [Complex.ofReal_zero, zero_add, stripProfile_imaginary p y hy] at hi
  have hreal := Complex.ofReal_injective
    ((integral_ofReal (μ := volume) (f := fun w : ℝ => a * g (b * w))).symm.trans hi)
  have hinv := (integral_const_mul (μ := volume) a (fun w => g (b * w))).symm.trans hreal
  rw [Measure.integral_comp_mul_left g b, smul_eq_mul, ← mul_assoc] at hinv
  have h₂ : (2 : ℝ) ^ p = (2 : ℝ) ^ (p - 1) * 2 := by
    calc
      (2 : ℝ) ^ p = (2 : ℝ) ^ ((p - 1) + 1) := by rw [sub_add_cancel]
      _ = _ := by rw [Real.rpow_add (by norm_num), Real.rpow_one]
  have hab : a * |b⁻¹| = (2 : ℝ) ^ (-p) := by
    rw [abs_inv, abs_of_neg hb, Real.rpow_neg (by norm_num), h₂]
    dsimp only [a, b]
    field_simp [Real.pi_ne_zero, (Real.rpow_pos_of_pos (by norm_num : 0 < (2 : ℝ)) _).ne']
  have hcos : 0 < Real.cos (y / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [(abs_lt.mp hy).1, (abs_lt.mp hy).2]
  rw [hab, Real.mul_rpow (by norm_num) hcos.le] at hinv
  exact mul_left_cancel₀ (Real.rpow_pos_of_pos (by norm_num) _).ne' hinv

/-- The equivalent positive-half-axis form of the strip moment. -/
theorem gammaDensity_cosh_moment {p y : ℝ} (hp : 0 < p) (hy : |y| < Real.pi) :
    (∫ t : ℝ in Ioi 0, 2 * gammaDensity p t * Real.cosh (t * y)) =
      (Real.cos (y / 2)) ^ (-p) := by
  let f (t : ℝ) := gammaDensity p t * Real.exp (t * y)
  have hf : Integrable f := gammaDensity_exp_integrable hp hy
  have he (t : ℝ) : gammaDensity p (-t) = gammaDensity p t := gammaDensity_even p t
  have hneg : Integrable (fun t : ℝ => f (-t)) := by
    simpa only [f, he, neg_mul, mul_neg] using
      gammaDensity_exp_integrable hp (y := -y) (by simpa only [abs_neg] using hy)
  calc
    _ = ∫ t : ℝ in Ioi 0, f t + f (-t) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      dsimp only [f]
      rw [he, neg_mul, Real.cosh_eq]
      ring
    _ = (∫ t : ℝ in Ioi 0, f t) + ∫ t : ℝ in Iic 0, f t := by
      rw [integral_add hf.integrableOn hneg.integrableOn, integral_comp_neg_Ioi, neg_zero]
    _ = ∫ t : ℝ, f t := by
      simpa only [compl_Ioi] using integral_add_compl measurableSet_Ioi hf
    _ = _ := gammaDensity_exp_moment hp hy

end ACS12.GammaMeasure

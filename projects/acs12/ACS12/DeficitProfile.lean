import ACS12.GaussianSine
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Absolute bounds for the profile and integrated sine bracket in the
cumulative Gamma comparison. -/

namespace ACS12.GammaDeficit

open MeasureTheory Set Filter

noncomputable def sinhProfile (p t : ℝ) : ℝ := (2 * Real.sinh (t / 2)) ^ (-p)

noncomputable def deficitProfile (p t : ℝ) : ℝ := t ^ (-p) - sinhProfile p t

noncomputable def sineBracket (U t : ℝ) : ℝ :=
  Real.sin (U * t) - U * t * Real.cos (U * t)

theorem deficitProfile_nonneg {p t : ℝ} (hp : 0 < p) (ht : 0 < t) :
    0 ≤ deficitProfile p t := by
  have h := Real.self_le_sinh_iff.mpr (show 0 ≤ t / 2 by positivity)
  exact sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos ht (by linarith) (neg_nonpos.mpr hp.le))

theorem deficitProfile_le_power (p t : ℝ) (ht : 0 < t) :
    deficitProfile p t ≤ t ^ (-p) := by
  have h : 0 < 2 * Real.sinh (t / 2) := by
    exact mul_pos (by norm_num) (Real.sinh_pos_iff.mpr (by positivity))
  exact sub_le_self _ (Real.rpow_nonneg h.le _)

theorem abs_sineBracket_le_linear {U t : ℝ} (h : 0 ≤ U * t) :
    |sineBracket U t| ≤ 1 + U * t := by
  unfold sineBracket
  calc
    _ ≤ |Real.sin (U * t)| + |U * t * Real.cos (U * t)| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (Real.sin (U * t)) (-(U * t * Real.cos (U * t)))
    _ ≤ _ := by
      rw [abs_mul, abs_of_nonneg h]
      exact add_le_add (Real.abs_sin_le_one _) (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (U * t)) h)

theorem abs_sineBracket_le_cubic {U t : ℝ} (h : 0 ≤ U * t) :
    |sineBracket U t| ≤ (U * t) ^ 3 / 3 := by
  let x := U * t
  have hder (y : ℝ) : HasDerivAt (fun y => Real.sin y - y * Real.cos y)
      (y * Real.sin y) y := by
    convert (Real.hasDerivAt_sin y).sub ((hasDerivAt_id y).mul (Real.hasDerivAt_cos y)) using 1
    dsimp
    ring
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := x) (fun y _ => hder y)
    (by apply Continuous.intervalIntegrable; fun_prop : IntervalIntegrable
      (fun y : ℝ => y * Real.sin y) volume 0 x)
  simp only [Real.sin_zero, zero_mul, sub_zero] at hftc
  unfold sineBracket
  rw [← hftc]
  have hmono :
      (∫ y : ℝ in (0 : ℝ)..x, |y * Real.sin y|) ≤ ∫ y : ℝ in (0 : ℝ)..x, y ^ (2 : ℕ) := by
    apply intervalIntegral.integral_mono_on h
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)
    intro y hy
    rw [abs_mul, abs_of_nonneg hy.1, pow_two]
    exact mul_le_mul_of_nonneg_left (by simpa only [abs_of_nonneg hy.1] using
      (Real.abs_sin_le_abs (x := y))) hy.1
  have hle := (intervalIntegral.abs_integral_le_integral_abs h).trans hmono
  rw [integral_pow] at hle
  norm_num at hle ⊢
  exact hle

theorem integrable_deficit_bracket {p U : ℝ} (hp : 0 < p) (hp₂ : p < 2) (hU : 0 < U) :
    IntegrableOn (fun t : ℝ => deficitProfile p t / t ^ 2 * sineBracket U t) (Ioi 0) := by
  have hm : Measurable (fun t : ℝ => deficitProfile p t / t ^ 2 * sineBracket U t) := by
    unfold deficitProfile sinhProfile sineBracket
    fun_prop
  have hnear : IntegrableOn (fun t : ℝ => deficitProfile p t / t ^ 2 * sineBracket U t)
      (Ioo 0 2) := by
    have hbase : IntegrableOn (fun t : ℝ => t ^ (1 - p)) (Ioo 0 2) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num)).mpr (by linarith)
    refine (hbase.const_mul (U ^ 3 / 3)).mono' hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have ht₀ : 0 < t := ht.1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (div_nonneg (deficitProfile_nonneg hp ht₀)
      (sq_nonneg t))]
    calc
      _ ≤ (t ^ (-p) / t ^ 2) * ((U * t) ^ 3 / 3) := mul_le_mul
        (div_le_div_of_nonneg_right (deficitProfile_le_power p t ht₀) (sq_nonneg t))
        (abs_sineBracket_le_cubic (by positivity)) (abs_nonneg _) (by positivity)
      _ = (U ^ 3 / 3) * (t ^ (-p) * t) := by field_simp [ht₀.ne']
      _ = _ := by rw [← Real.rpow_add_one ht₀.ne', show -p + 1 = 1 - p by ring]
  have htail : IntegrableOn (fun t : ℝ => deficitProfile p t / t ^ 2 * sineBracket U t)
      (Ioi 1) := by
    have hbase : IntegrableOn (fun t : ℝ => t ^ (-p - 1)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    refine (hbase.const_mul (1 + U)).mono' hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : 1 < t := ht
    have ht₀ : 0 < t := zero_lt_one.trans ht'
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (div_nonneg (deficitProfile_nonneg hp ht₀)
      (sq_nonneg t))]
    calc
      _ ≤ (t ^ (-p) / t ^ 2) * ((1 + U) * t) := mul_le_mul
        (div_le_div_of_nonneg_right (deficitProfile_le_power p t ht₀) (sq_nonneg t))
        ((abs_sineBracket_le_linear (by positivity)).trans (by linarith)) (abs_nonneg _) (by positivity)
      _ = (1 + U) * (t ^ (-p) / t) := by field_simp [ht₀.ne']
      _ = _ := by rw [Real.rpow_sub_one ht₀.ne']
  have hcover : Ioo (0 : ℝ) 2 ∪ Ioi 1 = Ioi 0 := by
    ext x
    simp only [mem_union, mem_Ioo, mem_Ioi]
    constructor
    · rintro (⟨h, _⟩ | h) <;> linarith
    · intro h
      by_cases hx : x < 2
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr (by linarith)
  rw [← hcover]
  exact hnear.union htail

end ACS12.GammaDeficit

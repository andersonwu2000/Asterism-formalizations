import ACS12.GammaDefectSampling
import ACS12.GammaRadialComparison

/-! Comparison with the line at the original period. The constant part
is recovered by the Abel boundary, which retains the literal self term. -/

namespace ACS12.GammaDeficit

open MeasureTheory Set Filter
open scoped Topology
open ACS12.GammaMeasure

set_option backward.isDefEq.respectTransparency false

private theorem lineDefect_eq_integral {p b : ℝ} (hp : 0 < p) (hb : 2 / 3 ≤ b) (hb₁ : b ≤ 1) :
    IntegrableOn (fun s => lineDensity p s * defectCore b s) (Ioi 0) ∧
      LowScalar.lineValue p b / Real.Gamma p =
        ∫ s : ℝ in Ioi 0, lineDensity p s * defectCore b s := by
  have he (s : ℝ) : LowScalar.lineDensity p b s / Real.Gamma p = lineDensity p s * defectCore b s := by
    unfold LowScalar.lineDensity lineDensity defectCore tailDifference
    ring
  exact ⟨((LowScalar.lineDensity_integrable hp hb hb₁).div_const _).congr (Eventually.of_forall he),
    (integral_div (f := LowScalar.lineDensity p b) _).symm.trans
      (integral_congr_ae (Eventually.of_forall he))⟩

private theorem exp_test_integrable {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0))
    {τ : ℝ} (hτ : 0 ≤ τ) : IntegrableOn (fun s => f s * Real.exp (-s * τ)) (Ioi 0) := by
  have hm : Measurable (fun s : ℝ => Real.exp (-s * τ)) := by fun_prop
  refine hf.norm.mono' (hf.aestronglyMeasurable.mul hm.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_of_le_one_right (norm_nonneg (f s))
    (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mem_Ioi.mp hs).le) hτ))

private theorem tendsto_exp_test {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) :
    Tendsto (fun τ : ℝ => ∫ s : ℝ in Ioi 0, f s * Real.exp (-s * τ))
      (𝓝[>] 0) (𝓝 (∫ s : ℝ in Ioi 0, f s)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun s => ‖f s‖)
  · exact Eventually.of_forall fun τ => hf.aestronglyMeasurable.mul (by fun_prop)
  · filter_upwards [self_mem_nhdsWithin] with τ hτ
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_of_le_one_right (norm_nonneg (f s))
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) hτ.le))
  · exact hf.norm
  · exact Eventually.of_forall fun s => by
      have h : Continuous (fun τ : ℝ => f s * Real.exp (-s * τ)) := by fun_prop
      simpa only [mul_zero, Real.exp_zero, mul_one] using h.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)) (a := 0))

private theorem positive_damped_defect {p L b τ : ℝ} (hp : 0 < p) (hp₁ : p ≤ 1) (hL : 0 < L)
    (hb : 0 < b) (hb₁ : b ≤ 1) (hτ : 0 < τ)
    (hR : IntegrableOn (fun s => signedDensity p L s * defectCore b s) (Ioi 0)) :
    0 ≤ defectConstant b * (τ ^ (-p) - imagePotential p L τ) +
      ∫ s : ℝ in Ioi 0, (signedDensity p L s * defectCore b s) * Real.exp (-s * τ) := by
  let f (s : ℝ) := Real.exp (-s * τ) * defectWeight b s
  let e (s : ℝ) := signedDensity p L s * Real.exp (-s * τ)
  let r (s : ℝ) := (signedDensity p L s * defectCore b s) * Real.exp (-s * τ)
  have he : IntegrableOn e (Ioi 0) := signedDensity_exp_integrable hp hL hτ
  have hr : IntegrableOn r (Ioi 0) := exp_test_integrable hR hτ.le
  have hE (s : ℝ) (hs : 0 < s) :
      signedFirstDensity p L s * f s = defectConstant b * e s + r s := by
    rw [signedFirstDensity_eq hs]
    dsimp only [f, e, r, defectWeight]
    field_simp [hs.ne']
  have hAE : (fun s => signedFirstDensity p L s * f s) =ᵐ[volume.restrict (Ioi 0)]
      (fun s => defectConstant b * e s + r s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact hE s hs
  have hI : IntegrableOn (fun s => signedFirstDensity p L s * f s) (Ioi 0) :=
    ((he.const_mul (defectConstant b)).add hr).congr hAE.symm
  have hExp : ContDiff ℝ 1 (fun s : ℝ => Real.exp (-s * τ)) := by fun_prop
  have hSmooth : ContDiffOn ℝ 1 f (Ioi 0) := hExp.contDiffOn.mul (contDiffOn_defectWeight hb)
  have hnonneg (s : ℝ) (hs : 0 < s) : 0 ≤ f s :=
    mul_nonneg (Real.exp_pos _).le (defectWeight_bounds hb hb₁ hs).1
  have hAnti : AntitoneOn f (Ioi 0) := by
    intro s hs t ht hst
    exact mul_le_mul (Real.exp_le_exp.mpr (by nlinarith))
      (defectWeight_antitone hb hb₁ hs ht hst) (defectWeight_bounds hb hb₁ ht).1 (Real.exp_pos _).le
  have hB (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) : |f s| ≤ 1 - b := by
    rw [abs_of_nonneg (hnonneg s hs.1)]
    exact (mul_le_of_le_one_left (defectWeight_bounds hb hb₁ hs.1).1
      (Real.exp_le_one_iff.mpr (by nlinarith [hs.1]))).trans (defectWeight_bounds hb hb₁ hs.1).2
  have h := signedFirstDensity_test_nonneg hp hp₁ hL hSmooth hnonneg hAnti hB hI
  rw [integral_congr_ae hAE] at h
  have hi : (∫ s : ℝ in Ioi 0, defectConstant b * e s + r s) =
      defectConstant b * (τ ^ (-p) - imagePotential p L τ) + (∫ s : ℝ in Ioi 0, r s) := by
    calc
      _ = (∫ s : ℝ in Ioi 0, defectConstant b * e s) + ∫ s : ℝ in Ioi 0, r s :=
        integral_add (he.const_mul _) hr
      _ = _ := by rw [integral_const_mul, show (∫ s : ℝ in Ioi 0, e s) = _ from
        signedDensity_exp_integral hp hL hτ]
  rw [hi] at h
  exact h

/-- The finite circle defect is bounded by the actual line scalar expression. -/
theorem circleDefect_le_line {p L b : ℝ} (hp : 0 < p) (hp₁ : p ≤ 1) (hL : 0 < L)
    (hb : 2 / 3 ≤ b) (hb₁ : b ≤ 1) :
    circleDefect p L b ≤ LowScalar.lineValue p b / Real.Gamma p := by
  have hb₀ : 0 < b := lt_of_lt_of_le (by norm_num) hb
  have hp₂ : p ≤ 2 := hp₁.trans (by norm_num)
  obtain ⟨hw, hCircle⟩ := circleDefect_eq_integral hp hp₂ hL hb₀
  obtain ⟨hρ, hLine⟩ := lineDefect_eq_integral hp hb hb₁
  let R (s : ℝ) := signedDensity p L s * defectCore b s
  have hE (s : ℝ) : lineDensity p s * defectCore b s - imageDensity p L s * defectCore b s = R s := by
    dsimp only [R, signedDensity]
    ring
  have hR : IntegrableOn R (Ioi 0) := (hρ.sub hw).congr (Eventually.of_forall hE)
  have hlim := ((tendsto_line_sub_imagePotential hp hp₁ hL).const_mul (defectConstant b)).add
    (tendsto_exp_test hR)
  have h : 0 ≤ defectConstant b * imageSelf p L + (∫ s : ℝ in Ioi 0, R s) := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact positive_damped_defect hp hp₁ hL hb₀ hb₁ hτ hR
  have hInt : (∫ s : ℝ in Ioi 0, lineDensity p s * defectCore b s) -
      (∫ s : ℝ in Ioi 0, imageDensity p L s * defectCore b s) = ∫ s : ℝ in Ioi 0, R s :=
    (integral_sub hρ hw).symm.trans (integral_congr_ae (Eventually.of_forall hE))
  rw [hCircle, hLine]
  linarith

end ACS12.GammaDeficit

import ACS12.PressureCut
import ACS12.SpeedMoments

/-! The original full cut stress is integrable at every positive exponent. -/
namespace ACS12.Pressure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaMeasure

private theorem sinh_le_linear_exp (x : ℝ) :
    Real.sinh x ≤ x * Real.exp x := by
  have h := Real.add_one_le_exp (-2 * x)
  have hE : Real.exp (-x) = Real.exp x * Real.exp (-2 * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [Real.sinh_eq,hE]
  have h' := mul_le_mul_of_nonneg_right h (Real.exp_pos x).le
  linarith only [h']

theorem imageDensity_linear_exp_bound {p L ε : ℝ} (hp : 0 < p) (hL : 0 < L) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s > 0, imageDensity p L s ≤ C * s * Real.exp (ε * s) := by
  let d := min (Real.pi / 2) (ε * (2 * Real.pi) / L)
  let r := Real.pi - d
  have hd : 0 < d := lt_min (by positivity) (by positivity)
  have hR : r < Real.pi := sub_lt_self _ hd
  have hR₀ : 0 ≤ r := by
    have h := min_le_left (Real.pi / 2) (ε * (2 * Real.pi) / L)
    unfold r d
    linarith only [h,Real.pi_pos]
  obtain ⟨A,hA,hB⟩ := gammaDensity_exp_bound hp hR hR₀
  let a := (Real.pi / L) ^ (p - 1)
  refine ⟨a * A * (L / 2),by unfold a; positivity,?_⟩
  intro s hs
  let t := L * s / (2 * Real.pi)
  have ht : 0 < t := by unfold t; positivity
  have hT : Real.pi * t = L * s / 2 := by unfold t; field_simp [Real.pi_ne_zero]
  have hE : (Real.pi - r) * t ≤ ε * s := by
    have h := min_le_right (Real.pi / 2) (ε * (2 * Real.pi) / L)
    have h₁ : d * L ≤ ε * (2 * Real.pi) := (le_div_iff₀ hL).mp h
    have h₂ : d * L / (2 * Real.pi) ≤ ε := (div_le_iff₀ (by positivity)).mpr h₁
    have h₃ := mul_le_mul_of_nonneg_right h₂ hs.le
    have hEq : (Real.pi - r) * t = (d * L / (2 * Real.pi)) * s := by unfold r t; ring
    rw [hEq]
    exact h₃
  rw [imageDensity_eq_spectral p hL]
  change a * gammaDensity p t * Real.sinh (L * s / 2) ≤ _
  have hW := hB t
  rw [abs_of_pos ht] at hW
  have hS := sinh_le_linear_exp (L * s / 2)
  have ha : 0 ≤ a := by unfold a; positivity
  have h₁ := mul_le_mul hW hS (Real.sinh_nonneg_iff.mpr (by positivity)) (by positivity : 0 ≤ A * Real.exp (-r * t))
  calc
    _ ≤ a * ((A * Real.exp (-r * t)) * ((L * s / 2) * Real.exp (L * s / 2))) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left h₁ ha
    _ = (a * A * (L / 2)) * s * Real.exp ((Real.pi - r) * t) := by
      rw [show (Real.pi - r) * t = -r * t + L * s / 2 by linarith only [hT],Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hE) (by positivity)

theorem stressKernel_integrable_all {p L D t : ℝ} (hp : 0 < p) (hL : 0 < L) (hD : 0 < D) (ht : 0 < t) :
    IntegrableOn (fun s => imageDensity p L s * s * Real.exp (-s * t) / (periodicDen D s) ^ 2) (Ioi 0) := by
  obtain ⟨C,hC,hB⟩ := imageDensity_linear_exp_bound hp hL (show 0 < t / 2 by positivity)
  let f (s : ℝ) := imageDensity p L s * s * Real.exp (-s * t) / (periodicDen D s) ^ 2
  let g (s : ℝ) := C * ((s + D⁻¹) ^ 2 * Real.exp (-s * (t / 2)))
  have ht₂ : 0 < t / 2 := by positivity
  have hI : IntegrableOn g (Ioi 0) := by
    have h₀ : IntegrableOn (fun s : ℝ => Real.exp (-s * (t / 2))) (Ioi 0) := by
      simpa only [pow_zero,one_mul] using integrable_power_exponential 0 (t / 2) ht₂
    have h₁ : IntegrableOn (fun s : ℝ => s * Real.exp (-s * (t / 2))) (Ioi 0) := by
      simpa only [pow_one] using integrable_power_exponential 1 (t / 2) ht₂
    have h₂ := integrable_power_exponential 2 (t / 2) ht₂
    apply (((h₂.add (h₁.const_mul (2 * D⁻¹))).add (h₀.const_mul (D⁻¹ ^ 2))).const_mul C).congr
    exact Eventually.of_forall fun s => by dsimp only [g,Pi.add_apply]; ring
  have hf : Measurable f := by
    unfold f
    refine (((continuous_imageDensity hp hL).measurable.mul measurable_id).mul (by fun_prop)).div ?_
    unfold periodicDen
    fun_prop
  apply hI.mono' hf.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs₀ : 0 < s := hs
  have hDen := periodicDen_pos hD hs₀
  have hHead := (BoseShape.expTail_bounds (mul_pos hs₀ hD)).2
  have hEq : s * D / periodicDen D s = s * D + expTailFactor (s * D) := by
    rw [← GammaMeasure.expHeadFactor_eq_add_expTail (mul_pos hs₀ hD)]
    simp only [expHeadFactor,periodicDen,neg_mul]
  have hSd : s / periodicDen D s ≤ s + D⁻¹ := by
    apply (mul_le_mul_iff_right₀ hD).mp
    rw [← mul_div_assoc,mul_comm D s,hEq,mul_add,mul_inv_cancel₀ hD.ne']
    linarith only [hHead]
  have hSq := pow_le_pow_left₀ (div_nonneg hs₀.le hDen.le) hSd 2
  have hW := imageDensity_pos hp hL hs₀
  change ‖f s‖ ≤ g s
  rw [Real.norm_of_nonneg (show 0 ≤ f s by dsimp only [f]; positivity)]
  calc
    f s ≤ ((C * s * Real.exp (t / 2 * s)) * (s * Real.exp (-s * t))) / periodicDen D s ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      convert mul_le_mul_of_nonneg_right (hB s hs₀) (show 0 ≤ s * Real.exp (-s * t) by positivity) using 1
      ring
    _ = C * ((s / periodicDen D s) ^ 2 * Real.exp (-s * (t / 2))) := by
      rw [← show t / 2 * s + -s * t = -s * (t / 2) by ring,Real.exp_add,div_pow]
      ring
    _ ≤ g s := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hSq (Real.exp_pos _).le) hC

end ACS12.Pressure

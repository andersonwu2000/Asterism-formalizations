import ACS12.LawPeano
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The small-spacing limit of the original fourth A stream, including p = 1. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open scoped Topology
open GammaDeficit (lineDensity)

private theorem polyA_tendsto_one : Tendsto polyA atTop (𝓝 1) := by
  have h0 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0
  have h1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have h := (h0.add h1).const_sub (1 : ℝ)
  simp only [zero_add, sub_zero, pow_zero, pow_one, one_mul] at h
  apply h.congr
  intro x
  unfold polyA
  ring

private theorem lawDensity_eventual_floor {p L θ : ℝ} (hp : 1 ≤ p) (hp₂ : p < 2)
    (hL : 0 < L) :
    ∀ᶠ s : ℝ in atTop, (Real.Gamma p)⁻¹ / 2 ≤ lawDensity p L θ s := by
  have h := (lawDensity_div_lineDensity_tendsto_one (θ := θ) hp hp₂ hL).eventually
    (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with s hs hs₁
  have hs₀ : 0 < s := zero_lt_one.trans_le hs₁
  have hp₀ : 0 < p := zero_lt_one.trans_le hp
  have hρ : (Real.Gamma p)⁻¹ ≤ lineDensity p s := by
    unfold lineDensity
    rw [div_eq_mul_inv]
    exact le_mul_of_one_le_left (inv_pos.mpr (Real.Gamma_pos_of_pos hp₀)).le
      (Real.one_le_rpow hs₁ (sub_nonneg.mpr hp))
  have hs' := (lt_div_iff₀ (lineDensity_pos hp₀ hs₀)).mp (mem_Ioi.mp hs)
  linarith only [hρ, hs']

private theorem scaledExpTail_floor {s r : ℝ} (hs : 0 < s) (hr : 0 < r) (hsr : s * r ≤ 1) :
    expTailFactor 1 * s⁻¹ ≤ scaledExpTail s r := by
  rw [scaledExpTail_eq_factor hs, ← div_eq_mul_inv]
  apply div_le_div_of_nonneg_right _ hs.le
  exact strictAntiOn_expTailFactor.antitoneOn (mul_pos hs hr) (mem_Ioi.mpr zero_lt_one) hsr

theorem lawPeanoTail_unbounded_at_small_step {p L θ h v : ℝ} (hp : 1 ≤ p) (hp₂ : p < 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hh : 0 < h) (hv : 0 < v) (M : ℝ) :
    ∃ r ∈ Ioo 0 v, M < samplingTail (lawPeanoKernel p L θ h .a) 0 r := by
  let w := lawDensity p L θ
  let A := lawPeanoDensity p L θ h .a
  let K := (Real.Gamma p)⁻¹ / 2 * (1 / 2) * expTailFactor 1
  have hK : 0 < K := by
    dsimp only [K]
    exact mul_pos (mul_pos (div_pos (inv_pos.mpr (Real.Gamma_pos_of_pos (zero_lt_one.trans_le hp)))
      (by norm_num)) (by norm_num)) (div_pos zero_lt_one (expTail_den_pos zero_lt_one))
  have hLim : Tendsto (fun s : ℝ => polyA (h * s)) atTop (𝓝 1) :=
    polyA_tendsto_one.comp ((tendsto_const_mul_atTop_of_pos hh).mpr tendsto_id)
  have hA := hLim.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hW := lawDensity_eventual_floor (θ := θ) hp hp₂ hL
  obtain ⟨S, hS⟩ := eventually_atTop.1
    (hA.and (hW.and ((eventually_gt_atTop v⁻¹).and (eventually_ge_atTop (1 : ℝ)))))
  have h₁ := hS S le_rfl
  have hS₀ : 0 < S := zero_lt_one.trans_le h₁.2.2.2
  let E := (max M 0 + 1) / K
  have hE : 0 < E := by
    dsimp only [E]
    exact div_pos (add_pos_of_nonneg_of_pos (le_max_right _ _) zero_lt_one) hK
  let R := S * Real.exp E
  have hSR : S < R := lt_mul_of_one_lt_right hS₀ (Real.one_lt_exp_iff.mpr hE)
  have hR : 0 < R := hS₀.trans hSR
  let r := R⁻¹
  have hr : 0 < r := inv_pos.mpr hR
  have hrv : r < v := by
    have hTop : v⁻¹ < R := h₁.2.2.1.trans hSR
    exact (inv_lt_comm₀ hR hv).mpr hTop
  refine ⟨r, ⟨hr, hrv⟩, ?_⟩
  obtain ⟨hInt, hEq⟩ := lawPeanoTail_sampling hp hp₂.le hL hθ hh (t := 0) le_rfl hr .a
  simp only [mul_zero, Real.exp_zero, mul_one] at hInt hEq
  rw [hEq]
  let f (s : ℝ) := A s * scaledExpTail s r
  have hF : IntegrableOn f (Ioi 0) := hInt
  have hSub : Ioc S R ⊆ Ioi (0 : ℝ) := fun s hs => hS₀.trans hs.1
  have hFull : (∫ s : ℝ in Ioc S R, f s) ≤ ∫ s : ℝ in Ioi 0, f s := by
    apply setIntegral_mono_set hF _ (Eventually.of_forall hSub)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_nonneg (lawPeanoDensity_pos (zero_lt_one.trans_le hp) hL hθ hh hs .a).le
      (div_pos hr (expTail_den_pos (mul_pos hs hr))).le
  have hCont : ContinuousOn (fun s : ℝ => K * s⁻¹) (uIcc S R) := by
    apply ContinuousOn.const_mul _ K
    apply continuous_id.continuousOn.inv₀
    intro s hs
    rw [uIcc_of_le hSR.le] at hs
    exact (hS₀.trans_le hs.1).ne'
  have hIntInv : IntegrableOn (fun s : ℝ => K * s⁻¹) (Ioc S R) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hSR.le).mp hCont.intervalIntegrable
  have hLower : (∫ s : ℝ in Ioc S R, K * s⁻¹) ≤ ∫ s : ℝ in Ioc S R, f s := by
    apply setIntegral_mono_on hIntInv (hF.mono_set hSub) measurableSet_Ioc
    intro s hs
    have hs₀ := hS₀.trans hs.1
    have hData := hS s hs.1.le
    have hsr : s * r ≤ 1 := by
      dsimp only [r]
      simpa only [r, mul_inv_cancel₀ hR.ne'] using mul_le_mul_of_nonneg_right hs.2 hr.le
    have hβ := scaledExpTail_floor hs₀ hr hsr
    have hD : (Real.Gamma p)⁻¹ / 2 * (1 / 2) ≤ A s :=
      mul_le_mul hData.2.1 (mem_Ioi.mp hData.1).le (by norm_num)
        (lawDensity_pos (zero_lt_one.trans_le hp) hL hθ hs₀).le
    have hPos : 0 ≤ expTailFactor 1 * s⁻¹ :=
      mul_nonneg (BoseShape.expTail_bounds zero_lt_one).1 (inv_pos.mpr hs₀).le
    calc
      _ = ((Real.Gamma p)⁻¹ / 2 * (1 / 2)) * (expTailFactor 1 * s⁻¹) := by dsimp only [K]; ring
      _ ≤ f s := mul_le_mul hD hβ hPos (lawPeanoDensity_pos (zero_lt_one.trans_le hp) hL hθ hh hs₀ .a).le
  have hEval : (∫ s : ℝ in Ioc S R, K * s⁻¹) = max M 0 + 1 := by
    rw [← intervalIntegral.integral_of_le hSR.le, intervalIntegral.integral_const_mul,
      integral_inv_of_pos hS₀ hR]
    have hR' : R / S = Real.exp E := by dsimp only [R]; field_simp [hS₀.ne']
    rw [hR', Real.log_exp]
    dsimp only [E]
    field_simp [hK.ne']
  exact lt_of_lt_of_le (by linarith [le_max_left M (0 : ℝ)]) (hEval ▸ hLower.trans hFull)

end ACS12.GammaMeasure


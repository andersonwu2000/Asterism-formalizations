import ACS12.FiniteUnimodalCapacity
import ACS12.HighCurrentHumpShape
import ACS12.HighCurrentIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Capacity and change of variables for the same complete physical current hump. -/
namespace ACS12.HighCurrent

open Set Finset MeasureTheory

theorem currentHump_integral_truncate {τ x A : ℝ} (hτ : 0 < τ) (hx : 0 < x) (hA : 0 ≤ A) :
    (∫ z in (0 : ℝ)..A, currentHump τ z / (x + z ^ 2)) ≤
      ∫ z in (0 : ℝ)..τ, τ * z ^ 3 * (τ - z) / (x + z ^ 2) := by
  let g (z : ℝ) := currentHump τ z / (x + z ^ 2)
  have hCont : Continuous g := (currentHump_continuous τ).div
    (by fun_prop) (fun z => (show 0 < x + z ^ 2 by positivity).ne')
  have hEnd : (∫ z in (0 : ℝ)..τ, g z) =
      ∫ z in (0 : ℝ)..τ, τ * z ^ 3 * (τ - z) / (x + z ^ 2) := by
    apply intervalIntegral.integral_congr
    intro z hz
    have hzτ : z ≤ τ := (mem_uIcc.mp hz).elim (fun h => h.2) (fun h => by linarith)
    simp only [g,currentHump,if_pos hzτ]
  rw [← hEnd]
  by_cases hAτ : A ≤ τ
  · have hAdd := intervalIntegral.integral_add_adjacent_intervals
      (hCont.intervalIntegrable (μ := volume) 0 A) (hCont.intervalIntegrable (μ := volume) A τ)
    have hNon : 0 ≤ ∫ z in A..τ, g z :=
      intervalIntegral.integral_nonneg hAτ (fun z hz => div_nonneg
        (currentHump_nonneg hτ.le (hA.trans hz.1)) (by positivity))
    linarith only [hAdd,hNon]
  · have hτA := (le_of_not_ge hAτ)
    have hZero : (∫ z in τ..A, g z) = 0 := by
      have hFun : (∫ z in τ..A, g z) = ∫ _ in τ..A, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro z hz
        have hzτ : τ ≤ z := (mem_uIcc.mp hz).elim (fun h => h.1) (fun h => by linarith)
        by_cases hzEq : z = τ
        · simp only [g,currentHump,hzEq,le_refl,if_true,sub_self,mul_zero,zero_div]
        · have hNot : ¬z ≤ τ := fun h => hzEq (le_antisymm h hzτ)
          simp only [g,currentHump,if_neg hNot,zero_div]
      simpa only [intervalIntegral.integral_zero] using hFun
    have hAdd := intervalIntegral.integral_add_adjacent_intervals
      (hCont.intervalIntegrable (μ := volume) 0 τ) (hCont.intervalIntegrable (μ := volume) τ A)
    linarith only [hAdd,hZero]

theorem currentHump_arc_integral {τ x a b : ℝ} {z : ℝ → ℝ}
    (hτ : 0 < τ) (hx : 0 < x) (hab : a ≤ b)
    (hZ : ContinuousOn z (Icc a b))
    (hD : ∀ s ∈ Icc a b, HasDerivAt z (-(x + z s ^ 2)) s)
    (hZa : 0 ≤ z a) (hZb : z b = 0) :
    (∫ s in a..b, currentHump τ (z s)) ≤
      ∫ v in (0 : ℝ)..τ, τ * v ^ 3 * (τ - v) / (x + v ^ 2) := by
  let g (v : ℝ) := currentHump τ v / (x + v ^ 2)
  have hG : Continuous g := (currentHump_continuous τ).div
    (by fun_prop) (fun v => (show 0 < x + v ^ 2 by positivity).ne')
  have hSub := intervalIntegral.integral_comp_mul_deriv
    (fun s hs => hD s (by simpa only [uIcc_of_le hab] using hs))
    (show ContinuousOn (fun s => -(x + z s ^ 2)) (uIcc a b) by
      rw [uIcc_of_le hab]
      fun_prop) hG
  have hLeft : (∫ s in a..b, (g ∘ z) s * (-(x + z s ^ 2))) =
      -(∫ s in a..b, currentHump τ (z s)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro s _
    simp only [Function.comp_apply,g]
    field_simp [show x + z s ^ 2 ≠ 0 by positivity]
  rw [hLeft,hZb,intervalIntegral.integral_symm 0 (z a)] at hSub
  have hEq : (∫ s in a..b, currentHump τ (z s)) =
      ∫ v in (0 : ℝ)..z a, currentHump τ v / (x + v ^ 2) := by
    exact neg_injective hSub
  rw [hEq]
  exact currentHump_integral_truncate hτ hx hZa

theorem finite_currentHump_capacity {ι : Type*} [DecidableEq ι]
    (t w : ι → ℝ) (S : Finset ι) {τ x a b : ℝ} {z : ℝ → ℝ}
    (hτ : 0 < τ) (hx : 0 < x) (hab : a ≤ b)
    (hZ : ContinuousOn z (Icc a b)) (hAnti : AntitoneOn z (Icc a b))
    (hZpos : ∀ s ∈ Icc a b, 0 ≤ z s)
    (hD : ∀ s ∈ Icc a b, HasDerivAt z (-(x + z s ^ 2)) s)
    (hZb : z b = 0) (hw : ∀ i ∈ S, 0 ≤ w i ∧ w i ≤ 1)
    (hDom : ∀ i ∈ S, t i ∈ Icc a b)
    (hSep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → w i ≤ |t i - t j|) :
    (∑ i ∈ S, w i * currentHump τ (z (t i))) ≤
      27 * τ ^ 5 / 256 +
        ∫ v in (0 : ℝ)..τ, τ * v ^ 3 * (τ - v) / (x + v ^ 2) := by
  have hCap := finite_unimodal_capacity t w S hab (by positivity : 0 ≤ 27 * τ ^ 5 / 256)
    ((currentHump_continuous τ).comp_continuousOn hZ)
    (fun s hs => currentHump_nonneg hτ.le (hZpos s hs))
    (fun s hs => currentHump_max hτ.le (hZpos s hs))
    (fun {s _v r} hs hr hsv hvr => by
      have hv : _v ∈ Icc a b := ⟨hs.1.trans hsv,hvr.trans hr.2⟩
      rw [min_comm]
      exact currentHump_min hτ.le (hZpos r hr) (hAnti hv hr hvr) (hAnti hs hv hsv))
    hw hDom hSep
  have hIntegral := currentHump_arc_integral hτ hx hab hZ hD (hZpos a ⟨le_rfl,hab⟩) hZb
  simp only [Function.comp_apply] at hCap
  linarith only [hCap,hIntegral]

end ACS12.HighCurrent

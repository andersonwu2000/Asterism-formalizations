import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Moment interpolation by one normalized weighted arithmetic-geometric mean. -/
namespace ACS12
open MeasureTheory Filter
set_option maxHeartbeats 1400000

 theorem positive_moment_interpolation {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω→ℝ} {β : ℝ}
    (hβ : 0≤β) (hβ₁ : β≤1) (hX : ∀ᵐ ω ∂μ,0<X ω)
    (hXI : Integrable X μ) (hβI : Integrable (fun ω=>X ω^β) μ)
    (h₂I : Integrable (fun ω=>X ω^2) μ)
    (hA : 0<∫ ω,X ω^β ∂μ) (hB : 0<∫ ω,X ω^2 ∂μ)
    (hMean : 0<∫ ω,X ω ∂μ) :
    (∫ ω,X ω ∂μ)^(2-β)≤(∫ ω,X ω^β ∂μ)*(∫ ω,X ω^2 ∂μ)^(1-β) := by
  let A:=∫ ω,X ω^β ∂μ
  let B:=∫ ω,X ω^2 ∂μ
  let a:=1/(2-β)
  let b:=(1-β)/(2-β)
  have hD : 0<2-β := by linarith only [hβ₁]
  have ha : 0≤a := (div_pos zero_lt_one hD).le
  have hb : 0≤b := div_nonneg (sub_nonneg.mpr hβ₁) hD.le
  have hab : a+b=1 := by
    unfold a b
    field_simp [hD.ne']
    <;>ring
  let F (ω : Ω):=X ω/(A^a*B^b)
  let G (ω : Ω):=a*(X ω^β/A)+b*(X ω^2/B)
  have hNorm : 0<A^a*B^b:=mul_pos (Real.rpow_pos_of_pos hA _) (Real.rpow_pos_of_pos hB _)
  have hFI : Integrable F μ := hXI.div_const _
  have hGI : Integrable G μ := (hβI.div_const A |>.const_mul a).add (h₂I.div_const B |>.const_mul b)
  have hPoint : ∀ᵐ ω ∂μ,F ω≤G ω := by
    filter_upwards [hX] with ω hω
    have hAM:=Real.geom_mean_le_arith_mean2_weighted ha hb
      (div_nonneg (Real.rpow_nonneg hω.le β) hA.le)
      (div_nonneg (sq_nonneg (X ω)) hB.le) hab
    have hE : (X ω^β/A)^a*(X ω^2/B)^b=F ω := by
      rw [Real.div_rpow (Real.rpow_nonneg hω.le _) hA.le,
        Real.div_rpow (sq_nonneg (X ω)) hB.le]
      rw [←Real.rpow_mul hω.le,←Real.rpow_two (X ω),←Real.rpow_mul hω.le,
        div_mul_div_comm,←Real.rpow_add hω,
        show β*a+2*b=1 by
          unfold a b
          field_simp [hD.ne']
          <;>ring,Real.rpow_one]
    exact hE ▸ hAM
  have hCmp:=integral_mono_ae hFI hGI hPoint
  have hInt : (∫ ω,G ω ∂μ)=1 := by
    rw [show G=(fun ω=>a*(X ω^β/A)+b*(X ω^2/B)) by rfl,
      integral_add (hβI.div_const A |>.const_mul a) (h₂I.div_const B |>.const_mul b),
      integral_const_mul,integral_const_mul,integral_div,integral_div]
    change a*(A/A)+b*(B/B)=1
    rw [div_self hA.ne',div_self hB.ne',mul_one,mul_one,hab]
  rw [hInt] at hCmp
  change (∫ ω,X ω/(A^a*B^b) ∂μ)≤1 at hCmp
  rw [integral_div] at hCmp
  have hBound : (∫ ω,X ω ∂μ)≤A^a*B^b := (div_le_one hNorm).mp hCmp
  have hPow:=Real.rpow_le_rpow hMean.le hBound hD.le
  rw [Real.mul_rpow (Real.rpow_nonneg hA.le _) (Real.rpow_nonneg hB.le _),
    ←Real.rpow_mul hA.le,←Real.rpow_mul hB.le,
    show a*(2-β)=1 by unfold a;field_simp [hD.ne'],
    show b*(2-β)=1-β by unfold b;field_simp [hD.ne'],Real.rpow_one] at hPow
  exact hPow

end ACS12

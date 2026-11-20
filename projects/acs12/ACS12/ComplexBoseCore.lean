import ACS12.NativeBoseRow
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import ACS12.GammaArgumentCore

/-! The original complete Bose row with its literal complex Gamma product. -/
namespace ACS12.NativeCells
open MeasureTheory Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

noncomputable def complexGammaPair (α : ℂ) (ξ : ℝ) : ℂ :=
  Complex.Gamma (α/2+(ξ:ℂ)*Complex.I)*Complex.Gamma (α/2-(ξ:ℂ)*Complex.I)

noncomputable def boseWeight (N ξ : ℝ) : ℝ :=
  Real.sinh (Real.pi*ξ)/(Real.exp (2*Real.pi*ξ/N)-1)

noncomputable def complexBoseKernel (N : ℝ) (α : ℂ) (ξ : ℝ) : ℂ :=
  complexGammaPair α ξ * (boseWeight N ξ:ℂ)

noncomputable def complexBoseCoefficient (α : ℂ) : ℂ :=
  (2:ℂ)^(α+1)/((Real.pi:ℂ)*Complex.Gamma α)

noncomputable def complexBoseRow (N : ℝ) (α : ℂ) : ℂ :=
  complexBoseCoefficient α * ∫ ξ : ℝ in Ioi 0, complexBoseKernel N α ξ

theorem complexGammaPair_real (p ξ : ℝ) :
    complexGammaPair (p:ℂ) ξ = (‖Complex.Gamma (GammaMeasure.gammaArgument (p/2) ξ)‖^2:ℝ) := by
  have hc : (p:ℂ)/2-(ξ:ℂ)*Complex.I =
      star ((p:ℂ)/2+(ξ:ℂ)*Complex.I) := by simp [Complex.conj_I,sub_eq_add_neg]
  unfold complexGammaPair
  rw [hc,Complex.star_def,Complex.Gamma_conj,Complex.mul_conj,Complex.normSq_eq_norm_sq]
  simp [GammaMeasure.gammaArgument,Complex.ofReal_div]

theorem complexBoseRow_real (p N : ℝ) :
    complexBoseRow N (p:ℂ) = (boseRow p N:ℂ) := by
  have hCoeff : complexBoseCoefficient (p:ℂ) =
      (((2:ℝ)^(p+1)/(Real.pi*Real.Gamma p):ℝ):ℂ) := by
    unfold complexBoseCoefficient
    rw [show (p:ℂ)+1 = ((p+1:ℝ):ℂ) by push_cast; rfl,
      show (2:ℂ) = ((2:ℝ):ℂ) by norm_num,←Complex.ofReal_cpow (by norm_num : (0:ℝ)≤2),
      Complex.Gamma_ofReal]
    push_cast
    rfl
  have hKernel : complexBoseKernel N (p:ℂ) =
      (fun ξ => ((‖Complex.Gamma (GammaMeasure.gammaArgument (p/2) ξ)‖^2*boseWeight N ξ:ℝ):ℂ)) := by
    funext ξ
    rw [complexBoseKernel,complexGammaPair_real]
    push_cast
    rfl
  unfold complexBoseRow
  rw [hCoeff,hKernel,integral_complex_ofReal,←Complex.ofReal_mul]
  congr 1
  rw [←integral_const_mul]
  unfold boseRow
  apply setIntegral_congr_fun measurableSet_Ioi
  intro ξ _
  unfold GammaMeasure.gammaDensity GammaMeasure.gammaArgument boseWeight
  have hPow : (2:ℝ)^(p+1) = 4*(2:ℝ)^(p-1) := by
    rw [show p+1 = 2+(p-1) by ring,Real.rpow_add (by norm_num : (0:ℝ)<2)]
    norm_num
  rw [hPow]
  ring

theorem complexGammaPair_differentiableAt {α : ℂ} (hα : 0 < α.re) (ξ : ℝ) :
    DifferentiableAt ℂ (fun a => complexGammaPair a ξ) α := by
  have hArgPlus : DifferentiableAt ℂ (fun a : ℂ => a/2+(ξ:ℂ)*Complex.I) α := by fun_prop
  have hArgMinus : DifferentiableAt ℂ (fun a : ℂ => a/2-(ξ:ℂ)*Complex.I) α := by fun_prop
  have hAvoid (z : ℂ) (hz : 0 < z.re) (n : ℕ) : z ≠ -(n:ℂ) := by
    intro he
    have hh := congrArg Complex.re he
    simp only [Complex.neg_re,Complex.natCast_re] at hh
    linarith only [hz,hh,Nat.cast_nonneg (α:=ℝ) n]
  have hp : 0 < (α/2+(ξ:ℂ)*Complex.I).re := by simp; linarith only [hα]
  have hm : 0 < (α/2-(ξ:ℂ)*Complex.I).re := by simp; linarith only [hα]
  exact ((Complex.differentiableAt_Gamma _ (hAvoid _ hp)).comp α hArgPlus).mul
    ((Complex.differentiableAt_Gamma _ (hAvoid _ hm)).comp α hArgMinus)

theorem complexBoseKernel_differentiableAt {α : ℂ} (hα : 0 < α.re) (N ξ : ℝ) :
    DifferentiableAt ℂ (fun a => complexBoseKernel N a ξ) α :=
  (complexGammaPair_differentiableAt hα ξ).mul_const _

theorem complexBoseCoefficient_differentiableAt {α : ℂ} (hα : 0 < α.re) :
    DifferentiableAt ℂ complexBoseCoefficient α := by
  have hn : DifferentiableAt ℂ (fun a : ℂ => (2:ℂ)^(a+1)) α := by
    have he : (fun a : ℂ => (2:ℂ)^(a+1)) =
        (fun a => Complex.exp (Complex.log 2*(a+1))) := by
      funext a
      rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
    rw [he]
    fun_prop
  have hAvoid (n : ℕ) : α ≠ -(n:ℂ) := by
    intro he
    have hh := congrArg Complex.re he
    simp only [Complex.neg_re,Complex.natCast_re] at hh
    linarith only [hα,hh,Nat.cast_nonneg (α:=ℝ) n]
  exact hn.div ((Complex.differentiableAt_Gamma _ hAvoid).const_mul _)
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
      (Complex.Gamma_ne_zero_of_re_pos hα))

end ACS12.NativeCells

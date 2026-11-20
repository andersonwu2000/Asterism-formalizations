import ACS12.ComplexBoseCore
import ACS12.GammaShiftedPairTail
import ACS12.GammaPositiveNorm

/-! One compact real shape interval controls the original complex Gamma pair, including all imaginary shifts. -/
namespace ACS12.NativeCells
open Set
set_option backward.isDefEq.respectTransparency false

theorem complexGammaPair_eq_arguments (α : ℂ) (ξ : ℝ) :
    complexGammaPair α ξ =
      Complex.Gamma (GammaMeasure.gammaArgument (α.re/2) (α.im/2+ξ)) *
        Complex.Gamma (GammaMeasure.gammaArgument (α.re/2) (α.im/2-ξ)) := by
  unfold complexGammaPair
  congr 2 <;> apply Complex.ext <;> simp [GammaMeasure.gammaArgument] <;> ring

theorem complexGammaPair_norm_bound {α : ℂ} {a b B : ℝ} (ha : 0 < a)
    (hα : α.re/2 ∈ Icc a b) (hB : ∀ s ∈ Icc a b, Real.Gamma s ≤ B) (ξ : ℝ) :
    ‖complexGammaPair α ξ‖ ≤ B^2 := by
  have hPos : 0 < α.re/2 := ha.trans_le hα.1
  have hp : 0 < (α/2+(ξ:ℂ)*Complex.I).re := by simpa using hPos
  have hm : 0 < (α/2-(ξ:ℂ)*Complex.I).re := by simpa using hPos
  have hPlus := GammaMeasure.norm_Gamma_le_realGamma hp
  have hMinus := GammaMeasure.norm_Gamma_le_realGamma hm
  simp only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.div_ofNat_re,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,
    add_zero] at hPlus hMinus
  rw [complexGammaPair,norm_mul]
  have hB₀ : 0 ≤ B := (Real.Gamma_pos_of_pos hPos).le.trans (hB _ hα)
  simpa only [pow_two] using
    mul_le_mul (hPlus.trans (hB _ hα)) (hMinus.trans (hB _ hα)) (norm_nonneg _) hB₀

theorem complexGammaPair_rect_tail {a b T : ℝ} (ha : 0 < a) (hT : 0 ≤ T) :
    ∃ C > 0, ∃ k : ℕ, ∀ α : ℂ, α.re/2 ∈ Icc a b → |α.im/2| ≤ T →
      ∀ ξ : ℝ, T+1 ≤ ξ →
      ‖complexGammaPair α ξ‖ ≤ C*(1+ξ)^k*Real.exp (-Real.pi*ξ) := by
  obtain ⟨C,hC,k,h⟩ := GammaMeasure.gamma_pair_compact_tail (b:=b) ha hT
  refine ⟨C,hC,k,?_⟩
  intro α hα hIm ξ hξ
  rw [complexGammaPair_eq_arguments]
  exact h _ hα _ hIm ξ hξ

end ACS12.NativeCells

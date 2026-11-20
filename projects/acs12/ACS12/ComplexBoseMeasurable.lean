import ACS12.ComplexBoseCore

/-! The literal complex Bose integrand is measurable for every complex shape. -/
namespace ACS12.NativeCells
open Set MeasureTheory

theorem measurable_Gamma_vertical (z : ℂ) :
    Measurable (fun ξ : ℝ => Complex.Gamma (z+(ξ:ℂ)*Complex.I)) := by
  apply measurable_of_continuousOn_compl_singleton (-z.im)
  intro ξ hξ
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.comp (Complex.continuousAt_Gamma _ ?_) (by fun_prop)
  intro n he
  have hIm := congrArg Complex.im he
  simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.I_im,
    Complex.ofReal_im,Complex.I_re,mul_one,mul_zero,zero_add,add_zero,
    Complex.neg_im,Complex.natCast_im,neg_zero] at hIm
  have hEq : ξ = -z.im := by linarith only [hIm]
  exact hξ (Set.mem_singleton_iff.mpr hEq)

theorem measurable_complexGammaPair (α : ℂ) : Measurable (complexGammaPair α) := by
  have hP := measurable_Gamma_vertical (α/2)
  have hM := hP.comp measurable_neg
  have hEq : (fun ξ : ℝ => Complex.Gamma (α/2+((-ξ:ℝ):ℂ)*Complex.I)) =
      (fun ξ : ℝ => Complex.Gamma (α/2-(ξ:ℂ)*Complex.I)) := by
    funext ξ
    congr 1
    push_cast
    ring
  change Measurable (fun ξ : ℝ => Complex.Gamma (α/2+((-ξ:ℝ):ℂ)*Complex.I)) at hM
  rw [hEq] at hM
  exact hP.mul hM

theorem measurable_boseWeight (N : ℝ) : Measurable (boseWeight N) := by
  unfold boseWeight
  fun_prop

theorem measurable_complexBoseKernel (N : ℝ) (α : ℂ) : Measurable (complexBoseKernel N α) :=
  (measurable_complexGammaPair α).mul (Complex.measurable_ofReal.comp (measurable_boseWeight N))

end ACS12.NativeCells

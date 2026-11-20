import ACS12.ComplexGammaPairBounds
import ACS12.BoseWeightBounds

/-! Direct full Bose-kernel bounds at the origin and over the entire tail. -/
namespace ACS12.NativeCells
open Set
set_option backward.isDefEq.respectTransparency false

theorem boseWeight_nonneg {N ξ : ℝ} (hN : 0 < N) (hξ : 0 < ξ) : 0 ≤ boseWeight N ξ := by
  unfold boseWeight
  exact div_nonneg (Real.sinh_nonneg_iff.mpr (by positivity))
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))).le

theorem complexBoseKernel_origin_bound {α : ℂ} {N ξ L B : ℝ} (hN : 0 < N)
    (hξ : 0 < ξ) (hξL : ξ ≤ L) (hB : 0 ≤ B) (hGamma : ‖complexGammaPair α ξ‖ ≤ B) :
    ‖complexBoseKernel N α ξ‖ ≤
      B*(Real.pi*Real.exp (Real.pi*L)/(2*Real.pi/N)) := by
  have hd : 0 < 2*Real.pi/N := by positivity
  have hWeight := bose_weight_origin_bound hd hξ hξL
  have hArg : 2*Real.pi*ξ/N = (2*Real.pi/N)*ξ := by ring
  rw [←hArg] at hWeight
  change boseWeight N ξ ≤ _ at hWeight
  rw [complexBoseKernel,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (boseWeight_nonneg hN hξ)]
  exact mul_le_mul hGamma hWeight (boseWeight_nonneg hN hξ) hB

theorem complexBoseKernel_tail_bound {α : ℂ} {N ξ L C : ℝ} (k : ℕ) (hN : 0 < N)
    (hL : 0 < L) (hξ : L ≤ ξ) (hC : 0 ≤ C)
    (hGamma : ‖complexGammaPair α ξ‖ ≤ C*(1+ξ)^k*Real.exp (-Real.pi*ξ)) :
    ‖complexBoseKernel N α ξ‖ ≤
      (C*(1-Real.exp (-(2*Real.pi/N)*L))⁻¹)*(1+ξ)^k*Real.exp (-(2*Real.pi/N)*ξ) := by
  have hξ₀ : 0 < ξ := hL.trans_le hξ
  have hd : 0 < 2*Real.pi/N := by positivity
  have hk : 0 < 1-Real.exp (-(2*Real.pi/N)*L) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith only [mul_pos hd hL]))
  have hWeight := bose_weight_tail_bound hd hL hξ
  have hArg : 2*Real.pi*ξ/N = (2*Real.pi/N)*ξ := by ring
  rw [←hArg] at hWeight
  change boseWeight N ξ ≤ _ at hWeight
  rw [complexBoseKernel,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (boseWeight_nonneg hN hξ₀)]
  calc
    _ ≤ (C*(1+ξ)^k*Real.exp (-Real.pi*ξ))*
        ((1-Real.exp (-(2*Real.pi/N)*L))⁻¹*Real.exp (Real.pi*ξ)*Real.exp (-(2*Real.pi/N)*ξ)) :=
      mul_le_mul hGamma hWeight (boseWeight_nonneg hN hξ₀) (by positivity)
    _ = _ := by
      have he : Real.exp (-Real.pi*ξ)*Real.exp (Real.pi*ξ) = 1 := by
        rw [←Real.exp_add]
        simp
      calc
        _ = (C*(1-Real.exp (-(2*Real.pi/N)*L))⁻¹)*(1+ξ)^k*
          (Real.exp (-Real.pi*ξ)*Real.exp (Real.pi*ξ))*Real.exp (-(2*Real.pi/N)*ξ) := by ring
        _ = _ := by rw [he,mul_one]

end ACS12.NativeCells

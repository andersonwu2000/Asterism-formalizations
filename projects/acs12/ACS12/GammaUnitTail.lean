import ACS12.GammaUnitReflection

/-! The reflected unit Gamma has a direct exponential tail; no Stirling theorem is needed. -/
namespace ACS12.GammaMeasure
set_option backward.isDefEq.respectTransparency false

noncomputable def gammaUnitTailConstant : ℝ :=
  1+2*Real.pi/(1-Real.exp (-(2*Real.pi)))

theorem gammaUnitTailConstant_pos : 0 < gammaUnitTailConstant := by
  have h : Real.exp (-(2*Real.pi)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  unfold gammaUnitTailConstant
  exact add_pos zero_lt_one (div_pos (by positivity) (sub_pos.mpr h))

theorem gammaUnit_tail {u : ℝ} (hu : 1 ≤ u) :
    ‖Complex.Gamma (gammaArgument 1 u)‖ ≤
      gammaUnitTailConstant*u*Real.exp (-Real.pi*u/2) := by
  have hu₀ : 0 < u := by linarith
  let k := 1-Real.exp (-(2*Real.pi))
  have hk : 0 < k := by
    dsimp only [k]
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos]))
  have hExp : Real.exp (-(2*Real.pi*u)) ≤ Real.exp (-(2*Real.pi)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hS : k*Real.exp (Real.pi*u)/2 ≤ Real.sinh (Real.pi*u) := by
    rw [Real.sinh_eq]
    have he : Real.exp (-(Real.pi*u)) =
        Real.exp (Real.pi*u)*Real.exp (-(2*Real.pi*u)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    have hh := mul_le_mul_of_nonneg_left hExp (Real.exp_pos (Real.pi*u)).le
    dsimp only [k]
    nlinarith only [hh]
  have hLeft : 0 < k*Real.exp (Real.pi*u)/2 := by positivity
  have hSq : ‖Complex.Gamma (gammaArgument 1 u)‖^2 ≤
      (2*Real.pi/k)*u*Real.exp (-(Real.pi*u)) := by
    rw [gammaUnit_norm_sq hu₀]
    calc
      _ ≤ Real.pi*u/(k*Real.exp (Real.pi*u)/2) :=
        div_le_div_of_nonneg_left (by positivity) hLeft hS
      _ = _ := by
        rw [Real.exp_neg]
        field_simp [hk.ne',Real.exp_ne_zero]
  have hC : gammaUnitTailConstant = 1+2*Real.pi/k := rfl
  have hCoeff : (2*Real.pi/k)*u ≤ (gammaUnitTailConstant*u)^2 := by
    have hb : 0 ≤ 2*Real.pi/k := by positivity
    rw [hC]
    nlinarith [sq_nonneg (2*Real.pi/k),sq_nonneg (u-1),
      mul_nonneg hb (sub_nonneg.mpr hu)]
  have hTarget : (gammaUnitTailConstant*u*Real.exp (-Real.pi*u/2))^2 =
      (gammaUnitTailConstant*u)^2*Real.exp (-(Real.pi*u)) := by
    rw [mul_pow,←Real.exp_nat_mul]
    congr 2
    ring
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (mul_nonneg gammaUnitTailConstant_pos.le hu₀.le) (Real.exp_pos _).le)).mp
  rw [hTarget]
  exact hSq.trans (mul_le_mul_of_nonneg_right hCoeff (Real.exp_pos _).le)

end ACS12.GammaMeasure


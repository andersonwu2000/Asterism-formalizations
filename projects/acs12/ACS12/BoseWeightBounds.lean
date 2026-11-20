import ACS12.GammaUnitReflection

/-! Direct origin and tail bounds for the literal full Bose weight. -/
namespace ACS12.NativeCells
set_option backward.isDefEq.respectTransparency false

theorem sinh_le_mul_exp {x : ℝ} (hx : 0 ≤ x) : Real.sinh x ≤ x*Real.exp x := by
  rw [Real.sinh_eq]
  have h := Real.add_one_le_exp (-2*x)
  have he : Real.exp (-x) = Real.exp x*Real.exp (-2*x) := by
    rw [←Real.exp_add]
    congr 1
    ring
  rw [he]
  have hh := mul_le_mul_of_nonneg_left h (Real.exp_pos x).le
  nlinarith only [hh]

theorem bose_weight_origin_bound {d L ξ : ℝ} (hd : 0 < d) (hξ : 0 < ξ) (hξL : ξ ≤ L) :
    Real.sinh (Real.pi*ξ)/(Real.exp (d*ξ)-1) ≤ Real.pi*Real.exp (Real.pi*L)/d := by
  have hDen : 0 < Real.exp (d*ξ)-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos hd hξ))
  have hD : d*ξ ≤ Real.exp (d*ξ)-1 := by linarith only [Real.add_one_le_exp (d*ξ)]
  have hS : Real.sinh (Real.pi*ξ) ≤ Real.pi*ξ*Real.exp (Real.pi*L) := by
    exact (sinh_le_mul_exp (by positivity)).trans
      (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hξL Real.pi_pos.le)) (by positivity))
  apply (div_le_iff₀ hDen).mpr
  have h := mul_le_mul_of_nonneg_left hD
    (show 0 ≤ Real.pi*Real.exp (Real.pi*L)/d by positivity)
  have hEq : (Real.pi*Real.exp (Real.pi*L)/d)*(d*ξ) =
      Real.pi*ξ*Real.exp (Real.pi*L) := by field_simp [hd.ne']
  rw [hEq] at h
  exact hS.trans h

theorem bose_weight_tail_bound {d L ξ : ℝ} (hd : 0 < d) (hL : 0 < L) (hξ : L ≤ ξ) :
    Real.sinh (Real.pi*ξ)/(Real.exp (d*ξ)-1) ≤
      (1-Real.exp (-d*L))⁻¹*Real.exp (Real.pi*ξ)*Real.exp (-d*ξ) := by
  have hξ₀ : 0 < ξ := hL.trans_le hξ
  have hk : 0 < 1-Real.exp (-d*L) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith only [mul_pos hd hL]))
  have hD : (1-Real.exp (-d*L))*Real.exp (d*ξ) ≤ Real.exp (d*ξ)-1 := by
    have hE : 1 ≤ Real.exp (-d*L)*Real.exp (d*ξ) := by
      rw [←Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      nlinarith only [hξ,hd]
    nlinarith only [hE]
  have hS : Real.sinh (Real.pi*ξ) ≤ Real.exp (Real.pi*ξ) := by
    rw [Real.sinh_eq]
    linarith [Real.exp_pos (-(Real.pi*ξ)),Real.exp_pos (Real.pi*ξ)]
  calc
    _ ≤ Real.exp (Real.pi*ξ)/((1-Real.exp (-d*L))*Real.exp (d*ξ)) :=
      div_le_div₀ (Real.exp_pos _).le hS (by positivity) hD
    _ = _ := by
      rw [show -d*ξ = -(d*ξ) by ring,Real.exp_neg]
      field_simp [hk.ne',Real.exp_ne_zero]

end ACS12.NativeCells

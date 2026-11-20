import ACS12.NativeBetaRow

/-! Euler reflection fixes the common-law entrance coefficient; no normalization is fitted. -/
namespace ACS12.NativeCells
open GammaDeficit

noncomputable def nativeJointScale (p : ℝ) : ℝ :=
  (4:ℝ)^((p-2)/2)/(3*Real.Gamma (p/2))

theorem nativeJointScale_pos {p : ℝ} (hp : 0 < p) : 0 < nativeJointScale p := by
  unfold nativeJointScale
  positivity

theorem nativeJoint_entrance_scale {p : ℝ} (hp : 0 < p) (hp₁ : p < 1) :
    nativeGammaScale p*Real.Gamma (1-p/2)/(12*sineScale p) = nativeJointScale p := by
  let θ := Real.pi*p/2
  have hθ : 0 < θ := by unfold θ; positivity
  have hθπ : θ < Real.pi := by unfold θ; nlinarith [Real.pi_pos]
  have hS : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ hθπ
  have hC : 0 < Real.cos θ := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> dsimp only [θ] <;> nlinarith [Real.pi_pos]
  have hSin : Real.sin (Real.pi*p) = 2*Real.sin θ*Real.cos θ := by
    rw [show Real.pi*p = 2*θ by unfold θ; ring,Real.sin_two_mul]
  have hP : Real.Gamma p*Real.Gamma (1-p)*(2*Real.sin θ*Real.cos θ) = Real.pi := by
    have h := Real.Gamma_mul_Gamma_one_sub p
    rw [hSin] at h
    exact (eq_div_iff (by positivity : 2*Real.sin θ*Real.cos θ ≠ 0)).mp h
  have hHalf : Real.Gamma (p/2)*Real.Gamma (1-p/2)*Real.sin θ = Real.pi := by
    have h := Real.Gamma_mul_Gamma_one_sub (p/2)
    rw [show Real.pi*(p/2) = θ by unfold θ; ring] at h
    exact (eq_div_iff hS.ne').mp h
  have hG : Real.Gamma (p/2)*Real.Gamma (1-p/2) =
      2*Real.Gamma p*Real.Gamma (1-p)*Real.cos θ := by
    apply mul_right_cancel₀ hS.ne'
    nlinarith only [hHalf,hP]
  have h4 : (4:ℝ)^((p-2)/2) = (2:ℝ)^(p-2) := by
    rw [show (4:ℝ) = (2:ℝ)^(2:ℝ) by norm_num,← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    congr 1
    ring
  have hTwo : (2:ℝ)^(p-1) = (2:ℝ)^(p-2)*2 := by
    rw [← Real.rpow_add_one (by norm_num : (2:ℝ)≠0)]
    congr 1
    ring
  unfold nativeGammaScale nativeJointScale sineScale
  change _ = (4:ℝ)^((p-2)/2)/(3*Real.Gamma (p/2))
  rw [h4,hTwo]
  have hG₀ := Real.Gamma_pos_of_pos hp
  have hG₁ := Real.Gamma_pos_of_pos (sub_pos.mpr hp₁)
  have hG₂ := Real.Gamma_pos_of_pos (by positivity : 0<p/2)
  change (2:ℝ)^(p-2)*2/Real.Gamma p*Real.Gamma (1-p/2)/
    (12*(Real.Gamma (1-p)*Real.cos θ)) = (2:ℝ)^(p-2)/(3*Real.Gamma (p/2))
  field_simp [hG₀.ne',hG₁.ne',hG₂.ne',hC.ne']
  rw [show (2-p)/2 = 1-p/2 by ring]
  linear_combination 6*hG

end ACS12.NativeCells

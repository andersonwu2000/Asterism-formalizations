import ACS12.PressureFeePade
import ACS12.PressureBose

/-! Monotonicity of the entire fixed-neighbor force deficit on the positive axis. -/
namespace ACS12.Pressure

open Set CenteredCircle.AllN

noncomputable def oppositeRayBose (r g s : ℝ) : ℝ :=
  Real.exp (-(g - r) * s) * pressureBose r s

noncomputable def minimumAtomTest (a r g s : ℝ) : ℝ := s * (a + oppositeRayBose r g s)

noncomputable def oppositeDeficit (r g s : ℝ) : ℝ := 1 / s - oppositeRayBose r g s

private noncomputable def boseForceSlope (r s : ℝ) : ℝ :=
  r ^ 2 * (Real.exp (r * s) / (Real.exp (r * s) - 1) ^ 2)

private theorem pressureBose_deriv_s {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    HasDerivAt (pressureBose r) (-boseForceSlope r s) s := by
  have hE := (Real.hasDerivAt_exp (r * s)).comp s ((hasDerivAt_id s).const_mul r)
  have h := (hasDerivAt_const s r).div (hE.sub_const 1) (expTail_den_pos (mul_pos hr hs)).ne'
  have hEq : pressureBose r =ᶠ[nhds s] (fun t => r / (Real.exp (r * t) - 1)) := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    rw [pressureBose_eq hr ht,scaledExpTail,mul_comm]
  apply HasDerivAt.congr_of_eventuallyEq _ hEq
  convert h using 1
  simp only [Function.comp_apply,id_eq,mul_one,zero_mul,zero_sub,boseForceSlope]
  ring

private theorem pressureBose_le_mul_slope {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    pressureBose r s ≤ s * boseForceSlope r s := by
  have hX := mul_pos hr hs
  have hE := Real.exp_pos (r * s)
  have hD := expTail_den_pos hX
  have hExp : (Real.exp (r * s) - 1) ≤ (r * s) * Real.exp (r * s) := by
    have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-(r * s))) hE.le
    rw [add_mul,one_mul,← Real.exp_add,neg_add_cancel,Real.exp_zero] at h
    linarith only [h]
  rw [pressureBose_eq hr hs,scaledExpTail,mul_comm s r,boseForceSlope]
  have h := mul_le_mul_of_nonneg_left hExp hr.le
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hD)).mp
  convert h using 1 <;> field_simp [hD.ne'] <;> ring

private theorem boseForceSlope_le {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    boseForceSlope r s ≤ 1 / s ^ 2 := by
  have h := mul_le_mul_of_nonneg_left (bose_slope_le_inv_sq (mul_pos hr hs)) (sq_nonneg r)
  apply h.trans_eq
  field_simp [hr.ne',hs.ne']

private theorem scaledBoseForceSlope_le {r s d : ℝ} (hr : 0 < r) (hs : 0 < s) (hd : 0 ≤ d) :
    Real.exp (-d * s) * (d * pressureBose r s + boseForceSlope r s) ≤ 1 / s ^ 2 := by
  let β := pressureBose r s
  let G := boseForceSlope r s
  let f (d : ℝ) := Real.exp (-d * s) * (d * β + G)
  have hD (d : ℝ) : HasDerivAt f
      (Real.exp (-d * s) * (β - s * G - s * d * β)) d := by
    have h₁ := (((hasDerivAt_id d).neg).mul_const s).exp
    have h₂ := ((hasDerivAt_id d).mul_const β).add_const G
    convert h₁.mul h₂ using 1
    simp only [id_eq,Pi.neg_apply,mul_one]
    ring
  have hAnti : AntitoneOn f (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · exact fun x _ => (hD x).continuousAt.continuousWithinAt
    · exact fun x _ => (hD x).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx₀ : 0 ≤ x := interior_subset hx
      rw [(hD x).deriv]
      have h := pressureBose_le_mul_slope hr hs
      have hB : 0 ≤ s * x * β := mul_nonneg (mul_nonneg hs.le hx₀) (pressureBose_pos hr hs).le
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith only [h,hB])
  have hC := hAnti (mem_Ici.mpr (le_refl (0 : ℝ))) (mem_Ici.mpr hd) hd
  have hG : f 0 = G := by simp only [f,neg_zero,zero_mul,Real.exp_zero,zero_add,one_mul]
  rw [hG] at hC
  exact hC.trans (boseForceSlope_le hr hs)

theorem oppositeDeficit_antitone {r g : ℝ} (hr : 0 < r) (hg : r ≤ g) :
    AntitoneOn (oppositeDeficit r g) (Ioi 0) := by
  let d := g - r
  have hd : 0 ≤ d := sub_nonneg.mpr hg
  have hD (s : ℝ) (hs : 0 < s) : HasDerivAt (oppositeDeficit r g)
      (-(1 / s ^ 2) + Real.exp (-d * s) * (d * pressureBose r s + boseForceSlope r s)) s := by
    have h₁ := (hasDerivAt_const s (1 : ℝ)).div (hasDerivAt_id s) hs.ne'
    have h₂ := ((((hasDerivAt_id s).const_mul (-d)).exp).mul (pressureBose_deriv_s hr hs))
    convert h₁.sub h₂ using 1
    simp only [id_eq,one_mul,mul_one,zero_mul,zero_sub]
    ring
  apply antitoneOn_of_deriv_nonpos (convex_Ioi _)
  · exact fun s hs => (hD s hs).continuousAt.continuousWithinAt
  · exact fun s hs => (hD s (interior_subset hs)).differentiableAt.differentiableWithinAt
  · intro s hs
    have hs₀ : 0 < s := interior_subset hs
    rw [(hD s hs₀).deriv]
    linarith only [scaledBoseForceSlope_le hr hs₀ hd]

theorem minimumAtomTest_div_mono {a r g Z : ℝ} (hr : 0 < r) (hg : r ≤ g) (hZ : 1 ≤ Z) :
    MonotoneOn (fun s => (minimumAtomTest a r g s - Z) / s) (Ioi 0) := by
  have hE (s : ℝ) (hs : 0 < s) :
      (minimumAtomTest a r g s - Z) / s = a - oppositeDeficit r g s + (1 - Z) / s := by
    unfold minimumAtomTest oppositeDeficit
    field_simp [hs.ne']
    ring
  intro s hs t ht h
  dsimp only
  rw [hE s hs,hE t ht]
  have hA := oppositeDeficit_antitone hr hg hs ht h
  have h' := one_div_le_one_div_of_le hs h
  have hB := mul_le_mul_of_nonpos_left h' (sub_nonpos.mpr hZ)
  simp only [mul_one_div] at hB
  linarith only [hA,hB]

end ACS12.Pressure

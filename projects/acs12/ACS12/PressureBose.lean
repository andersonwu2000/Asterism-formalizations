import ACS12.PressureMaxPacking
import ACS12.GammaLikelihood

/-! The packed Bose ray and the exact maximum-cut inequality. -/
namespace ACS12.Pressure

open Set CenteredCircle.AllN

noncomputable def pressureBose (Q s : ℝ) : ℝ :=
  Q * (Real.exp (-s * Q) / periodicDen Q s)

theorem pressureBose_pos {Q s : ℝ} (hQ : 0 < Q) (hs : 0 < s) : 0 < pressureBose Q s :=
  mul_pos hQ (div_pos (Real.exp_pos _) (periodicDen_pos hQ hs))

theorem pressureBose_eq {Q s : ℝ} (hQ : 0 < Q) (hs : 0 < s) :
    pressureBose Q s = scaledExpTail s Q := by
  unfold pressureBose periodicDen scaledExpTail
  have hExp := Real.exp_pos (s * Q)
  have hD := (expTail_den_pos (mul_pos hs hQ)).ne'
  rw [neg_mul,Real.exp_neg]
  field_simp [hExp.ne',hD,show 1 - (Real.exp (s * Q))⁻¹ ≠ 0 by
    have h := periodicDen_pos hQ hs
    unfold periodicDen at h
    rw [neg_mul,Real.exp_neg] at h
    exact h.ne']

private theorem bose_affine_guard {x : ℝ} (hx : 0 < x) :
    0 < (x - 2) * Real.exp x + x + 2 := by
  let f (x : ℝ) := (x - 2) * Real.exp x + x + 2
  let g (x : ℝ) := (x - 1) * Real.exp x + 1
  have hG (x : ℝ) : HasDerivAt g (x * Real.exp x) x := by
    convert (((hasDerivAt_id x).sub_const 1).mul (Real.hasDerivAt_exp x)).add_const 1 using 1
    simp only [id_eq,one_mul]
    ring
  have hF (x : ℝ) : HasDerivAt f (g x) x := by
    convert ((((hasDerivAt_id x).sub_const 2).mul (Real.hasDerivAt_exp x)).add
      (hasDerivAt_id x)).add_const 2 using 1
    simp only [g,id_eq,one_mul]
    ring
  have hGS : StrictMonoOn g (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
    · exact fun x _ => (hG x).continuousAt.continuousWithinAt
    · intro x hx
      rw [(hG x).deriv]
      rw [interior_Ici] at hx
      exact mul_pos hx (Real.exp_pos _)
  have hGpos {x : ℝ} (hx : 0 < x) : 0 < g x := by
    have h := hGS (mem_Ici.mpr (le_refl (0 : ℝ))) (mem_Ici.mpr hx.le) hx
    simpa [g] using h
  have hFS : StrictMonoOn f (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
    · exact fun x _ => (hF x).continuousAt.continuousWithinAt
    · intro x hx
      rw [(hF x).deriv]
      rw [interior_Ici] at hx
      exact hGpos hx
  simpa [f] using hFS (mem_Ici.mpr (le_refl (0 : ℝ))) (mem_Ici.mpr hx.le) hx

theorem one_lt_pressureBose_multiplier {Q s : ℝ} (hQ : 0 < Q) (hs : 0 < s) :
    1 < s * (Q / 2 + pressureBose Q s) := by
  let x := s * Q
  have hx := mul_pos hs hQ
  have hD : 0 < Real.exp x - 1 := expTail_den_pos hx
  rw [pressureBose_eq hQ hs,scaledExpTail,mul_add,← mul_div_assoc,← mul_div_assoc]
  change 1 < x / 2 + x / (Real.exp x - 1)
  have hA := bose_affine_guard hx
  have hB : 1 - x / 2 < x / (Real.exp x - 1) := by
    apply (lt_div_iff₀ hD).mpr
    nlinarith only [hA]
  linarith only [hB]

theorem pressureBose_product_gt {Q s A B : ℝ} (hQ : 0 < Q) (hs : 0 < s)
    (hA : 0 < A) (hB : 0 < B) (hAU : A ≤ pressureBose Q s) (hBU : B ≤ pressureBose Q s) :
    A + B - s * pressureBose Q s ^ 2 < s * (A * B + (Q / 2) * (A + B)) := by
  let β := pressureBose Q s
  have hG : 0 ≤ s * ((β - A) * (β - B)) :=
    mul_nonneg hs.le (mul_nonneg (sub_nonneg.mpr hAU) (sub_nonneg.mpr hBU))
  have hP := mul_lt_mul_of_pos_right (one_lt_pressureBose_multiplier hQ hs) (add_pos hA hB)
  change 1 * (A + B) < (s * (Q / 2 + β)) * (A + B) at hP
  change A + B - s * β ^ 2 < s * (A * B + (Q / 2) * (A + B))
  linarith only [hP,hG]

end ACS12.Pressure

import ACS12.BoseMoments
import ACS12.BoseShape

/-! A complete second-Bernoulli upper bound by the Bose integral. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaDeficit (gamma_exp_integral integrable_gamma_exp)

private theorem bose_upper_exp_polynomial_pos {x : ℝ} (hx : 0 < x) :
    0 < (1 - x / 2 + x ^ 2 / 12) * Real.exp x - (1 + x / 2 + x ^ 2 / 12) := by
  let f (t : ℝ) := BoseShape.expQuad 1 (1 / 12) (-1 / 2) 1 t - (1 + t / 2 + t ^ 2 / 12)
  let f₁ (t : ℝ) := BoseShape.expQuad 1 (1 / 12) (-1 / 3) (1 / 2) t - (1 / 2 + t / 6)
  let f₂ (t : ℝ) := BoseShape.expQuad 1 (1 / 12) (-1 / 6) (1 / 6) t - 1 / 6
  let f₃ (t : ℝ) := BoseShape.expQuad 1 (1 / 12) 0 0 t
  have h₁ (t : ℝ) : HasDerivAt f (f₁ t) t := by
    have hP := (((hasDerivAt_id t).div_const 2).const_add 1).add (((hasDerivAt_id t).pow 2).div_const 12)
    convert (BoseShape.expQuad_deriv 1 (1 / 12) (-1 / 2) 1 t).sub hP using 1
    norm_num [f₁, id_eq, Pi.pow_apply, show (2 - 1 : ℕ) = 1 by decide] <;> ring
  have h₂ (t : ℝ) : HasDerivAt f₁ (f₂ t) t := by
    convert (BoseShape.expQuad_deriv 1 (1 / 12) (-1 / 3) (1 / 2) t).sub
      (((hasDerivAt_id t).div_const 6).const_add (1 / 2)) using 1
    norm_num [f₂]
  have h₃ (t : ℝ) : HasDerivAt f₂ (f₃ t) t := by
    convert (BoseShape.expQuad_deriv 1 (1 / 12) (-1 / 6) (1 / 6) t).sub_const (1 / 6) using 1
    norm_num [f₃]
  have hP₃ (t : ℝ) (ht : 0 < t) : 0 < f₃ t := by
    dsimp only [f₃, BoseShape.expQuad]
    positivity
  have hP₂ (t : ℝ) (ht : 0 < t) : 0 < f₂ t :=
    BoseShape.positive_of_derivative (by norm_num [f₂, BoseShape.expQuad]) h₃ hP₃ ht
  have hP₁ (t : ℝ) (ht : 0 < t) : 0 < f₁ t :=
    BoseShape.positive_of_derivative (by norm_num [f₁, BoseShape.expQuad]) h₂ hP₂ ht
  have hP := BoseShape.positive_of_derivative (by norm_num [f, BoseShape.expQuad]) h₁ hP₁ hx
  convert hP using 1
  dsimp only [f, BoseShape.expQuad, one_mul]
  ring

theorem bose_inverse_B2 {s : ℝ} (hs : 0 < s) :
    (1 - Real.exp (-s))⁻¹ < s⁻¹ + 1 / 2 + s / 12 := by
  have hH : expHeadFactor s < 1 + s / 2 + s ^ 2 / 12 := by
    have hExp : expHeadFactor s = s * Real.exp s / (Real.exp s - 1) := by
      unfold expHeadFactor
      apply (div_eq_div_iff (expHead_den_pos hs).ne' (expTail_den_pos hs).ne').mpr
      have he : Real.exp s * Real.exp (-s) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      linear_combination s * he
    rw [hExp]
    apply (div_lt_iff₀ (expTail_den_pos hs)).mpr
    have h := bose_upper_exp_polynomial_pos hs
    nlinarith only [h]
  have he : expHeadFactor s / s = (1 - Real.exp (-s))⁻¹ := by
    unfold expHeadFactor
    field_simp [hs.ne', (expHead_den_pos hs).ne']
  rw [← he]
  apply (div_lt_iff₀ hs).mpr
  have he' : (s⁻¹ + 1 / 2 + s / 12) * s = 1 + s / 2 + s ^ 2 / 12 := by
    field_simp [hs.ne']
  exact he'.symm ▸ hH

/-- The full tail, from m onward, is bounded by its B2 majorant. -/
theorem powerTail_B2 {q : ℝ} (hq : 1 < q) {m : ℕ} (hm : 0 < m) :
    powerTail q m <
      ((m : ℝ) ^ (1 - q)) / (q - 1) + ((m : ℝ) ^ (-q)) / 2 +
        (q / 12) * (m : ℝ) ^ (-(q + 1)) := by
  let d : ℝ := m
  have hd : 0 < d := Nat.cast_pos.mpr hm
  have hq₀ : 0 < q := zero_lt_one.trans hq
  have hq₁ : 0 < q - 1 := sub_pos.mpr hq
  have hG : 0 < Real.Gamma q := Real.Gamma_pos_of_pos hq₀
  let f (s : ℝ) := s ^ (q - 1) * (Real.exp (-s * d) / (1 - Real.exp (-s)))
  let A (s : ℝ) := s ^ (q - 2) * Real.exp (-s * d)
  let B (s : ℝ) := s ^ (q - 1) * Real.exp (-s * d)
  let C (s : ℝ) := s ^ q * Real.exp (-s * d)
  have hf : IntegrableOn f (Ioi 0) := boseMoment_integrable hq₁ hm
  have hA : IntegrableOn A (Ioi 0) := by
    simpa only [A, show q - 1 - 1 = q - 2 by ring, neg_mul, mul_comm d] using integrable_gamma_exp hq₁ hd
  have hB : IntegrableOn B (Ioi 0) := by
    simpa only [B, neg_mul, mul_comm d] using integrable_gamma_exp hq₀ hd
  have hC : IntegrableOn C (Ioi 0) := by
    simpa only [C, add_sub_cancel_right, neg_mul, mul_comm d] using
      integrable_gamma_exp (show 0 < q + 1 by positivity) hd
  have hIAB : IntegrableOn (fun s => A s + (1 / 2) * B s) (Ioi 0) :=
    hA.add (hB.const_mul (1 / 2))
  have hI : IntegrableOn (fun s => A s + (1 / 2) * B s + (1 / 12) * C s) (Ioi 0) :=
    hIAB.add (hC.const_mul (1 / 12))
  letI : NeZero (volume.restrict (Ioi (0 : ℝ))) := ⟨positiveHalfLine_ne_zero⟩
  have hLt := integral_strict_of_ae_lt (volume.restrict (Ioi (0 : ℝ))) hf hI ?_
  · have hfE : (∫ s : ℝ in Ioi 0, f s) = Real.Gamma q * powerTail q m := by
      simpa only [f, d, sub_add_cancel] using boseMoment_integral hq₁ hm
    have hAE : (∫ s : ℝ in Ioi 0, A s) = Real.Gamma (q - 1) * d ^ (1 - q) := by
      simpa only [A, show q - 1 - 1 = q - 2 by ring, show -(q - 1) = 1 - q by ring,
        neg_mul, mul_comm d] using gamma_exp_integral hq₁ hd
    have hBE : (∫ s : ℝ in Ioi 0, B s) = Real.Gamma q * d ^ (-q) := by
      simpa only [B, neg_mul, mul_comm d] using gamma_exp_integral hq₀ hd
    have hCE : (∫ s : ℝ in Ioi 0, C s) = Real.Gamma (q + 1) * d ^ (-(q + 1)) := by
      simpa only [C, add_sub_cancel_right, neg_mul, mul_comm d] using
        gamma_exp_integral (show 0 < q + 1 by positivity) hd
    rw [hfE, integral_add hIAB (hC.const_mul (1 / 12)), integral_add hA (hB.const_mul (1 / 2)),
      integral_const_mul, integral_const_mul, hAE, hBE, hCE, Real.Gamma_add_one hq₀.ne'] at hLt
    have hGamma : Real.Gamma (q - 1) = Real.Gamma q / (q - 1) := by
      apply (eq_div_iff hq₁.ne').mpr
      simpa only [sub_add_cancel, mul_comm] using (Real.Gamma_add_one hq₁.ne').symm
    rw [hGamma] at hLt
    apply lt_of_mul_lt_mul_left ?_ hG.le
    refine hLt.trans_le (le_of_eq ?_)
    dsimp only [d]
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0 < s := hs
    have hMul := mul_lt_mul_of_pos_left (bose_inverse_B2 hs₀)
      (mul_pos (Real.rpow_pos_of_pos hs₀ (q - 1)) (Real.exp_pos (-s * d)))
    have h1 : s ^ (q - 1) * s⁻¹ = s ^ (q - 2) := by
      rw [← div_eq_mul_inv, ← Real.rpow_sub_one hs₀.ne', show q - 1 - 1 = q - 2 by ring]
    have h2 : s ^ (q - 1) * s = s ^ q := by
      rw [Real.rpow_sub_one hs₀.ne', div_mul_cancel₀ _ hs₀.ne']
    dsimp only [f, A, B, C]
    simp only [div_eq_mul_inv]
    nlinarith only [hMul, congrArg (fun x => x * Real.exp (-s * d)) h1,
      congrArg (fun x => (1 / 12) * x * Real.exp (-s * d)) h2]

end ACS12.GammaMeasure


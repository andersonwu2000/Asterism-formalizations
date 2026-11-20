import ACS12.BaseBoseEvenMoments

/-! The ordinary sine transform retains every Bose mode; absolute first moments pay the interchange. -/
namespace ACS12.NativeCells
open MeasureTheory Set Filter GammaMeasure GammaDeficit
open CenteredCircle.AllN

theorem fullBoseSine_hasSum {d : ℝ} (hd : 0 < d) (v : ℝ) :
    HasSum (fun j : ℕ => v/((d*((j:ℝ)+1))^2+v^2))
      (∫ s : ℝ in Ioi 0, Real.sin (v*s)/(Real.exp (d*s)-1)) := by
  let μ := volume.restrict (Ioi (0:ℝ))
  let c (j : ℕ) := d*((j:ℝ)+1)
  let F (j : ℕ) (s : ℝ) := Real.exp (-c j*s)*Real.sin (v*s)
  let G (j : ℕ) (s : ℝ) := |v| * (s*Real.exp (-s*c j))
  have hc (j : ℕ) : 0 < c j := by unfold c; positivity
  have hG (j : ℕ) : Integrable (G j) μ := by
    simpa only [G,μ,pow_one] using (expMoment_nat_integrable 1 (hc j)).const_mul |v|
  have hBound (j : ℕ) : ∀ᵐ s ∂μ, ‖F j s‖ ≤ G j s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0 < s := hs
    unfold F G
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
    have h := Real.abs_sin_le_abs (x := v*s)
    rw [abs_mul,abs_of_pos hs₀] at h
    have h' := mul_le_mul_of_nonneg_left h (Real.exp_pos (-c j*s)).le
    rw [show -s*c j = -c j*s by ring]
    nlinarith only [h']
  have hF (j : ℕ) : Integrable (F j) μ :=
    (hG j).mono' (by unfold F; fun_prop) (hBound j)
  have hIntG (j : ℕ) : (∫ s, G j s ∂μ) = |v|/(c j)^2 := by
    unfold G
    rw [integral_const_mul]
    have h := expMoment_nat_integral 1 (hc j)
    norm_num only [pow_one,Nat.factorial_one,Nat.cast_one,show (1:ℕ)+1=2 by decide] at h
    rw [h]
    ring
  have hS : Summable (fun j : ℕ => |v|/(c j)^2) := by
    have h := (powerTail_summable (by norm_num : (1:ℝ)<2) 1).mul_left (|v|/d^2)
    convert h using 1
    funext j
    unfold c
    rw [Real.rpow_neg (by positivity),Real.rpow_two]
    push_cast
    field_simp [hd.ne',show (1+(j:ℝ))≠0 by positivity,show ((j:ℝ)+1)≠0 by positivity]
    <;> ring
  have hNorm : Summable (fun j => ∫ s, ‖F j s‖ ∂μ) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun j => by rw [← hIntG]; exact integral_mono_ae (hF j).norm (hG j) (hBound j)) hS
  have h := hasSum_integral_of_summable_integral_norm hF hNorm
  have hValue (j : ℕ) : (∫ s, F j s ∂μ) = v/((c j)^2+v^2) :=
    exp_sine_integral (hc j) v
  simp_rw [hValue] at h
  have hPoint (s : ℝ) (hs : s ∈ Ioi (0:ℝ)) :
      (∑' j, F j s) = Real.sin (v*s)/(Real.exp (d*s)-1) := by
    have hs₀ : 0 < s := hs
    have hExp := (exponential_samples_hasSum (d*s) 1 1 (mul_pos hd hs₀) zero_lt_one).mul_right
      (Real.sin (v*s))
    have hTerm (j : ℕ) :
        Real.exp (-(d*s)*(1+(j:ℝ)*1))*Real.sin (v*s) = F j s := by
      unfold F c
      congr 2
      ring
    simp_rw [hTerm] at hExp
    rw [hExp.tsum_eq,mul_one,Real.exp_neg]
    field_simp [(Real.exp_ne_zero (d*s)),
      (expTail_den_pos (mul_pos hd hs₀)).ne',
      show 1-(Real.exp (d*s))⁻¹≠0 by
        intro he
        have hE := expTail_den_pos (mul_pos hd hs₀)
        field_simp [Real.exp_ne_zero (d*s)] at he
        linarith]
  change HasSum (fun x => v/((c x)^2+v^2)) (∫ s : ℝ in Ioi 0, ∑' j, F j s) at h
  have hEq : (∫ s : ℝ in Ioi 0, ∑' j, F j s) =
      ∫ s : ℝ in Ioi 0, Real.sin (v*s)/(Real.exp (d*s)-1) :=
    setIntegral_congr_fun measurableSet_Ioi hPoint
  rw [hEq] at h
  simpa only [c] using h

end ACS12.NativeCells

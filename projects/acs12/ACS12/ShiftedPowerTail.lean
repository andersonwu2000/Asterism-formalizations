import ACS12.BoseBernoulliFour
import ACS12.JointGapK

/-! Complete ordinary Bernoulli bounds on positive real-shift power tails. -/
namespace ACS12.GammaMeasure

open Set Filter MeasureTheory CenteredCircle.AllN
open GammaDeficit (lineDensity lineDensity_exp_integrable lineDensity_exp_integral)

noncomputable def shiftedPowerTail (q x : ℝ) : ℝ :=
  ∑' n : ℕ, (x + (n : ℝ)) ^ (-q)

theorem shiftedPowerTail_summable {q x : ℝ} (hq : 1 < q) (hx : 1 ≤ x) :
    Summable (fun n : ℕ => (x + (n : ℝ)) ^ (-q)) := by
  apply (powerTail_summable hq 1).of_nonneg_of_le
  · intro n
    exact Real.rpow_nonneg (by linarith only [hx,Nat.cast_nonneg (α := ℝ) n]) _
  · intro n
    apply Real.rpow_le_rpow_of_nonpos (by positivity)
    · norm_num only [Nat.cast_one]
      linarith only [hx]
    · linarith only [hq]

theorem shiftedPowerTail_bose {q x : ℝ} (hq : 1 < q) (hx : 1 ≤ x) :
    (∫ s : ℝ in Ioi 0, lineDensity q s * Real.exp (-s * x) * (1 - Real.exp (-s))⁻¹) =
      shiftedPowerTail q x := by
  let f (n : ℕ) (s : ℝ) := lineDensity q s * Real.exp (-s * (x + (n : ℝ)))
  let μ := volume.restrict (Ioi (0 : ℝ))
  have hx₀ := zero_lt_one.trans_le hx
  have hq₀ := zero_lt_one.trans hq
  have hI (n : ℕ) : Integrable (f n) μ := lineDensity_exp_integrable hq₀ (by positivity)
  have hE (n : ℕ) : (∫ s : ℝ, f n s ∂μ) = (x + (n : ℝ)) ^ (-q) :=
    lineDensity_exp_integral hq₀ (by positivity)
  have hN (n : ℕ) : (∫ s : ℝ, ‖f n s‖ ∂μ) = ∫ s : ℝ, f n s ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact Real.norm_of_nonneg (mul_nonneg (lineDensity_pos hq₀ hs).le (Real.exp_pos _).le)
  have hS : Summable (fun n => ∫ s : ℝ, ‖f n s‖ ∂μ) := by
    simp_rw [hN,hE]
    exact shiftedPowerTail_summable hq hx
  have h := integral_tsum_of_summable_integral_norm hI hS
  simp_rw [hE] at h
  refine (integral_congr_ae ?_).trans h.symm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs₀ : 0 < s := hs
  have hP := ((exponential_samples_hasSum s x 1 hs₀ zero_lt_one).mul_left (lineDensity q s)).tsum_eq
  simpa only [f,mul_one,div_eq_mul_inv,mul_assoc] using hP.symm

private theorem shiftedBose_inverse_integral {q x : ℝ} (hq : 1 < q) (hx : 0 < x) :
    let f (s : ℝ) := lineDensity q s * Real.exp (-s * x) * s⁻¹
    IntegrableOn f (Ioi 0) ∧ (∫ s : ℝ in Ioi 0, f s) = x ^ (1 - q) / (q - 1) := by
  let f (s : ℝ) := lineDensity q s * Real.exp (-s * x) * s⁻¹
  let g (s : ℝ) := lineDensity (q - 1) s * Real.exp (-s * x)
  have hq₀ := zero_lt_one.trans hq
  have hq₁ := sub_pos.mpr hq
  have hI : IntegrableOn g (Ioi 0) := lineDensity_exp_integrable hq₁ hx
  have hG : Real.Gamma q = (q - 1) * Real.Gamma (q - 1) := by
    simpa only [sub_add_cancel] using Real.Gamma_add_one hq₁.ne'
  have hE (s : ℝ) (hs : 0 < s) : f s = (q - 1)⁻¹ * g s := by
    unfold f g lineDensity
    rw [hG,Real.rpow_sub_one hs.ne']
    field_simp [hs.ne',hq₁.ne',(Real.Gamma_pos_of_pos hq₁).ne']
    rw [← Real.rpow_two,← Real.rpow_add hs]
    congr 1
    ring
  refine ⟨(hI.const_mul (q - 1)⁻¹).congr ?_,?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hE s hs).symm
  · change (∫ s : ℝ in Ioi 0, f s) = _
    rw [setIntegral_congr_fun measurableSet_Ioi hE,integral_const_mul,lineDensity_exp_integral hq₁ hx,
      show -(q - 1) = 1 - q by ring,div_eq_mul_inv,mul_comm]

theorem shiftedPowerTail_bernoulli {q x : ℝ} (hq : 1 < q) (hx : 1 ≤ x) :
    let upper := x ^ (1 - q) / (q - 1) + x ^ (-q) / 2 + q * x ^ (-q - 1) / 12
    upper - q * (q + 1) * (q + 2) * x ^ (-q - 3) / 720 < shiftedPowerTail q x ∧
      shiftedPowerTail q x < upper := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  let F (s : ℝ) := lineDensity q s * Real.exp (-s * x)
  let A (s : ℝ) := F s * s⁻¹
  let B (s : ℝ) := F s * s
  let C (s : ℝ) := F s * s ^ 3
  let U (s : ℝ) := A s + (1 / 2) * F s + (1 / 12) * B s
  let D (s : ℝ) := F s * (1 - Real.exp (-s))⁻¹
  let E (s : ℝ) := U s - (1 / 720) * C s
  have hx₀ := zero_lt_one.trans_le hx
  have hq₀ := zero_lt_one.trans hq
  have hF : Integrable F μ := lineDensity_exp_integrable hq₀ hx₀
  have hA : Integrable A μ := (shiftedBose_inverse_integral hq hx₀).1
  have hBC (k : ℕ) :
      Integrable (fun s => F s * s ^ k) μ ∧
        (∫ s : ℝ, F s * s ^ k ∂μ) =
          (Real.Gamma (q + k) / Real.Gamma q) * x ^ (-(q + k)) := by
    have h := lineDensity_moment hq₀ hx₀ k
    have hEq (s : ℝ) : F s * s ^ k = lineDensity q s * s ^ k * Real.exp (-s * x) := by unfold F; ring
    simpa only [hEq] using h
  have hB : Integrable B μ := by simpa only [B,pow_one] using (hBC 1).1
  have hC : Integrable C μ := (hBC 3).1
  have hU₀ : Integrable (fun s => A s + (1 / 2) * F s) μ := hA.add (hF.const_mul _)
  have hU : Integrable U μ := hU₀.add (hB.const_mul _)
  have hE : Integrable E μ := hU.sub (hC.const_mul _)
  have hDval : (∫ s : ℝ, D s ∂μ) = shiftedPowerTail q x := shiftedPowerTail_bose hq hx
  have hD : Integrable D μ := Integrable.of_integral_ne_zero (hDval ▸
    ((shiftedPowerTail_summable hq hx).tsum_pos (fun n => Real.rpow_nonneg (by positivity) _) 0 (by positivity)).ne')
  have hComp : ∀ᵐ s ∂μ, E s < D s ∧ D s < U s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0 < s := hs
    have hf : 0 < F s := mul_pos (lineDensity_pos hq₀ hs₀) (Real.exp_pos _)
    have hUp := mul_lt_mul_of_pos_left (bose_inverse_B2 hs₀) hf
    have hLow := mul_lt_mul_of_pos_left (bose_inverse_B4 hs₀) hf
    unfold E D U A B C
    constructor <;> linarith only [hUp,hLow]
  letI : NeZero μ := ⟨positiveHalfLine_ne_zero⟩
  have hUp := integral_strict_of_ae_lt μ hD hU (hComp.mono fun _ hs => hs.2)
  have hLow := integral_strict_of_ae_lt μ hE hD (hComp.mono fun _ hs => hs.1)
  have hG₁ : Real.Gamma (q + 1) / Real.Gamma q = q := by
    rw [Real.Gamma_add_one hq₀.ne']
    field_simp [(Real.Gamma_pos_of_pos hq₀).ne']
  have hG₃ : Real.Gamma (q + 3) / Real.Gamma q = q * (q + 1) * (q + 2) := by
    rw [show q + 3 = q + 1 + 1 + 1 by ring,Real.Gamma_add_one (by positivity : 0 < q + 1 + 1).ne',
      Real.Gamma_add_one (by positivity : 0 < q + 1).ne',Real.Gamma_add_one hq₀.ne']
    field_simp [(Real.Gamma_pos_of_pos hq₀).ne']
    ring
  have hBval : (∫ s : ℝ, B s ∂μ) = q * x ^ (-q - 1) := by
    simpa only [B,pow_one,Nat.cast_one,hG₁,show -(q + 1) = -q - 1 by ring] using (hBC 1).2
  have hCval : (∫ s : ℝ, C s ∂μ) = q * (q + 1) * (q + 2) * x ^ (-q - 3) := by
    simpa only [C,Nat.cast_ofNat,hG₃,show -(q + 3) = -q - 3 by ring] using (hBC 3).2
  have hUval : (∫ s : ℝ, U s ∂μ) =
      x ^ (1 - q) / (q - 1) + x ^ (-q) / 2 + q * x ^ (-q - 1) / 12 := by
    unfold U
    rw [integral_add hU₀ (hB.const_mul _),integral_add hA (hF.const_mul _),integral_const_mul,
      integral_const_mul,(shiftedBose_inverse_integral hq hx₀).2,lineDensity_exp_integral hq₀ hx₀,hBval]
    ring
  have hEval : (∫ s : ℝ, E s ∂μ) = (∫ s : ℝ, U s ∂μ) - (1 / 720) * ∫ s : ℝ, C s ∂μ := by
    unfold E
    rw [integral_sub hU (hC.const_mul _),integral_const_mul]
  rw [hEval,hUval,hCval,hDval] at hLow
  rw [hDval,hUval] at hUp
  exact ⟨by linarith only [hLow],hUp⟩

end ACS12.GammaMeasure


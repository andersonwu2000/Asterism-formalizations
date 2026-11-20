import ACS12.NativeProbabilityCore

/-! The selected common law: a shape-dependent Gamma sum and one fixed Bose noise law, both independent of count. -/
namespace ACS12.NativeCells
open MeasureTheory ProbabilityTheory Set Filter
open GammaMixture (gammaProduct gammaTotal)

abbrev BoseNoiseSample := ℕ × ℝ

noncomputable def boseNoiseMeasure : Measure BoseNoiseSample :=
  (nativeZetaMeasure 2).prod (gammaMeasure 1 1)

noncomputable def boseNoise (s : BoseNoiseSample) : ℝ :=
  s.2 / GammaMixture.gammaRate s.1

theorem boseNoise_probability : IsProbabilityMeasure boseNoiseMeasure := by
  letI := nativeZeta_probability (by norm_num : (1:ℝ)<2)
  letI := isProbabilityMeasure_gammaMeasure zero_lt_one zero_lt_one
  unfold boseNoiseMeasure
  infer_instance

theorem measurable_boseNoise : Measurable boseNoise := by
  unfold boseNoise
  exact measurable_snd.div ((Measurable.of_discrete (f := GammaMixture.gammaRate)).comp measurable_fst)

theorem boseNoise_ae_pos : ∀ᵐ s ∂boseNoiseMeasure, 0 < boseNoise s := by
  letI := nativeZeta_probability (by norm_num : (1:ℝ)<2)
  letI := isProbabilityMeasure_gammaMeasure zero_lt_one zero_lt_one
  have h : ∀ᵐ s : BoseNoiseSample ∂boseNoiseMeasure, 0 < s.2 :=
    Measure.quasiMeasurePreserving_snd.ae (gammaUnit_ae_pos 1)
  exact h.mono fun s hs => div_pos hs (GammaMixture.gammaRate_pos s.1)

abbrev NativeJointSample := (ℕ → ℝ) × BoseNoiseSample

noncomputable def nativeJointMeasure (p : ℝ) : Measure NativeJointSample :=
  (gammaProduct p).prod boseNoiseMeasure

noncomputable def nativeJointEnergy (z : ℝ) (s : NativeJointSample) : ℝ :=
  gammaTotal s.1 + z*boseNoise s.2

theorem nativeJoint_probability {p : ℝ} (hp : 0 < p) :
    IsProbabilityMeasure (nativeJointMeasure p) := by
  letI := GammaMixture.gammaProduct_probability hp
  letI := boseNoise_probability
  unfold nativeJointMeasure
  infer_instance

theorem measurable_nativeJointEnergy (z : ℝ) : Measurable (nativeJointEnergy z) :=
  (GammaMixture.measurable_gammaTotal.comp measurable_fst).add
    ((measurable_boseNoise.comp measurable_snd).const_mul z)

theorem nativeJoint_coordinates_ae_pos {p : ℝ} (hp : 0 < p) :
    ∀ᵐ s ∂nativeJointMeasure p, 0 < gammaTotal s.1 ∧ 0 < boseNoise s.2 := by
  letI := GammaMixture.gammaProduct_probability hp
  letI := boseNoise_probability
  have hX : ∀ᵐ s : NativeJointSample ∂nativeJointMeasure p, 0 < gammaTotal s.1 :=
    Measure.quasiMeasurePreserving_fst.ae (GammaMixture.gammaProduct_ae_total_pos hp)
  have hχ : ∀ᵐ s : NativeJointSample ∂nativeJointMeasure p, 0 < boseNoise s.2 :=
    Measure.quasiMeasurePreserving_snd.ae boseNoise_ae_pos
  exact hX.and hχ

theorem nativeJointEnergy_ae_pos {p z : ℝ} (hp : 0 < p) (hz : 0 ≤ z) :
    ∀ᵐ s ∂nativeJointMeasure p, 0 < nativeJointEnergy z s :=
  (nativeJoint_coordinates_ae_pos hp).mono fun s hs =>
    add_pos_of_pos_of_nonneg hs.1 (mul_nonneg hz hs.2.le)

theorem exponentialUnit_laplace {c : ℝ} (hc : 0 ≤ c) :
    (∫ e : ℝ, Real.exp (-c*e) ∂gammaMeasure 1 1) = 1/(1+c) := by
  rw [gammaUnitIntegral zero_lt_one]
  have hPoint (e : ℝ) (he : e ∈ Ioi (0:ℝ)) :
      (Real.Gamma 1)⁻¹*e^((1:ℝ)-1)*Real.exp (-e)*Real.exp (-c*e) =
        Real.exp (-(1+c)*e) := by
    norm_num only [Real.Gamma_one,inv_one,sub_self,Real.rpow_zero,mul_one,one_mul]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hPoint,
    integral_exp_mul_Ioi (by linarith : -(1+c)<0)]
  simp only [mul_zero,Real.exp_zero]
  field_simp [show 1+c ≠ 0 by linarith,show -(1+c) ≠ 0 by linarith]
  <;> ring

end ACS12.NativeCells

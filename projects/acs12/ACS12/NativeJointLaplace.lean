import ACS12.NativeJointGammaLaw

/-! Exact Laplace transforms of the fixed Bose noise and the count-dependent joint energy. -/
namespace ACS12.NativeCells
open MeasureTheory ProbabilityTheory Set Filter
open GammaMixture (gammaProduct gammaTotal)

theorem boseNoise_laplace {c : ℝ} (hc : 0 ≤ c) :
    (∫ s, Real.exp (-c*boseNoise s) ∂boseNoiseMeasure) =
      ∑' k : ℕ, nativeZetaWeight 2 k/(1+c/GammaMixture.gammaRate k) := by
  let ν := nativeZetaMeasure 2
  let γ := gammaMeasure 1 1
  let F (s : BoseNoiseSample) := Real.exp (-c*boseNoise s)
  let G (k : ℕ) := 1/(1+c/GammaMixture.gammaRate k)
  letI := nativeZeta_probability (by norm_num : (1:ℝ)<2)
  letI := isProbabilityMeasure_gammaMeasure zero_lt_one zero_lt_one
  have hM : Measurable F := (measurable_boseNoise.const_mul (-c)).exp
  have hI : Integrable F (ν.prod γ) := by
    apply (integrable_const (μ := ν.prod γ) (1:ℝ)).mono' hM.aestronglyMeasurable
    exact boseNoise_ae_pos.mono fun s hs => by
      dsimp only [F]
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) hs.le)
  have hSlice (k : ℕ) : (∫ e, F (k,e) ∂γ) = G k := by
    have h := exponentialUnit_laplace (div_nonneg hc (GammaMixture.gammaRate_pos k).le)
    convert h using 1
    congr 1
    funext e
    unfold F boseNoise
    congr 1
    ring
  have hGI : Integrable G ν := by
    apply (integrable_const (μ := ν) (1:ℝ)).mono' (Measurable.of_discrete (f := G)).aestronglyMeasurable
    exact Eventually.of_forall fun k => by
      have hC := div_nonneg hc (GammaMixture.gammaRate_pos k).le
      unfold G
      rw [Real.norm_of_nonneg (by positivity)]
      exact (div_le_one (by positivity)).mpr (by linarith)
  change (∫ s, F s ∂ν.prod γ) = _
  rw [integral_prod F hI]
  simp_rw [hSlice]
  rw [nativeZeta_integral_eq_tsum (by norm_num : (1:ℝ)<2) G hGI]
  apply tsum_congr
  intro k
  unfold G
  ring

theorem nativeJoint_laplace {p t z : ℝ} (hp : 0 < p) (ht : 0 < t) (hz : 0 ≤ z) :
    (∫ s, Real.exp (-(t^2)*nativeJointEnergy z s) ∂nativeJointMeasure p) =
      (t/(2*Real.sinh (t/2)))^p *
        ∑' k : ℕ, nativeZetaWeight 2 k/(1+(t^2*z)/GammaMixture.gammaRate k) := by
  letI := GammaMixture.gammaProduct_probability hp
  letI := boseNoise_probability
  have hPoint : (fun s : NativeJointSample => Real.exp (-(t^2)*nativeJointEnergy z s)) =
      (fun s : NativeJointSample =>
        Real.exp (-(t^2)*gammaTotal s.1)*Real.exp (-(t^2*z)*boseNoise s.2)) := by
    funext s
    unfold nativeJointEnergy
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hPoint,nativeJointMeasure,
    integral_prod_mul (fun ω : ℕ → ℝ => Real.exp (-(t^2)*gammaTotal ω))
      (fun s : BoseNoiseSample => Real.exp (-(t^2*z)*boseNoise s)),
    GammaMixture.gammaTotal_laplace hp ht,
    boseNoise_laplace (mul_nonneg (sq_nonneg t) hz)]

theorem nativeJoint_laplace_product {p t z : ℝ} (hp : 0 < p) (ht : 0 < t) (hz : 0 ≤ z) :
    (∫ s, Real.exp (-(t^2)*nativeJointEnergy z s) ∂nativeJointMeasure p) =
      (t/(2*Real.sinh (t/2)))^p *
        ∫ s, Real.exp (-(t^2*z)*boseNoise s) ∂boseNoiseMeasure := by
  rw [nativeJoint_laplace hp ht hz,boseNoise_laplace (mul_nonneg (sq_nonneg t) hz)]

end ACS12.NativeCells

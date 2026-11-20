import ACS12.NativeJointLaplace
import ACS12.GammaDeficitMomentReduction

/-! The ordinary negative-moment entrance has a finite complete joint-law Mellin kernel. -/
namespace ACS12.NativeCells
open MeasureTheory Set Filter GammaDeficit
open scoped Topology

noncomputable def nativeJointLaplaceValue (p z s : ℝ) : ℝ :=
  ∫ ω, Real.exp (-s*nativeJointEnergy z ω) ∂nativeJointMeasure p

theorem measurable_nativeJointLaplaceValue {p : ℝ} (hp : 0 < p) (z : ℝ) :
    Measurable (nativeJointLaplaceValue p z) := by
  letI := nativeJoint_probability hp
  have hM : Measurable (fun a : ℝ × NativeJointSample =>
      Real.exp (-a.1*nativeJointEnergy z a.2)) :=
    (measurable_fst.neg.mul ((measurable_nativeJointEnergy z).comp measurable_snd)).exp
  exact hM.stronglyMeasurable.integral_prod_right'.measurable

theorem nativeJointLaplaceValue_bounds {p z s : ℝ} (hp : 0 < p) (hz : 0 ≤ z) (hs : 0 ≤ s) :
    0 ≤ nativeJointLaplaceValue p z s ∧ nativeJointLaplaceValue p z s ≤ 1 := by
  letI := nativeJoint_probability hp
  constructor
  · exact integral_nonneg fun _ => (Real.exp_pos _).le
  · have hBound : ∀ᵐ ω ∂nativeJointMeasure p, Real.exp (-s*nativeJointEnergy z ω) ≤ 1 :=
      (nativeJointEnergy_ae_pos hp hz).mono fun ω hω =>
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) hω.le)
    have h := integral_mono_of_nonneg (μ := nativeJointMeasure p)
      (Eventually.of_forall fun _ => (Real.exp_pos _).le) (integrable_const (1:ℝ)) hBound
    simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using h

noncomputable def nativeJointNegativeKernel (p N s : ℝ) : ℝ :=
  s^(-p/2)*nativeJointLaplaceValue p (N^2) s

theorem jointNegativeKernel_square {p N t : ℝ} (hp : 0 < p) (hN : 0 < N) (ht : 0 < t) :
    |2*t| * nativeJointNegativeKernel p N (t^2) =
      2*(t*sinhProfile p t) *
        ∫ s, Real.exp (-(t^2*N^2)*boseNoise s) ∂boseNoiseMeasure := by
  have hSin : 0 < 2*Real.sinh (t/2) := by positivity
  have hPow : (t^2)^(-p/2)*(t/(2*Real.sinh (t/2)))^p = sinhProfile p t := by
    have hT : (t^2)^(-p/2) = t^(-p) := by
      rw [show t^2 = t^(2:ℝ) by rw [Real.rpow_two],← Real.rpow_mul ht.le,
        show (2:ℝ)*(-p/2) = -p by ring]
    rw [hT,Real.div_rpow ht.le hSin.le,sinhProfile,Real.rpow_neg ht.le,Real.rpow_neg hSin.le]
    field_simp [(Real.rpow_pos_of_pos ht p).ne']
  unfold nativeJointNegativeKernel nativeJointLaplaceValue
  rw [abs_of_pos (mul_pos zero_lt_two ht),nativeJoint_laplace_product hp ht (sq_nonneg N)]
  linear_combination (2*t*(∫ s, Real.exp (-(t^2*N^2)*boseNoise s) ∂boseNoiseMeasure))*hPow

theorem nativeJointNegativeKernel_integrable {p N : ℝ} (hp : 0 < p) (hp₂ : p < 2) (hN : 0 < N) :
    IntegrableOn (nativeJointNegativeKernel p N) (Ioi 0) := by
  let f (t : ℝ) := t^2
  have hImg : f '' Ioi (0:ℝ) = Ioi 0 := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      change 0 < t at ht
      exact sq_pos_of_pos ht
    · intro hx
      exact ⟨Real.sqrt x,Real.sqrt_pos.mpr hx,Real.sq_sqrt hx.le⟩
  have hD (t : ℝ) : HasDerivAt f (2*t) t := by
    simpa only [Nat.cast_ofNat,show (2:ℕ)-1=1 by decide,pow_one] using hasDerivAt_pow 2 t
  have hInj : (Ioi (0:ℝ)).InjOn f := by
    intro x hx y hy h
    exact (sq_eq_sq₀ hx.le hy.le).mp h
  have hK : Measurable (nativeJointNegativeKernel p N) :=
    (measurable_id.pow_const _).mul (measurable_nativeJointLaplaceValue hp (N^2))
  have hMajor := (sinhProfile_moment_one_integrable hp hp₂).const_mul (2:ℝ)
  have hI : IntegrableOn (fun t => |2*t| * nativeJointNegativeKernel p N (f t)) (Ioi 0) := by
    apply hMajor.mono' (((by fun_prop : Measurable (fun t : ℝ => |2*t|))).mul
      (hK.comp (by unfold f; fun_prop : Measurable f))).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht₀ : 0 < t := ht
    simp only [Function.comp_apply]
    rw [show f t = t^2 by rfl,jointNegativeKernel_square hp hN ht₀]
    have hχ : 0 ≤ ∫ s, Real.exp (-(t^2*N^2)*boseNoise s) ∂boseNoiseMeasure :=
      integral_nonneg fun _ => (Real.exp_pos _).le
    have hχU : (∫ s, Real.exp (-(t^2*N^2)*boseNoise s) ∂boseNoiseMeasure) ≤ 1 := by
      letI := boseNoise_probability
      have h := integral_mono_of_nonneg (μ := boseNoiseMeasure)
        (Eventually.of_forall fun _ => (Real.exp_pos _).le) (integrable_const (1:ℝ))
        (boseNoise_ae_pos.mono fun s hs =>
          Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
            (neg_nonpos.mpr (mul_nonneg (sq_nonneg t) (sq_nonneg N))) hs.le))
      simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using h
    have hP : 0 ≤ 2*(t*sinhProfile p t) := by unfold sinhProfile; positivity
    rw [Real.norm_of_nonneg (mul_nonneg hP hχ)]
    exact mul_le_of_le_one_right hP hχU
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun t _ => (hD t).hasDerivWithinAt) hInj (nativeJointNegativeKernel p N)
  rw [hImg] at h
  exact h.mpr hI

end ACS12.NativeCells

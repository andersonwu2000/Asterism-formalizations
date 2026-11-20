import ACS12.JointDifferentiatedMellin
import ACS12.JointLaplaceRealDerivative

/-! The strip-normalized differentiated integral is exactly the actual real joint moment. -/
namespace ACS12.NativeCells
open MeasureTheory Set Filter
open scoped Topology
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem jointDifferentiatedMoment_differentiableAt {z : ℝ} {α : ℂ} (hz : 0 ≤ z) (hα : 0 < α.re)
    (k : ℕ) (hStrip : (jointDifferentiatedExponent α).re < (k:ℝ)) :
    DifferentiableAt ℂ (jointDifferentiatedMoment z k) α := by
  have hPos : 0 < ((k:ℂ)-jointDifferentiatedExponent α).re := by
    simp only [Complex.sub_re,Complex.natCast_re]
    linarith only [hStrip]
  have hAvoid (n : ℕ) : (k:ℂ)-jointDifferentiatedExponent α ≠ -(n:ℂ) := by
    intro h
    have hR := congrArg Complex.re h
    simp only [Complex.neg_re,Complex.natCast_re] at hR
    linarith only [hR,hPos,Nat.cast_nonneg (α:=ℝ) n]
  have hGamma := (Complex.differentiableAt_Gamma _ hAvoid).comp α
    (by unfold jointDifferentiatedExponent; fun_prop :
      DifferentiableAt ℂ (fun a => (k:ℂ)-jointDifferentiatedExponent a) α)
  exact ((differentiableAt_const ((-1:ℂ)^k)).div hGamma
    (Complex.Gamma_ne_zero_of_re_pos hPos)).mul
      (jointDifferentiatedIntegral_differentiableAt hz hα k hStrip)

theorem jointDifferentiatedMoment_analytic {z : ℝ} {α : ℂ} (hz : 0 ≤ z) (hα : 0 < α.re)
    (k : ℕ) (hStrip : (jointDifferentiatedExponent α).re < (k:ℝ)) :
    AnalyticAt ℂ (jointDifferentiatedMoment z k) α := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  have hOpen : IsOpen {a : ℂ | 0 < a.re ∧ (jointDifferentiatedExponent a).re < (k:ℝ)} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt (show Continuous (fun a : ℂ => (jointDifferentiatedExponent a).re) by unfold jointDifferentiatedExponent; fun_prop) continuous_const)
  filter_upwards [hOpen.mem_nhds ⟨hα,hStrip⟩] with a ha
  exact jointDifferentiatedMoment_differentiableAt hz ha.1 k ha.2

theorem jointDifferentiatedMoment_real {p z : ℝ} (hp : 0 < p) (hz : 0 ≤ z)
    (k : ℕ) (hβ : (p-2)/2 < (k:ℝ)) :
    jointDifferentiatedMoment z k (p:ℂ) =
      ((∫ ω, nativeJointEnergy z ω^((p-2)/2) ∂nativeJointMeasure p:ℝ):ℂ) := by
  let β := (p-2)/2
  have hMoment := jointDifferentiatedLaplace_moment hp hz k hβ
  have hPoint (t : ℝ) (ht : 0 < t) : jointDifferentiatedKernel z k (p:ℂ) t =
      (((-1:ℝ)^k*(t^((k:ℝ)-β-1)*
        (∫ ω, nativeJointEnergy z ω^k*Real.exp (-t*nativeJointEnergy z ω) ∂nativeJointMeasure p)):ℝ):ℂ) := by
    have hExp : (k:ℂ)-jointDifferentiatedExponent (p:ℂ)-1 = (((k:ℝ)-β-1:ℝ):ℂ) := by
      dsimp [jointDifferentiatedExponent,β]
      push_cast
      ring
    unfold jointDifferentiatedKernel
    rw [hExp,jointLaplaceCarrier_real_iteratedDeriv hp hz ht k,←Complex.ofReal_cpow ht.le]
    push_cast
    ring
  have hIntegral : jointDifferentiatedIntegral z k (p:ℂ) =
      (((-1:ℝ)^k*Real.Gamma ((k:ℝ)-β)*
        (∫ ω, nativeJointEnergy z ω^β ∂nativeJointMeasure p):ℝ):ℂ) := by
    unfold jointDifferentiatedIntegral
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => hPoint t ht),integral_complex_ofReal,
      integral_const_mul,hMoment.2]
    push_cast
    ring
  have hGamma : Complex.Gamma ((k:ℂ)-jointDifferentiatedExponent (p:ℂ)) =
      (Real.Gamma ((k:ℝ)-β):ℂ) := by
    have hExp : (k:ℂ)-jointDifferentiatedExponent (p:ℂ) = (((k:ℝ)-β:ℝ):ℂ) := by
      dsimp [jointDifferentiatedExponent,β]
      push_cast
      ring
    rw [hExp,Complex.Gamma_ofReal]
  have hΓ : Real.Gamma ((k:ℝ)-β) ≠ 0 := (Real.Gamma_pos_of_pos (sub_pos.mpr hβ)).ne'
  have hSign : (-1:ℂ)^k*(-1:ℂ)^k = 1 := by rw [←mul_pow]; norm_num
  unfold jointDifferentiatedMoment
  rw [hIntegral,hGamma]
  push_cast
  calc
    _ = ((-1:ℂ)^k*(-1:ℂ)^k)*((∫ ω, nativeJointEnergy z ω^β ∂nativeJointMeasure p:ℝ):ℂ) := by
      field_simp [hΓ]
      <;> ring
    _ = _ := by rw [hSign,one_mul]

end ACS12.NativeCells

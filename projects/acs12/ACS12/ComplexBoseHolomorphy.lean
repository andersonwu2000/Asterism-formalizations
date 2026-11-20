import ACS12.ComplexBoseEnvelope
import ACS12.ComplexBoseMeasurable
import ACS12.HolomorphicDominatedIntegral

/-! Ordinary-beta Gamma tails give holomorphy of the complete original Bose row on the positive-shape half-plane. -/
namespace ACS12.NativeCells
open Set MeasureTheory Metric Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

theorem complexBose_local_rectangle {α β : ℂ} (hα : 0 < α.re)
    (hβ : β ∈ closedBall α (α.re/2)) :
    β.re/2 ∈ Icc (α.re/4) (3*α.re/4) ∧
      |β.im/2| ≤ (|α.im|+α.re/2)/2 := by
  have hNorm : ‖β-α‖ ≤ α.re/2 := by simpa only [dist_eq_norm] using mem_closedBall.mp hβ
  have hr := (Complex.abs_re_le_norm (β-α)).trans hNorm
  have hi := (Complex.abs_im_le_norm (β-α)).trans hNorm
  rw [Complex.sub_re] at hr
  rw [Complex.sub_im] at hi
  obtain ⟨hr₁,hr₂⟩ := abs_le.mp hr
  obtain ⟨hi₁,hi₂⟩ := abs_le.mp hi
  constructor
  · constructor <;> linarith only [hr₁,hr₂]
  · apply abs_le.mpr
    constructor
    · linarith [neg_le_abs α.im]
    · linarith [le_abs_self α.im]

theorem complexBoseIntegral_differentiableAt {α : ℂ} {N : ℝ} (hα : 0 < α.re) (hN : 0 < N) :
    DifferentiableAt ℂ (fun a => ∫ ξ : ℝ in Ioi 0, complexBoseKernel N a ξ) α := by
  let T := (|α.im|+α.re/2)/2
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  obtain ⟨G,hG,hBound⟩ := complexBose_rect_uniform_envelope
    (a:=α.re/4) (b:=3*α.re/4) (T:=T) (by positivity) hT hN
  refine differentiableAt_integral_of_holomorphic_dominated (half_pos hα)
    (fun a => (measurable_complexBoseKernel N a).aestronglyMeasurable) hG ?_ ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ _
    intro a ha
    have hDom := (complexBose_local_rectangle hα ha).1.1
    have hPos : 0 < a.re := by linarith only [hDom,hα]
    exact complexBoseKernel_differentiableAt hPos N ξ
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
    intro a ha
    have hDom := complexBose_local_rectangle hα ha
    exact hBound a hDom.1 hDom.2 ξ hξ

theorem complexBoseRow_differentiableAt {α : ℂ} {N : ℝ} (hα : 0 < α.re) (hN : 0 < N) :
    DifferentiableAt ℂ (complexBoseRow N) α :=
  (complexBoseCoefficient_differentiableAt hα).mul (complexBoseIntegral_differentiableAt hα hN)

theorem complexBoseRow_analytic {α : ℂ} {N : ℝ} (hα : 0 < α.re) (hN : 0 < N) :
    AnalyticAt ℂ (complexBoseRow N) α := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hα] with a ha
  exact complexBoseRow_differentiableAt ha hN

end ACS12.NativeCells

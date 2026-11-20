import ACS12.ParameterDerivativeMeasurable
import Mathlib.Analysis.Complex.Liouville

/-! Local domination of a holomorphic family pays its integral by Cauchy's derivative estimate. -/
namespace ACS12
open MeasureTheory Filter Set Metric
open scoped Topology

theorem differentiableAt_integral_of_holomorphic_dominated {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {F : ℂ → Ω → ℂ} {x₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hM : ∀ x, AEStronglyMeasurable (F x) μ) {G : Ω → ℝ} (hG : Integrable G μ)
    (hHol : ∀ᵐ ω ∂μ, ∀ x ∈ closedBall x₀ R, DifferentiableAt ℂ (fun z => F z ω) x)
    (hBound : ∀ᵐ ω ∂μ, ∀ x ∈ closedBall x₀ R, ‖F x ω‖ ≤ G ω) :
    DifferentiableAt ℂ (fun x => ∫ ω, F x ω ∂μ) x₀ := by
  have hHalf : 0 < R/2 := half_pos hR
  have hCenter : x₀ ∈ closedBall x₀ R := mem_closedBall_self hR.le
  have hI : Integrable (F x₀) μ := hG.mono' (hM x₀) (hBound.mono fun ω h => h x₀ hCenter)
  have hD₀ : AEStronglyMeasurable (fun ω => deriv (fun z => F z ω) x₀) μ :=
    aestronglyMeasurable_parameter_deriv hM (hHol.mono fun ω h => h x₀ hCenter)
  have hContain (x : ℂ) (hx : x ∈ ball x₀ (R/2)) (y : ℂ) (hy : y ∈ closedBall x (R/2)) :
      y ∈ closedBall x₀ R := by
    have hxD := mem_ball.mp hx
    have hyD := mem_closedBall.mp hy
    apply mem_closedBall.mpr
    have h := dist_triangle y x x₀
    linarith only [h,hxD,hyD]
  have hSmall (x : ℂ) (hx : x ∈ ball x₀ (R/2)) : x ∈ closedBall x₀ R := by
    apply mem_closedBall.mpr
    have h := mem_ball.mp hx
    linarith only [h,hR]
  have hDerivBound : ∀ᵐ ω ∂μ, ∀ x ∈ ball x₀ (R/2),
      ‖deriv (fun z => F z ω) x‖ ≤ G ω/(R/2) := by
    filter_upwards [hHol,hBound] with ω hH hB
    intro x hx
    have hd : DiffContOnCl ℂ (fun z => F z ω) (ball x (R/2)) :=
      ⟨fun y hy => (hH y (hContain x hx y (ball_subset_closedBall hy))).differentiableWithinAt,
       fun y hy => (hH y (hContain x hx y (closure_ball_subset_closedBall hy))).continuousAt.continuousWithinAt⟩
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hHalf hd
      (fun y hy => hB y (hContain x hx y (sphere_subset_closedBall hy)))
  have hDiff : ∀ᵐ ω ∂μ, ∀ x ∈ ball x₀ (R/2),
      HasDerivAt (fun z => F z ω) (deriv (fun z => F z ω) x) x :=
    hHol.mono fun ω h x hx => (h x (hSmall x hx)).hasDerivAt
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds x₀ hHalf)
    (Eventually.of_forall hM) hI hD₀ hDerivBound (hG.div_const (R/2)) hDiff
  exact h.2.differentiableAt

end ACS12

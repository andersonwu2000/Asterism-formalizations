import CenteredCircle.CircleDensities

/-!
The manuscript's actual A/B Laplace kernels have all convergence and strict
sampling properties required by the half-source equality theorem. Their link
to C(t)-U(t+1) and U(t)-C(t), and saturation from the physical rows, are separate
obligations; neither is silently assumed here.
-/

namespace CenteredCircle.AllN

open MeasureTheory

noncomputable def circleKernel (L : ℝ) (kind : CircleKernelKind) : ℝ → ℝ :=
  laplaceKernel (densityMeasure (circleDensity L kind))

theorem circleMeasure_ne_zero {L : ℝ} (hL : 0 < L) (kind : CircleKernelKind) :
    densityMeasure (circleDensity L kind) ≠ 0 :=
  densityMeasure_ne_zero _ (continuous_circleDensity L kind).measurable
    (fun u hu => circleDensity_pos hL kind hu)

theorem circleKernel_integrable {L : ℝ} (hL : 0 < L) (kind : CircleKernelKind)
    (t : ℝ) (ht : 0 < t) :
    Integrable (fun u => Real.exp (-u * t)) (densityMeasure (circleDensity L kind)) :=
  integrable_exp_density _ (1 / 2) t (continuous_circleDensity L kind).measurable
    (fun u hu => (circleDensity_pos hL kind hu).le)
    (fun u hu => circleDensity_quadratic_bound kind hu) ht

theorem circleKernel_pos {L : ℝ} (hL : 0 < L) (kind : CircleKernelKind)
    (t : ℝ) (ht : 0 < t) : 0 < circleKernel L kind t := by
  letI : NeZero (densityMeasure (circleDensity L kind)) := ⟨circleMeasure_ne_zero hL kind⟩
  exact laplaceKernel_pos _ t (circleKernel_integrable hL kind t ht)

theorem circleKernel_le_cubic {L : ℝ} (hL : 0 < L) (kind : CircleKernelKind)
    (t : ℝ) (ht : 0 < t) : circleKernel L kind t ≤ 1 / t ^ 3 := by
  have h := laplace_density_cubic_bound (circleDensity L kind) (1 / 2) t
    (continuous_circleDensity L kind).measurable
    (fun u hu => (circleDensity_pos hL kind hu).le)
    (fun u hu => circleDensity_quadratic_bound kind hu) ht
  norm_num at h
  simpa only [circleKernel, one_div] using h

theorem circleKernel_summable {L : ℝ} (hL : 0 < L) (kind : CircleKernelKind)
    (t s : ℝ) (ht : 0 < t) (hs : 0 < s) :
    Summable (fun j : ℕ => circleKernel L kind (t + j * s)) :=
  summable_laplace_density _ (1 / 2) t s (continuous_circleDensity L kind).measurable
    (fun u hu => (circleDensity_pos hL kind hu).le)
    (fun u hu => circleDensity_quadratic_bound kind hu) (by norm_num) ht hs

theorem half_source_rigid_circle {L : ℝ} (hL : 0 < L) (kind : CircleKernelKind)
    (t s q : ℕ → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i)
    (hstart : 1 ≤ s 0) (hstart_eq : t 0 = s 0)
    (hnext : ∀ i, t (i + 1) = t i + s (i + 1))
    (hmass : ∀ i, q i ≤ min (s i) (s (i + 1)))
    (hsum : HasSum (fun i => q i * circleKernel L kind (t i))
      (samplingTail (circleKernel L kind) 0 1)) :
    ∀ i, s i = 1 ∧ t i = (i : ℝ) + 1 ∧ q i = 1 := by
  letI : NeZero (densityMeasure (circleDensity L kind)) := ⟨circleMeasure_ne_zero hL kind⟩
  exact half_source_rigid_laplace _ t s q
    (densityMeasure_positive_support _ (continuous_circleDensity L kind).measurable)
    (circleKernel_integrable hL kind) (circleKernel_summable hL kind)
    hs ht hstart hstart_eq hnext hmass hsum

end CenteredCircle.AllN

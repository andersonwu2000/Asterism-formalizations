import ACS12.FourthBound

/-! Differentiation of the original fourth source, with all periodic images. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open scoped Topology

theorem fourthSourceRow_variation {p L θ u v r m dv dr dm t : ℝ}
    (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hu : 0 < u) (hv : 0 < v + dv * t) (hr : 0 < r + dr * t) :
    let V := v + dv * t
    let R := r + dr * t
    let M := m + dm * t
    let F (s : ℝ) := lawDensity p L θ s *
      (dv * fourthV u V R M s - dr * fourthD V R s + dm * Real.exp (-s * V))
    IntegrableOn F (Ioi 0) ∧
      HasDerivAt (fun x => fourthSourceRow p L θ u (v + dv * x) (r + dr * x) (m + dm * x))
        ((∫ s : ℝ in Ioi 0, F s) + (dm - dr) * lawSelf p L θ) t := by
  let V (x : ℝ) := v + dv * x
  let R (x : ℝ) := r + dr * x
  let M (x : ℝ) := m + dm * x
  let c := min u (min (V t / 2) (R t / 2))
  let Vmax := 2 * V t
  let Rmax := 2 * R t
  let Mmax := |M t| + 1
  have hc : 0 < c := lt_min hu (lt_min (half_pos hv) (half_pos hr))
  have hcU : c ≤ u := min_le_left _ _
  have hcV : c ≤ V t / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hcR : c ≤ R t / 2 := (min_le_right _ _).trans (min_le_right _ _)
  let S := {x : ℝ | V x ∈ Ioo (V t / 2) Vmax ∧ R x ∈ Ioo (R t / 2) Rmax ∧ |M x| < Mmax}
  have hVM : ∀ᶠ x in 𝓝 t, V x ∈ Ioo (V t / 2) Vmax := by
    have hC : Continuous V := by unfold V; fun_prop
    exact hC.continuousAt.tendsto.eventually (Ioo_mem_nhds (by linarith [show 0 < V t from hv])
      (by dsimp only [Vmax]; linarith [show 0 < V t from hv]))
  have hRM : ∀ᶠ x in 𝓝 t, R x ∈ Ioo (R t / 2) Rmax := by
    have hC : Continuous R := by unfold R; fun_prop
    exact hC.continuousAt.tendsto.eventually (Ioo_mem_nhds (by linarith [show 0 < R t from hr])
      (by dsimp only [Rmax]; linarith [show 0 < R t from hr]))
  have hMM : ∀ᶠ x in 𝓝 t, |M x| < Mmax := by
    have hC : Continuous (fun x => |M x|) := by unfold M; fun_prop
    exact hC.continuousAt.tendsto.eventually (Iio_mem_nhds (by dsimp only [Mmax]; linarith))
  have hS : S ∈ 𝓝 t := hVM.and (hRM.and hMM)
  let w := lawDensity p L θ
  let F (x s : ℝ) := w s * fourthDensity u (V x) (R x) (M x) s
  let F' (x s : ℝ) := w s * (dv * fourthV u (V x) (R x) (M x) s -
    dr * fourthD (V x) (R x) s + dm * Real.exp (-s * V x))
  let μ := volume.restrict (Ioi (0 : ℝ))
  obtain ⟨B, hB, hWB⟩ := lawDensity_linear_envelope hp hp₂ hL hθ
  let D := |dv| * (u + 1 + (Vmax * (1 + Rmax) + Mmax)) +
    |dr| * (1 + Vmax + BoseShape.decayConstant * (Rmax + 1)) + |dm|
  let g (s : ℝ) := B * D * (1 + s) * (1 + s + s ^ 2) * Real.exp (-s * c)
  have hw := lawDensity_measurable (θ := θ) (zero_lt_one.trans_le hp) hL
  have hMeas : ∀ᶠ x in 𝓝 t, AEStronglyMeasurable (F x) μ := by
    exact Eventually.of_forall fun x => (hw.mul (by
      unfold fourthDensity fourthFirstStream polyA polyB scaledExpTail
      fun_prop)).aestronglyMeasurable
  have hMeas' : AEStronglyMeasurable (F' t) μ := by
    refine (hw.mul ?_).aestronglyMeasurable
    unfold fourthV fourthD fourthFirstStream polyA BoseShape.C expHeadFactor scaledExpTail
    fun_prop
  have hF : Integrable (F t) μ := (fourthSourceRow_integral hp hp₂ hL hθ hu hv hr).1
  have hDom : ∀ᵐ s : ℝ ∂μ, ∀ x ∈ S, ‖F' x s‖ ≤ g s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    intro x hx
    have hs₀ : 0 < s := hs
    have hvx : 0 < V x := (half_pos hv).trans hx.1.1
    have hrx : 0 < R x := (half_pos hr).trans hx.2.1.1
    have h := fourth_direction_bound (dv := dv) (dr := dr) (dm := dm) hu hvx hrx hs₀ hcU
      (hcV.trans hx.1.1.le) (hcR.trans hx.2.1.1.le) hx.1.2.le hx.2.1.2.le hx.2.2.le
    have hB' : 0 ≤ B * (1 + s) := by positivity
    rw [Real.norm_eq_abs]
    change |w s * (dv * fourthV u (V x) (R x) (M x) s -
      dr * fourthD (V x) (R x) s + dm * Real.exp (-s * V x))| ≤ g s
    rw [abs_mul]
    refine (mul_le_mul (hWB s hs₀) h (abs_nonneg _) hB').trans_eq ?_
    dsimp only [g, D]
    ring
  have hPoint : ∀ᵐ s : ℝ ∂μ, ∀ x ∈ S, HasDerivAt (fun x => F x s) (F' x s) x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    intro x hx
    have hrx : 0 < R x := (half_pos hr).trans hx.2.1.1
    exact (fourthDensity_hasDerivAt (u := u) (v := v) (m := m) (dv := dv) (dm := dm)
      (mem_Ioi.mp hs) hrx).const_mul (w s)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) hS hMeas hF hMeas' hDom
    (integrable_cubic_exp_envelope hc (B * D)) hPoint
  have hM' : HasDerivAt M dm t := by
    simpa only [M, id_eq, mul_one] using ((hasDerivAt_id t).const_mul dm).const_add m
  have hR' : HasDerivAt R dr t := by
    simpa only [R, id_eq, mul_one] using ((hasDerivAt_id t).const_mul dr).const_add r
  refine ⟨h.1, ?_⟩
  apply (h.2.add ((hM'.sub hR').mul_const (lawSelf p L θ))).congr_of_eventuallyEq
  filter_upwards [hS] with x hx
  exact (fourthSourceRow_integral hp hp₂ hL hθ hu ((half_pos hv).trans hx.1.1)
    ((half_pos hr).trans hx.2.1.1)).2

end ACS12.GammaMeasure


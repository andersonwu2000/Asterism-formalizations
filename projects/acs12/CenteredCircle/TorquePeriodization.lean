import CenteredCircle.SelfImages

/-!
The torque image identity, obtained by differentiating the one-sided Laplace
integral. Every image series is absolutely summable; no derivative of an
unevaluated infinite series is assumed.
-/

namespace CenteredCircle.AllN

open MeasureTheory Filter Set
open scoped BigOperators Topology

noncomputable def radialImageTail (L t : ℝ) : ℝ :=
  ∫ u : ℝ in Ioi 0, Real.exp (-u * t) / (1 + Real.exp (-u * L))

noncomputable def torqueImageTail (L t : ℝ) : ℝ :=
  ∫ u : ℝ in Ioi 0, u * Real.exp (-u * t) / (1 + Real.exp (-u * L))

theorem radialImageTail_eq_tsum {L t : ℝ} (hL : 0 < L) (ht : 0 < t) :
    radialImageTail L t = ∑' j : ℕ, radialKernel L (t + j * L) :=
  (radial_sample_tsum_integral hL t ht).symm

theorem torqueImageTail_eq_tsum {L t : ℝ} (hL : 0 < L) (ht : 0 < t) :
    torqueImageTail L t = ∑' j : ℕ, torqueKernel L (t + j * L) := by
  have hi : ∀ j : ℕ, IntegrableOn
      (fun u => (u * circleWeight L u) * Real.exp (-u * (t + j * L))) (Ioi 0) := by
    intro j
    exact torqueKernel_integrable hL _ (by positivity)
  have hn (j : ℕ) : (∫ u : ℝ in Ioi 0,
      ‖(u * circleWeight L u) * Real.exp (-u * (t + j * L))‖) =
      torqueKernel L (t + j * L) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact Real.norm_of_nonneg
      (mul_pos (mul_pos hu (circleWeight_pos hL hu)) (Real.exp_pos _)).le
  have hns : Summable (fun j : ℕ => ∫ u : ℝ in Ioi 0,
      ‖(u * circleWeight L u) * Real.exp (-u * (t + j * L))‖) := by
    simp_rw [hn]
    exact summable_torqueKernel hL t L ht hL
  have hswap := integral_tsum_of_summable_integral_norm hi hns
  change (∫ u : ℝ in Ioi 0, u * Real.exp (-u * t) / (1 + Real.exp (-u * L))) =
    ∑' j : ℕ, ∫ u : ℝ in Ioi 0, (u * circleWeight L u) * Real.exp (-u * (t + j * L))
  rw [hswap]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  dsimp only
  rw [tsum_mul_left, (exponential_samples_hasSum u t L hu hL).tsum_eq,
    circleWeight_exp_ratio]
  have hd : 1 - Real.exp (-u * L) ≠ 0 :=
    ne_of_gt (by simpa only [neg_mul] using expHead_den_pos (mul_pos hu hL))
  field_simp
  rw [mul_div_assoc, div_self (by simpa only [neg_mul] using hd), mul_one]

theorem hasDerivAt_radialImageTail (L : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (radialImageTail L) (-torqueImageTail L t) t := by
  let g : ℝ → ℝ := fun u => (1 + Real.exp (-u * L))⁻¹
  have hg : Measurable g := by dsimp [g]; fun_prop
  have hb : ∀ u, 0 < u → |g u| ≤ (1 : ℝ) * u ^ 0 := by
    intro u _
    have hpos : 0 < 1 + Real.exp (-u * L) := by positivity
    dsimp [g]
    rw [abs_of_pos (inv_pos.mpr hpos), pow_zero, mul_one]
    exact inv_le_one_of_one_le₀ (by have h := Real.exp_pos (-u * L); linarith)
  have h := hasDerivAt_weighted_laplace g 1 0 hg (by norm_num) hb ht
  have heq : (fun x => ∫ u : ℝ in Ioi 0, g u * Real.exp (-u * x)) = radialImageTail L := by
    funext x
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    dsimp [g, radialImageTail]
    ring
  have hval : (∫ u : ℝ in Ioi 0, (u * g u) * Real.exp (-u * t)) = torqueImageTail L t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    dsimp [g, torqueImageTail]
    ring
  rw [heq, hval] at h
  exact h

noncomputable def periodicRadialKernel (L t : ℝ) : ℝ :=
  (Real.pi / L) / Real.sin (Real.pi * t / L)

theorem periodicRadialKernel_eq_tails {L t : ℝ} (hL : 0 < L)
    (ht : 0 < t) (htL : t < L) :
    periodicRadialKernel L t = radialImageTail L t + radialImageTail L (L - t) := by
  rw [periodicRadialKernel, ← periodization_integral_eval hL ht htL]
  unfold radialImageTail
  rw [← integral_add (integrable_radial_sample_integrand hL t ht)
    (integrable_radial_sample_integrand hL (L - t) (sub_pos.mpr htL))]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  exact add_div _ _ _

theorem hasDerivAt_periodicRadialKernel {L t : ℝ} (hL : 0 < L)
    (ht : 0 < t) (htL : t < L) :
    HasDerivAt (periodicRadialKernel L)
      (-torqueImageTail L t + torqueImageTail L (L - t)) t := by
  have hd := (hasDerivAt_radialImageTail L ht).add
    ((hasDerivAt_radialImageTail L (sub_pos.mpr htL)).comp t
      ((hasDerivAt_id t).const_sub L))
  have he : (fun x => radialImageTail L x + radialImageTail L (L - x)) =ᶠ[𝓝 t]
      periodicRadialKernel L := by
    filter_upwards [Ioi_mem_nhds ht, Iio_mem_nhds htL] with x hx0 hxL
    exact (periodicRadialKernel_eq_tails hL hx0 hxL).symm
  have h := hd.congr_of_eventuallyEq he.symm
  convert h using 1 <;> ring

theorem periodicRadialKernel_deriv_torque {L t : ℝ} (hL : 0 < L)
    (ht : 0 < t) (htL : t < L) :
    deriv (periodicRadialKernel L) t =
      -(∑' j : ℕ, torqueKernel L (t + j * L)) +
        ∑' j : ℕ, torqueKernel L ((L - t) + j * L) := by
  rw [(hasDerivAt_periodicRadialKernel hL ht htL).deriv,
    torqueImageTail_eq_tsum hL ht, torqueImageTail_eq_tsum hL (sub_pos.mpr htL)]

end CenteredCircle.AllN

import ACS12.GammaPeriodization

/-! The signed derivative of the image row and the physical torque. -/

namespace ACS12.GammaMeasure

open MeasureTheory Set Filter
open scoped Topology

noncomputable def imageSlope (p L t : ℝ) : ℝ :=
  ∫ s : ℝ in Ioi 0, imageDensity p L s * s * Real.exp (-s * t)

private theorem weighted_exp_le {s d x : ℝ} (hs : 0 < s) (hd : 0 < d) (hx : 2 * d ≤ x) :
    s * Real.exp (-s * x) ≤ d⁻¹ * Real.exp (-s * d) := by
  have hs' : s ≤ d⁻¹ * Real.exp (s * d) := by
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ hd).mpr (by linarith [Real.add_one_le_exp (s * d)])
  calc
    _ ≤ (d⁻¹ * Real.exp (s * d)) * Real.exp (-s * x) :=
      mul_le_mul_of_nonneg_right hs' (Real.exp_pos _).le
    _ = d⁻¹ * Real.exp (s * d + -s * x) := by rw [mul_assoc, ← Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (inv_nonneg.mpr hd.le)

theorem imageSlope_integrable {p L t : ℝ} (hp : 0 < p) (hL : 0 < L) (ht : 0 < t) :
    IntegrableOn (fun s : ℝ => imageDensity p L s * s * Real.exp (-s * t)) (Ioi 0) := by
  have hd : 0 < t / 2 := by positivity
  refine ((imagePotential_integrable hp hL hd).const_mul (t / 2)⁻¹).mono' ?_ ?_
  · exact (((continuous_imageDensity hp hL).mul continuous_id).mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hw := (imageDensity_pos hp hL hs).le
    change 0 < s at hs
    rw [Real.norm_of_nonneg (by positivity), mul_assoc,
      mul_left_comm ((t / 2)⁻¹) (imageDensity p L s)]
    exact mul_le_mul_of_nonneg_left (weighted_exp_le hs hd (by linarith)) hw

noncomputable def imageSlopeIntegrand (p L t s : ℝ) : ℝ :=
  imageDensity p L s * s *
    ((Real.exp (-s * t) - Real.exp (-s * (L - t))) / (1 - Real.exp (-s * L)))

private theorem hasDerivAt_imageRowIntegrand (p L s x : ℝ) :
    HasDerivAt (fun t => imageRowIntegrand p L t s) (-imageSlopeIntegrand p L x s) x := by
  have h₁ := ((hasDerivAt_id x).const_mul (-s)).exp
  have h₂ := (((hasDerivAt_const x L).sub (hasDerivAt_id x)).const_mul (-s)).exp
  have h := (((h₁.add h₂).div_const (1 - Real.exp (-s * L))).const_mul (imageDensity p L s))
  convert h using 1
  dsimp [imageSlopeIntegrand]
  ring

private theorem norm_imageSlopeIntegrand_le {p L s d x : ℝ} (hp : 0 < p) (hL : 0 < L) (hs : 0 < s)
    (hd : 0 < d) (hx : 2 * d ≤ x) (hx' : 2 * d ≤ L - x) :
    ‖imageSlopeIntegrand p L x s‖ ≤ (2 * d⁻¹) * imageRowIntegrand p L d s := by
  let w := imageDensity p L s
  let B := 1 - Real.exp (-s * L)
  have hw : 0 ≤ w := (imageDensity_pos hp hL hs).le
  have hB : 0 < B := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))
  change ‖w * s * ((Real.exp (-s * x) - Real.exp (-s * (L - x))) / B)‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg hw hs.le), abs_div, abs_of_pos hB]
  calc
    _ = (w / B) * (s * |Real.exp (-s * x) - Real.exp (-s * (L - x))|) := by ring
    _ ≤ (w / B) * (s * (Real.exp (-s * x) + Real.exp (-s * (L - x)))) := by
      gcongr
      apply abs_le.mpr
      constructor <;> linarith [Real.exp_pos (-s * x), Real.exp_pos (-s * (L - x))]
    _ = (w / B) * (s * Real.exp (-s * x) + s * Real.exp (-s * (L - x))) := by rw [mul_add]
    _ ≤ (w / B) * (2 * (d⁻¹ * Real.exp (-s * d))) := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hw hB.le)
      linarith [weighted_exp_le hs hd hx, weighted_exp_le hs hd hx']
    _ ≤ _ := by
      change _ ≤ 2 * d⁻¹ * (w * ((Real.exp (-s * d) + Real.exp (-s * (L - d))) / B))
      rw [show (w / B) * (2 * (d⁻¹ * Real.exp (-s * d))) =
        2 * d⁻¹ * (w * (Real.exp (-s * d) / B)) by ring]
      gcongr
      exact le_add_of_nonneg_right (Real.exp_pos _).le

private theorem continuous_imageRowIntegrand {p L : ℝ} (hp : 0 < p) (hL : 0 < L)
    (x : ℝ) :
    AEStronglyMeasurable (imageRowIntegrand p L x) (volume.restrict (Ioi 0)) := by
  unfold imageRowIntegrand
  exact ((continuous_imageDensity hp hL).measurable.mul
    ((by fun_prop : Measurable (fun s : ℝ => Real.exp (-s * x) + Real.exp (-s * (L - x)))).div
      (by fun_prop))).aestronglyMeasurable

private theorem measurable_imageSlopeIntegrand {p L : ℝ} (hp : 0 < p) (hL : 0 < L) (x : ℝ) :
    Measurable (imageSlopeIntegrand p L x) := by
  unfold imageSlopeIntegrand
  exact ((continuous_imageDensity hp hL).measurable.mul measurable_id).mul
    ((by fun_prop : Measurable (fun s : ℝ => Real.exp (-s * x) - Real.exp (-s * (L - x)))).div
      (by fun_prop))

private theorem hasDerivAt_imageRowIntegral {p L t : ℝ} (hp : 0 < p) (hL : 0 < L)
    (ht : 0 < t) (htL : t < L) :
    HasDerivAt (fun x => ∫ s : ℝ in Ioi 0, imageRowIntegrand p L x s)
      (-(∫ s : ℝ in Ioi 0, imageSlopeIntegrand p L t s)) t := by
  let d := min t (L - t) / 4
  have hd : 0 < d := div_pos (lt_min ht (sub_pos.mpr htL)) (by norm_num)
  have hd₁ : 4 * d ≤ t := by dsimp [d]; linarith [min_le_left t (L - t)]
  have hd₂ : 4 * d ≤ L - t := by dsimp [d]; linarith [min_le_right t (L - t)]
  have hdL : d < L := by linarith
  have hn : Ioo (2 * d) (L - 2 * d) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hbound : ∀ᵐ s : ℝ ∂volume.restrict (Ioi 0), ∀ x ∈ Ioo (2 * d) (L - 2 * d),
      ‖-imageSlopeIntegrand p L x s‖ ≤ (2 * d⁻¹) * imageRowIntegrand p L d s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    intro x hx
    rw [norm_neg]
    exact norm_imageSlopeIntegrand_le hp hL hs hd hx.1.le (by linarith [hx.2])
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ))) hn
    (Eventually.of_forall fun x => continuous_imageRowIntegrand hp hL x)
    (imageRowIntegrable hp hL ht htL)
    ((measurable_imageSlopeIntegrand hp hL t).neg.aestronglyMeasurable)
    hbound ((imageRowIntegrable hp hL hd hdL).const_mul (2 * d⁻¹))
    (Eventually.of_forall fun s x _ => hasDerivAt_imageRowIntegrand p L s x)
  simpa only [integral_neg] using h.2

/-- The signed image integral is exactly the physical torque, with the
scale of the original radial derivative. -/
theorem imageSlopeIntegral {p L t : ℝ} (hp : 0 < p) (hL : 0 < L)
    (ht : 0 < t) (htL : t < L) :
    (∫ s : ℝ in Ioi 0, imageSlopeIntegrand p L t s) =
      p * (Real.pi / L) ^ (p + 1) * circleTorque p L t := by
  have heq : circlePower p L =ᶠ[𝓝 t]
      (fun x => ∫ s : ℝ in Ioi 0, imageRowIntegrand p L x s) := by
    filter_upwards [Ioo_mem_nhds ht htL] with x hx
    exact (imageRowIntegral hp hL hx.1 hx.2).symm
  have h₁ := (hasDerivAt_imageRowIntegral hp hL ht htL).congr_of_eventuallyEq heq
  have h₂ := hasDerivAt_circlePower p hL ht htL
  have h := h₁.unique h₂
  linarith

theorem imageSlopeTail_integrable {p L t : ℝ} (hp : 0 < p) (hL : 0 < L) (ht : 0 < t) :
    IntegrableOn (fun s : ℝ => imageDensity p L s * s *
      (Real.exp (-s * t) / (1 - Real.exp (-s * L)))) (Ioi 0) := by
  let d := min (t / 2) (L / 2)
  have hd : 0 < d := lt_min (by positivity) (by positivity)
  have hdL : d < L := (min_le_right _ _).trans_lt (by linarith)
  have hdt : 2 * d ≤ t := by dsimp [d]; linarith [min_le_left (t / 2) (L / 2)]
  refine ((imageRowIntegrable hp hL hd hdL).const_mul d⁻¹).mono' ?_ ?_
  · exact (((continuous_imageDensity hp hL).measurable.mul measurable_id).mul
      ((by fun_prop : Measurable (fun s : ℝ => Real.exp (-s * t))).div
        (by fun_prop))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    change 0 < s at hs
    let w := imageDensity p L s
    let B := 1 - Real.exp (-s * L)
    have hw : 0 ≤ w := (imageDensity_pos hp hL hs).le
    have hB : 0 < B := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))
    change ‖w * s * (Real.exp (-s * t) / B)‖ ≤ d⁻¹ *
      (w * ((Real.exp (-s * d) + Real.exp (-s * (L - d))) / B))
    rw [Real.norm_of_nonneg (by positivity)]
    calc
      _ = (w / B) * (s * Real.exp (-s * t)) := by ring
      _ ≤ (w / B) * (d⁻¹ * Real.exp (-s * d)) :=
        mul_le_mul_of_nonneg_left (weighted_exp_le hs hd hdt) (div_nonneg hw hB.le)
      _ = d⁻¹ * (w * (Real.exp (-s * d) / B)) := by ring
      _ ≤ _ := by
        gcongr
        exact le_add_of_nonneg_right (Real.exp_pos _).le

theorem imageSlope_samples_hasSum {p L t : ℝ} (hp : 0 < p) (hL : 0 < L) (ht : 0 < t) :
    HasSum (fun j : ℕ => imageSlope p L (t + (j : ℝ) * L))
      (∫ s : ℝ in Ioi 0, imageDensity p L s * s *
        (Real.exp (-s * t) / (1 - Real.exp (-s * L)))) := by
  exact hasSum_laplace_samples (fun s => imageDensity p L s * s)
    ((continuous_imageDensity hp hL).measurable.mul measurable_id)
    (fun s hs => mul_nonneg (imageDensity_pos hp hL hs).le hs.le)
    hL (imageSlopeTail_integrable hp hL ht)

theorem imageSlope_pair {p L t : ℝ} (hp : 0 < p) (hL : 0 < L)
    (ht : 0 < t) (htL : t < L) :
    CenteredCircle.AllN.imageTail (imageSlope p L) L t -
      CenteredCircle.AllN.imageTail (imageSlope p L) L (L - t) =
        p * (Real.pi / L) ^ (p + 1) * circleTorque p L t := by
  rw [CenteredCircle.AllN.imageTail, CenteredCircle.AllN.imageTail,
    (imageSlope_samples_hasSum hp hL ht).tsum_eq,
    (imageSlope_samples_hasSum hp hL (sub_pos.mpr htL)).tsum_eq,
    ← integral_sub (imageSlopeTail_integrable hp hL ht)
      (imageSlopeTail_integrable hp hL (sub_pos.mpr htL)),
    ← imageSlopeIntegral hp hL ht htL]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s _
  unfold imageSlopeIntegrand
  ring

end ACS12.GammaMeasure

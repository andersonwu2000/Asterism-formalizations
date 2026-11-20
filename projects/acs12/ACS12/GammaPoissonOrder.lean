import ACS12.GammaEvenPoisson

/-! The even Poisson extension preserves decrease on the positive half-line. -/

namespace ACS12.GammaMeasure

open MeasureTheory Set Filter

private theorem evenGammaBoundary_even : Function.Even evenGammaBoundary := by
  intro x
  rw [evenGammaBoundary_eq, evenGammaBoundary_eq, mul_neg, Real.cosh_neg]

private theorem evenGammaBoundary_nonneg (x : ℝ) : 0 ≤ evenGammaBoundary x := by
  rw [evenGammaBoundary_eq]
  positivity

private theorem evenGammaBoundary_bounded (x : ℝ) : evenGammaBoundary x ≤ Real.pi ^ 2 := by
  rw [evenGammaBoundary_eq]
  apply div_le_self (sq_nonneg _)
  exact one_le_pow₀ (Real.one_le_cosh _)

private theorem evenGammaBoundary_antitone : AntitoneOn evenGammaBoundary (Ici 0) := by
  intro x hx y hy hxy
  rw [evenGammaBoundary_eq, evenGammaBoundary_eq]
  apply div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos (Real.cosh_pos _))
  apply pow_le_pow_left₀ (Real.cosh_pos _).le _ 2
  exact Real.cosh_strictMonoOn.monotoneOn (mul_nonneg Real.pi_pos.le hx)
    (mul_nonneg Real.pi_pos.le hy) (mul_le_mul_of_nonneg_left hxy Real.pi_pos.le)

private theorem evenGammaBoundary_abs_le {x y : ℝ} (h : |x| ≤ |y|) :
    evenGammaBoundary y ≤ evenGammaBoundary x := by
  have hE (t : ℝ) : evenGammaBoundary |t| = evenGammaBoundary t := by
    by_cases ht : 0 ≤ t
    · rw [abs_of_nonneg ht]
    · rw [abs_of_neg (lt_of_not_ge ht), evenGammaBoundary_even]
  rw [← hE x, ← hE y]
  exact evenGammaBoundary_antitone (mem_Ici.mpr (abs_nonneg x)) (mem_Ici.mpr (abs_nonneg y)) h

private theorem kernel_abs_le {a : ℝ} (ha : 0 < a) {x y : ℝ} (h : |x| ≤ |y|) :
    Poisson.kernel a y ≤ Poisson.kernel a x := by
  unfold Poisson.kernel
  apply div_le_div_of_nonneg_left ha.le (by positivity)
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl ((sq_le_sq).mpr h)) Real.pi_pos.le

private theorem kernel_even (a : ℝ) : Function.Even (Poisson.kernel a) := by
  intro x
  simp only [Poisson.kernel, neg_sq]

private theorem subLeft_embedding (x : ℝ) : MeasurableEmbedding (fun y : ℝ => x - y) := by
  let e : ℝ ≃ₜ ℝ := {
    toFun := fun y => x - y
    invFun := fun y => x - y
    left_inv := by intro y; ring
    right_inv := by intro y; ring
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop
  }
  exact e.isClosedEmbedding.measurableEmbedding

private theorem smoothedEvenGamma_flip (a x : ℝ) :
    smoothedEvenGamma a x = ∫ y : ℝ, Poisson.kernel a (x - y) * evenGammaBoundary y := by
  have h := ((volume : Measure ℝ).measurePreserving_sub_left x).integral_comp
    (subLeft_embedding x) (fun y : ℝ => Poisson.kernel a y * evenGammaBoundary (x - y))
  simpa only [sub_sub_cancel, smoothedEvenGamma] using h.symm

private theorem kernel_mul_boundary_integrable {a : ℝ} (ha : 0 < a) (x : ℝ) :
    Integrable (fun y : ℝ => Poisson.kernel a (x - y) * evenGammaBoundary y) := by
  have h := ((volume : Measure ℝ).measurePreserving_sub_left x).integrable_comp_of_integrable
    (Poisson.integrable_kernel ha)
  refine (h.mul_const (Real.pi ^ 2)).mono' ?_ ?_
  · simp only [evenGammaBoundary_eq, Poisson.kernel]
    exact (by fun_prop : Measurable _).aestronglyMeasurable
  · exact Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (mul_nonneg (Poisson.kernel_pos ha _).le (evenGammaBoundary_nonneg _))]
      exact mul_le_mul_of_nonneg_left (evenGammaBoundary_bounded _) (Poisson.kernel_pos ha _).le

theorem smoothedEvenGamma_antitone {a : ℝ} (ha : 0 < a) :
    AntitoneOn (smoothedEvenGamma a) (Ici 0) := by
  intro x hx y hy hxy
  let D (t : ℝ) := Poisson.kernel a (x - t) - Poisson.kernel a (y - t)
  let f (t : ℝ) := D t * evenGammaBoundary t
  have hI : Integrable f := by
    simpa only [f, D, sub_mul] using (kernel_mul_boundary_integrable ha x).sub
      (kernel_mul_boundary_integrable ha y)
  have hreflect (t : ℝ) : D (x + y - t) = -D t := by
    dsimp only [D]
    rw [show x - (x + y - t) = -(y - t) by ring, show y - (x + y - t) = -(x - t) by ring,
      kernel_even, kernel_even]
    ring
  have hsign (t : ℝ) : 0 ≤ f t + f (x + y - t) := by
    change 0 ≤ D t * evenGammaBoundary t + D (x + y - t) * evenGammaBoundary (x + y - t)
    rw [hreflect, neg_mul, ← sub_eq_add_neg, ← mul_sub]
    have hsum : 0 ≤ x + y := add_nonneg hx hy
    by_cases ht : t ≤ (x + y) / 2
    · have hdist : |x - t| ≤ |y - t| := by
        apply (sq_le_sq).mp
        nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (show 0 ≤ x + y - 2 * t by linarith)]
      have hr : |t| ≤ |x + y - t| := by
        apply (sq_le_sq).mp
        nlinarith [mul_nonneg hsum (show 0 ≤ x + y - 2 * t by linarith)]
      exact mul_nonneg (sub_nonneg.mpr (kernel_abs_le ha hdist))
        (sub_nonneg.mpr (evenGammaBoundary_abs_le hr))
    · have hdist : |y - t| ≤ |x - t| := by
        apply (sq_le_sq).mp
        nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (show 0 ≤ 2 * t - (x + y) by linarith)]
      have hr : |x + y - t| ≤ |t| := by
        apply (sq_le_sq).mp
        nlinarith [mul_nonneg hsum (show 0 ≤ 2 * t - (x + y) by linarith)]
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (kernel_abs_le ha hdist))
        (sub_nonpos.mpr (evenGammaBoundary_abs_le hr))
  let r (t : ℝ) := x + y - t
  have hp : MeasurePreserving r volume volume := (volume : Measure ℝ).measurePreserving_sub_left _
  have hIr : Integrable (f ∘ r) := hp.integrable_comp_of_integrable hI
  have hInt : (∫ t : ℝ, f (r t)) = ∫ t : ℝ, f t :=
    hp.integral_comp (subLeft_embedding _) f
  have h : 0 ≤ ∫ t : ℝ, f t + f (r t) :=
    integral_nonneg (f := fun t : ℝ => f t + f (r t)) hsign
  have hadd : (∫ t : ℝ, f t + f (r t)) = (∫ t : ℝ, f t) + ∫ t : ℝ, f (r t) :=
    integral_add hI hIr
  rw [hadd, hInt] at h
  have hD : (∫ t : ℝ, f t) = smoothedEvenGamma a x - smoothedEvenGamma a y := by
    simpa only [f, D, sub_mul, smoothedEvenGamma_flip] using
      integral_sub (kernel_mul_boundary_integrable ha x) (kernel_mul_boundary_integrable ha y)
  rw [hD] at h
  linarith

end ACS12.GammaMeasure

import ACS12.JointHeatCurvature
import ACS12.BosePath

/-! Twice differentiating the complete Bose stream in its mass argument. -/
namespace ACS12.GammaMeasure

open Set MeasureTheory Filter CenteredCircle.AllN
open scoped Topology

private theorem boseCurvature_decay {x : ℝ} (hx : 0 < x) :
    -BoseShape.C₁ x ≤ BoseShape.curvatureHeat 1 * (x + 1) ^ 2 * Real.exp (-x) := by
  let K := BoseShape.curvatureHeat 1
  have hK : 0 < K := BoseShape.curvatureHeat_pos zero_lt_one
  have hE : Real.exp (-x) * BoseShape.curvatureHeat x = -BoseShape.C₁ x := by
    rw [BoseShape.curvatureHeat,← mul_assoc,← Real.exp_add,neg_add_cancel,Real.exp_zero,one_mul]
  rw [← hE,mul_comm (Real.exp (-x))]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  rcases le_total x 1 with hx₁ | hx₁
  · have hM := BoseShape.curvatureHeat_mono hx (mem_Ioi.mpr zero_lt_one) hx₁
    exact hM.trans (le_mul_of_one_le_right hK.le (one_le_pow₀ (by linarith only [hx])))
  · have h := BoseShape.curvatureHeat_div_sq_anti (mem_Ioi.mpr zero_lt_one) hx hx₁
    change BoseShape.curvatureHeat x / x ^ 2 ≤ K / (1 : ℝ) ^ 2 at h
    simp only [one_pow,div_one] at h
    exact ((div_le_iff₀ (sq_pos_of_pos hx)).mp h).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.le (by linarith) 2) hK.le)

theorem boseStream_second {g : ℝ → ℝ} {B r : ℝ} (hg : Measurable g)
    (hB : ∀ s > 0, |g s| ≤ B * (s + s ^ 2)) (hr : 0 < r) :
    IntegrableOn (fun s => g s * (s * (-BoseShape.C₁ (s * r)))) (Ioi 0) ∧
      HasDerivAt (fun t => -(∫ s : ℝ in Ioi 0, g s * BoseShape.C (s * t)))
        (∫ s : ℝ in Ioi 0, g s * (s * (-BoseShape.C₁ (s * r)))) r := by
  let c := r / 2
  let μ := volume.restrict (Ioi (0 : ℝ))
  let f (t s : ℝ) := -(g s * BoseShape.C (s * t))
  let f' (t s : ℝ) := g s * (s * (-BoseShape.C₁ (s * t)))
  let K := B * BoseShape.curvatureHeat 1 * (c + 1) ^ 2
  let M (s : ℝ) := K * (s ^ 2 * Real.exp (-s * c) + 3 * (s ^ 3 * Real.exp (-s * c)) +
    3 * (s ^ 4 * Real.exp (-s * c)) + s ^ 5 * Real.exp (-s * c))
  have hc : 0 < c := half_pos hr
  have hcr : c < r := by unfold c; linarith only [hr]
  have hB₀ : 0 ≤ B := by
    have h := (abs_nonneg _).trans (hB 1 zero_lt_one)
    norm_num at h
    linarith only [h]
  have hK : 0 ≤ BoseShape.curvatureHeat 1 := (BoseShape.curvatureHeat_pos zero_lt_one).le
  have hF : ∀ᶠ t in 𝓝 r, AEStronglyMeasurable (f t) μ := Eventually.of_forall fun t =>
    (hg.mul (by unfold BoseShape.C; fun_prop)).neg.aestronglyMeasurable
  have hF' : AEStronglyMeasurable (f' r) μ :=
    (hg.mul (measurable_id.mul (BoseShape.C₁_measurable.comp (by fun_prop)).neg)).aestronglyMeasurable
  have hM : Integrable M μ :=
    ((((expMoment_nat_integrable 2 hc).add ((expMoment_nat_integrable 3 hc).const_mul 3)).add
      ((expMoment_nat_integrable 4 hc).const_mul 3)).add (expMoment_nat_integrable 5 hc)).const_mul K
  have hDom : ∀ᵐ s ∂μ, ∀ t ∈ Ioi c, ‖f' t s‖ ≤ M s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    intro t ht
    have hs₀ : 0 < s := hs
    have ht₀ := hc.trans (mem_Ioi.mp ht)
    have hU := (neg_le_neg (BoseShape.C₁_mono (mul_pos hs₀ hc) (mul_pos hs₀ ht₀)
      (mul_le_mul_of_nonneg_left (mem_Ioi.mp ht).le hs₀.le))).trans (boseCurvature_decay (mul_pos hs₀ hc))
    rw [← neg_mul] at hU
    have hP : s * c + 1 ≤ (c + 1) * (s + 1) := by nlinarith only [hs₀,hc]
    simp only [f',Real.norm_eq_abs,abs_mul,abs_of_pos hs₀,abs_of_pos (neg_pos.mpr (BoseShape.C₁_neg (mul_pos hs₀ ht₀)))]
    calc
      _ ≤ B * (s + s ^ 2) * (s * (BoseShape.curvatureHeat 1 * (s * c + 1) ^ 2 * Real.exp (-s * c))) :=
        mul_le_mul (hB s hs₀) (mul_le_mul_of_nonneg_left hU hs₀.le)
          (mul_nonneg hs₀.le (neg_nonneg.mpr (BoseShape.C₁_neg (mul_pos hs₀ ht₀)).le))
          (mul_nonneg hB₀ (by positivity))
      _ ≤ B * (s + s ^ 2) * (s * (BoseShape.curvatureHeat 1 * ((c + 1) * (s + 1)) ^ 2 * Real.exp (-s * c))) := by
        gcongr
      _ = _ := by unfold M K; ring
  have hDeriv : ∀ᵐ s ∂μ, ∀ t ∈ Ioi c, HasDerivAt (fun x => f x s) (f' t s) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    intro t ht
    have ht₀ := hc.trans (mem_Ioi.mp ht)
    have h := (((BoseShape.C_deriv (mul_pos (show 0 < s from hs) ht₀)).comp t
      ((hasDerivAt_id t).const_mul s)).const_mul (g s)).neg
    convert h using 1
    simp only [f',mul_one]
    ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (Ioi_mem_nhds hcr) hF (boseStream_derivative hg hB hr).1.neg hF' hDom hM hDeriv
  exact ⟨h.1,by simpa only [f,integral_neg,f',μ] using h.2⟩

end ACS12.GammaMeasure

import ACS12.BoseShape
import ACS12.BoseMoments
import ACS12.GammaPeriodization

/-! Summation and step derivatives of a signed quadratic Laplace density. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open scoped Topology

noncomputable def signedLaplace (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s : ℝ in Ioi 0, g s * Real.exp (-s * t)

private theorem inverse_expHead_le {x : ℝ} (hx : 0 < x) :
    (1 - Real.exp (-x))⁻¹ ≤ 1 + x⁻¹ := by
  have hd := expHead_den_pos hx
  have hd' := expTail_den_pos hx
  have h := Real.add_one_le_exp x
  have hEq : (1 - Real.exp (-x))⁻¹ = 1 + (Real.exp x - 1)⁻¹ := by
    have he : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    field_simp [hd.ne', hd'.ne']
    linear_combination he
  rw [hEq]
  exact add_le_add le_rfl (inv_anti₀ hx (by linarith))

private theorem signedTail_majorant {g : ℝ → ℝ} {B t q : ℝ} (hg : Measurable g)
    (hB : ∀ s > 0, |g s| ≤ B * s ^ 2) (ht : 0 ≤ t) (hq : 0 < q) :
    IntegrableOn (fun s : ℝ => |g s| *
      (Real.exp (-s * (t + q)) / (1 - Real.exp (-s * q)))) (Ioi 0) := by
  have htq := add_pos_of_nonneg_of_pos ht hq
  have hI := ((expMoment_nat_integrable 2 htq).add
    ((expMoment_nat_integrable 1 htq).const_mul q⁻¹)).const_mul B
  have hM : Measurable (fun s : ℝ => Real.exp (-s * (t + q)) / (1 - Real.exp (-s * q))) := by fun_prop
  have hG : Measurable (fun s => |g s|) := by simpa only [Real.norm_eq_abs] using hg.norm
  apply hI.mono' (hG.mul hM).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  change 0 < s at hs
  have hP : 0 ≤ Real.exp (-s * (t + q)) / (1 - Real.exp (-s * q)) :=
    (div_pos (Real.exp_pos _) (by simpa only [neg_mul] using expHead_den_pos (mul_pos hs hq))).le
  rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) hP)]
  calc
    _ ≤ (B * s ^ 2) * (Real.exp (-s * (t + q)) / (1 - Real.exp (-s * q))) :=
      mul_le_mul_of_nonneg_right (hB s hs) hP
    _ ≤ (B * s ^ 2) * (Real.exp (-s * (t + q)) * (1 + (s * q)⁻¹)) := by
      rw [div_eq_mul_inv]
      have hInv : (1 - Real.exp (-s * q))⁻¹ ≤ 1 + (s * q)⁻¹ := by
        simpa only [neg_mul] using inverse_expHead_le (mul_pos hs hq)
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hInv
        (Real.exp_pos _).le) ((abs_nonneg _).trans (hB s hs))
    _ = _ := by
      dsimp only [Pi.add_apply, pow_one]
      field_simp [hs.ne', hq.ne']

theorem signedTail_majorant_linearQuadratic {g : ℝ → ℝ} {B t q : ℝ} (hg : Measurable g)
    (hB : ∀ s > 0, |g s| ≤ B * (s + s ^ 2)) (ht : 0 ≤ t) (hq : 0 < q) :
    IntegrableOn (fun s : ℝ => |g s| *
      (Real.exp (-s * (t + q)) / (1 - Real.exp (-s * q)))) (Ioi 0) := by
  have htq := add_pos_of_nonneg_of_pos ht hq
  have hI := (((expMoment_nat_integrable 2 htq).add
    ((expMoment_nat_integrable 1 htq).const_mul (1 + q⁻¹))).add
    ((expMoment_nat_integrable 0 htq).const_mul q⁻¹)).const_mul B
  have hM : Measurable (fun s : ℝ => Real.exp (-s * (t + q)) / (1 - Real.exp (-s * q))) := by fun_prop
  have hG : Measurable (fun s => |g s|) := by simpa only [Real.norm_eq_abs] using hg.norm
  apply hI.mono' (hG.mul hM).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  change 0 < s at hs
  have hP : 0 ≤ Real.exp (-s * (t + q)) / (1 - Real.exp (-s * q)) :=
    (div_pos (Real.exp_pos _) (by simpa only [neg_mul] using expHead_den_pos (mul_pos hs hq))).le
  rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) hP)]
  calc
    _ ≤ (B * (s + s ^ 2)) * (Real.exp (-s * (t + q)) / (1 - Real.exp (-s * q))) :=
      mul_le_mul_of_nonneg_right (hB s hs) hP
    _ ≤ (B * (s + s ^ 2)) * (Real.exp (-s * (t + q)) * (1 + (s * q)⁻¹)) := by
      rw [div_eq_mul_inv]
      have hInv : (1 - Real.exp (-s * q))⁻¹ ≤ 1 + (s * q)⁻¹ := by
        simpa only [neg_mul] using inverse_expHead_le (mul_pos hs hq)
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hInv (Real.exp_pos _).le)
        ((abs_nonneg _).trans (hB s hs))
    _ = _ := by
      dsimp only [Pi.add_apply, pow_zero, pow_one, one_mul]
      field_simp [hs.ne', hq.ne'] <;> ring

theorem hasSum_signedTail_of_majorant {g : ℝ → ℝ} {t q : ℝ} (hg : Measurable g)
    (hq : 0 < q) (hMajorant : IntegrableOn (fun s : ℝ => |g s| *
      (Real.exp (-s * (t + q)) / (1 - Real.exp (-s * q)))) (Ioi 0)) :
    HasSum (fun j : ℕ => signedLaplace g (t + q + (j : ℝ) * q))
      (∫ s : ℝ in Ioi 0, g s *
        (Real.exp (-s * (t + q)) / (1 - Real.exp (-s * q)))) := by
  let f (j : ℕ) (s : ℝ) := g s * Real.exp (-s * (t + q + (j : ℝ) * q))
  let G (s : ℝ) := g s * (Real.exp (-s * (t + q)) / (1 - Real.exp (-s * q)))
  let M (s : ℝ) := |g s| * (Real.exp (-s * (t + q)) / (1 - Real.exp (-s * q)))
  have hpoint : ∀ᵐ s : ℝ ∂volume.restrict (Ioi 0), HasSum (fun j => f j s) (G s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    simpa only [f, G, div_eq_mul_inv] using (exponential_samples_hasSum s (t + q) q hs hq).mul_left (g s)
  have hnorm : ∀ᵐ s : ℝ ∂volume.restrict (Ioi 0), HasSum (fun j => ‖f j s‖) (M s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have h (j : ℕ) : ‖f j s‖ = |g s| * Real.exp (-s * (t + q + (j : ℝ) * q)) := by
      dsimp only [f]
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    simp only [h, M, div_eq_mul_inv]
    exact (exponential_samples_hasSum s (t + q) q hs hq).mul_left |g s|
  change HasSum (fun j => ∫ s : ℝ in Ioi 0, f j s) (∫ s : ℝ in Ioi 0, G s)
  refine hasSum_integral_of_dominated_convergence (fun j s => ‖f j s‖) (fun j => ?_)
    (fun _ => Eventually.of_forall fun _ => le_rfl) (hnorm.mono fun _ hs => hs.summable) ?_ hpoint
  · exact (hg.mul (by fun_prop)).aestronglyMeasurable
  · exact hMajorant.congr (hnorm.mono fun _ hs => hs.tsum_eq.symm)

theorem hasSum_signedTail {g : ℝ → ℝ} {B t q : ℝ} (hg : Measurable g)
    (hB : ∀ s > 0, |g s| ≤ B * s ^ 2) (ht : 0 ≤ t) (hq : 0 < q) :
    HasSum (fun j : ℕ => signedLaplace g (t + q + (j : ℝ) * q))
      (∫ s : ℝ in Ioi 0, g s *
        (Real.exp (-s * (t + q)) / (1 - Real.exp (-s * q)))) :=
  hasSum_signedTail_of_majorant hg hq (signedTail_majorant hg hB ht hq)

theorem signedTail_sampling_of_majorant {g : ℝ → ℝ} {t q : ℝ} (hg : Measurable g)
    (hq : 0 < q) (hMajorant : IntegrableOn (fun s : ℝ => |g s| *
      (Real.exp (-s * (t + q)) / (1 - Real.exp (-s * q)))) (Ioi 0)) :
    IntegrableOn (fun s => g s * Real.exp (-s * t) * scaledExpTail s q) (Ioi 0) ∧
      samplingTail (signedLaplace g) t q =
        ∫ s : ℝ in Ioi 0, g s * Real.exp (-s * t) * scaledExpTail s q := by
  have hEq (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      q * (g s * (Real.exp (-s * (t + q)) / (1 - Real.exp (-s * q)))) =
        g s * Real.exp (-s * t) * scaledExpTail s q := by
    have hs₀ : 0 < s := hs
    have he : Real.exp (s * q) * Real.exp (-s * q) = 1 := by
      rw [← Real.exp_add, show s * q + -s * q = 0 by ring, Real.exp_zero]
    have hD : 0 < 1 - Real.exp (-s * q) := by
      simpa only [neg_mul] using expHead_den_pos (mul_pos hs₀ hq)
    have hEqβ : scaledExpTail s q = q * Real.exp (-s * q) / (1 - Real.exp (-s * q)) := by
      unfold scaledExpTail
      apply (div_eq_div_iff (expTail_den_pos (mul_pos hs₀ hq)).ne' hD.ne').mpr
      calc
        q * (1 - Real.exp (-s * q)) = q * (Real.exp (s * q) * Real.exp (-s * q) -
            Real.exp (-s * q)) := by rw [he]
        _ = _ := by ring
    rw [hEqβ, show -s * (t + q) = -s * t + -s * q by ring, Real.exp_add]
    ring
  refine ⟨?_, ?_⟩
  · have hM : Measurable (fun s : ℝ => g s *
        (Real.exp (-s * (t + q)) / (1 - Real.exp (-s * q)))) :=
      hg.mul (by fun_prop)
    have hI := hMajorant.mono' hM.aestronglyMeasurable ?_
    · apply (hI.const_mul q).congr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact hEq s hs
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hDen : 0 < 1 - Real.exp (-s * q) := by
        simpa only [neg_mul] using expHead_den_pos (mul_pos (mem_Ioi.mp hs) hq)
      rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (div_pos (Real.exp_pos _) hDen).le]
  · rw [samplingTail_eq_shift, samplingHead, (hasSum_signedTail_of_majorant hg hq hMajorant).tsum_eq,
      ← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi hEq

theorem signedTail_sampling {g : ℝ → ℝ} {B t q : ℝ} (hg : Measurable g)
    (hB : ∀ s > 0, |g s| ≤ B * s ^ 2) (ht : 0 ≤ t) (hq : 0 < q) :
    IntegrableOn (fun s => g s * Real.exp (-s * t) * scaledExpTail s q) (Ioi 0) ∧
      samplingTail (signedLaplace g) t q =
        ∫ s : ℝ in Ioi 0, g s * Real.exp (-s * t) * scaledExpTail s q :=
  signedTail_sampling_of_majorant hg hq (signedTail_majorant hg hB ht hq)

theorem scaledExpTail_derivative {s q : ℝ} (hs : 0 < s) (hq : 0 < q) :
    HasDerivAt (scaledExpTail s) (-BoseShape.C (s * q)) q := by
  have h := (((BoseShape.expTail_derivative (mul_pos hs hq)).comp q
    ((hasDerivAt_id q).const_mul s)).div_const s)
  convert h using 1
  · funext x
    rw [scaledExpTail_eq_factor hs]
    rfl
  · field_simp [hs.ne']

theorem signedTail_derivative {g : ℝ → ℝ} {B t q : ℝ} (hg : Measurable g)
    (hB : ∀ s > 0, |g s| ≤ B * s ^ 2) (ht : 0 ≤ t) (hq : 0 < q) :
    HasDerivAt (samplingTail (signedLaplace g) t)
      (-(∫ s : ℝ in Ioi 0, g s * Real.exp (-s * t) * BoseShape.C (s * q))) q := by
  let c := q / 2
  let d := 2 * q
  have hc : 0 < c := by dsimp [c]; positivity
  have hcq : c < q := by dsimp [c]; linarith
  have hqd : q < d := by dsimp [d]; linarith
  have hd : 0 ≤ d := by dsimp [d]; positivity
  let μ := volume.restrict (Ioi (0 : ℝ))
  let f (r s : ℝ) := g s * Real.exp (-s * t) * scaledExpTail s r
  let f' (r s : ℝ) := -(g s * Real.exp (-s * t) * BoseShape.C (s * r))
  let K := B * BoseShape.decayConstant * (d + 1)
  let F (s : ℝ) := K * (s ^ 3 * Real.exp (-s * c) + s ^ 2 * Real.exp (-s * c))
  have hfm : ∀ᶠ r in 𝓝 q, AEStronglyMeasurable (f r) μ := by
    exact Eventually.of_forall fun r => ((hg.mul (by fun_prop)).mul
      (show Measurable (fun s => scaledExpTail s r) by unfold scaledExpTail; fun_prop)).aestronglyMeasurable
  have hf'm : AEStronglyMeasurable (f' q) μ := by
    apply Measurable.aestronglyMeasurable
    exact ((hg.mul (by fun_prop)).mul (by unfold BoseShape.C; fun_prop)).neg
  have hF : Integrable F μ := ((expMoment_nat_integrable 3 hc).add
    (expMoment_nat_integrable 2 hc)).const_mul K
  have hDom : ∀ᵐ s : ℝ ∂μ, ∀ r ∈ Ioo c d, ‖f' r s‖ ≤ F s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    intro r hr
    have hs₀ : 0 < s := hs
    have hr₀ := hc.trans hr.1
    have hE : Real.exp (-s * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hD : 0 ≤ BoseShape.decayConstant := BoseShape.decayConstant_pos.le
    have hW : 0 ≤ B * s ^ 2 := (abs_nonneg _).trans (hB s hs₀)
    have hExp : Real.exp (-(s * r)) ≤ Real.exp (-s * c) := by
      apply Real.exp_le_exp.mpr
      simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_left hr.1.le hs₀.le)
    have hArg : s * r + 1 ≤ (d + 1) * (s + 1) := by
      have h := mul_le_mul_of_nonneg_left hr.2.le hs₀.le
      nlinarith only [h, hd, hs₀]
    have hC := BoseShape.C_le_decay (mul_pos hs₀ hr₀)
    simp only [f', Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos (Real.exp_pos (-s * t)),
      abs_of_pos (BoseShape.C_pos (mul_pos hs₀ hr₀))]
    calc
      _ ≤ B * s ^ 2 * BoseShape.C (s * r) :=
        mul_le_mul_of_nonneg_right ((mul_le_of_le_one_right (abs_nonneg _) hE).trans (hB s hs₀))
          (BoseShape.C_pos (mul_pos hs₀ hr₀)).le
      _ ≤ B * s ^ 2 * (BoseShape.decayConstant * (s * r + 1) * Real.exp (-(s * r))) :=
        mul_le_mul_of_nonneg_left hC hW
      _ ≤ B * s ^ 2 * (BoseShape.decayConstant * ((d + 1) * (s + 1)) * Real.exp (-s * c)) := by
        apply mul_le_mul_of_nonneg_left _ hW
        exact mul_le_mul (mul_le_mul_of_nonneg_left hArg hD) hExp (Real.exp_pos _).le (by positivity)
      _ = _ := by dsimp only [F, K]; ring
  have hDeriv : ∀ᵐ s : ℝ ∂μ, ∀ r ∈ Ioo c d, HasDerivAt (fun r => f r s) (f' r s) r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    intro r hr
    convert (scaledExpTail_derivative (mem_Ioi.mp hs) (hc.trans hr.1)).const_mul
      (g s * Real.exp (-s * t)) using 1
    dsimp only [f']
    ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (Ioo_mem_nhds hcq hqd) hfm (signedTail_sampling hg hB ht hq).1 hf'm hDom hF hDeriv
  have hEq : (fun r => ∫ s : ℝ, f r s ∂μ) =ᶠ[𝓝 q] samplingTail (signedLaplace g) t := by
    filter_upwards [Ioi_mem_nhds hq] with r hr
    exact (signedTail_sampling hg hB ht hr).2.symm
  simpa only [f', integral_neg, μ] using h.2.congr_of_eventuallyEq hEq.symm

end ACS12.GammaMeasure


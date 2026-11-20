import ACS12.HighIncidentPure
import ACS12.GammaSourceElasticity
import ACS12.GammaMoments

/-! Transfer of the complete incident kernel comparison to the original image law. -/
namespace ACS12.GammaMeasure

open Set MeasureTheory Filter CenteredCircle.AllN
open GammaDeficit (lineDensity)

private theorem peano_ratio_antitone : AntitoneOn (fun s => polyA s / polyB s) (Ioi 0) := by
  have hD (s : ℝ) (hs : 0 < s) :=
    (hasDerivAt_polyA s).div (hasDerivAt_polyB s) (polyB_pos hs).ne'
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · exact fun s hs => (hD s hs).continuousAt.continuousWithinAt
  · exact fun s hs => (hD s (interior_subset hs)).differentiableAt.differentiableWithinAt
  · intro s hs
    have hs₀ : 0 < s := interior_subset hs
    change deriv (polyA / polyB) s ≤ 0
    rw [(hD s hs₀).deriv]
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    let C (x : ℝ) := Real.exp x + Real.exp (-x) - x ^ 2 - 2
    have hC (x : ℝ) : HasDerivAt C (2 * (Real.sinh x - x)) x := by
      convert (((Real.hasDerivAt_exp x).add (hasDerivAt_id x).neg.exp).sub
        ((hasDerivAt_id x).pow 2)).sub_const 2 using 1
      rw [Real.sinh_eq]
      simp only [Pi.neg_apply,id_eq,mul_one]
      ring
    have hPos : 0 < C s := BoseShape.positive_of_derivative (by norm_num [C]) hC
      (fun x hx => mul_pos (by norm_num) (sub_pos.mpr (Real.self_lt_sinh_iff.mpr hx))) hs₀
    have he : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
    have h := mul_pos (Real.exp_pos (-s)) hPos
    unfold polyA polyB C at *
    nlinarith only [h,he]

private theorem spectralPeano_integrable {p L t : ℝ} (hp : 0 < p) (hL : 0 < L) (ht : 0 < t)
    (k : CircleKernelKind) :
    IntegrableOn (fun s => imageDensity p L s * densityPolynomial k s * Real.exp (-s * t)) (Ioi 0) := by
  have h := (sourceLaplaceMoment_integrable hp hL ht 2).const_mul (1 / 2 : ℝ)
  apply h.mono'
  · exact (((continuous_imageDensity hp hL).measurable.mul (continuous_densityPolynomial k).measurable).mul
      (by fun_prop : Measurable fun s : ℝ => Real.exp (-s * t))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0 < s := hs
    have hw := (imageDensity_pos hp hL hs₀).le
    have hd := (densityPolynomial_pos k hs₀).le
    have hQ := (densityPolynomial_lt_quadratic k hs₀).le
    rw [Real.norm_of_nonneg (by positivity)]
    change _ ≤ (1 / 2) * (imageDensity p L s * s ^ (2 : ℕ) * Real.exp (-s * t))
    nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQ hw) (Real.exp_pos (-s * t)).le]

private theorem pureSpectralPeano_integrable {p t : ℝ} (hp : 0 < p) (ht : 0 < t)
    (k : CircleKernelKind) :
    IntegrableOn (fun s => lineDensity p s * densityPolynomial k s * Real.exp (-s * t)) (Ioi 0) := by
  have h := (lineDensity_moment hp ht 2).1.const_mul (1 / 2 : ℝ)
  apply h.mono'
  · exact (((by unfold lineDensity; fun_prop : Measurable (lineDensity p)).mul
      (continuous_densityPolynomial k).measurable).mul
      (by fun_prop : Measurable fun s : ℝ => Real.exp (-s * t))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0 < s := hs
    have hw := (lineDensity_pos hp hs₀).le
    have hd := (densityPolynomial_pos k hs₀).le
    have hQ := (densityPolynomial_lt_quadratic k hs₀).le
    rw [Real.norm_of_nonneg (by positivity)]
    change _ ≤ (1 / 2) * (lineDensity p s * s ^ (2 : ℕ) * Real.exp (-s * t))
    nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQ hw) (Real.exp_pos (-s * t)).le]

private theorem pureSpectralPeano_eq {p t : ℝ} (hp : 0 < p) (ht : 0 < t) :
    (∫ s : ℝ in Ioi 0, lineDensity p s * polyA s * Real.exp (-s * t)) = purePeanoA p 1 t ∧
      (∫ s : ℝ in Ioi 0, lineDensity p s * polyB s * Real.exp (-s * t)) = purePeanoB p 1 t := by
  obtain ⟨hK,hKE⟩ := lineDensity_moment hp ht 0
  obtain ⟨hU,hUE⟩ := lineDensity_moment hp ht 1
  obtain ⟨hJ,hJE⟩ := lineDensity_moment hp (add_pos ht zero_lt_one) 0
  obtain ⟨hV,hVE⟩ := lineDensity_moment hp (add_pos ht zero_lt_one) 1
  simp only [Nat.cast_zero,Nat.cast_one,add_zero,pow_zero,pow_one,mul_one,
    div_self (Real.Gamma_pos_of_pos hp).ne',Real.Gamma_add_one hp.ne',
    mul_div_cancel_right₀ _ (Real.Gamma_pos_of_pos hp).ne',one_mul] at hK hU hJ hV hKE hUE hJE hVE
  let K (s : ℝ) := lineDensity p s * Real.exp (-s * t)
  let U (s : ℝ) := lineDensity p s * s * Real.exp (-s * t)
  let J (s : ℝ) := lineDensity p s * Real.exp (-s * (t + 1))
  let V (s : ℝ) := lineDensity p s * s * Real.exp (-s * (t + 1))
  have hA (s : ℝ) (_ : s ∈ Ioi 0) : lineDensity p s * polyA s * Real.exp (-s * t) = (K - J - V) s := by
    simp only [K,J,V,Pi.sub_apply,polyA]
    rw [show -s * (t + 1) = -s * t + -s by ring,Real.exp_add]
    ring
  have hB (s : ℝ) (_ : s ∈ Ioi 0) : lineDensity p s * polyB s * Real.exp (-s * t) = (U - K + J) s := by
    simp only [K,U,J,Pi.sub_apply,Pi.add_apply,polyB]
    rw [show -s * (t + 1) = -s * t + -s by ring,Real.exp_add]
    ring
  have hK' : IntegrableOn K (Ioi 0) := hK
  have hU' : IntegrableOn U (Ioi 0) := hU
  have hJ' : IntegrableOn J (Ioi 0) := hJ
  have hV' : IntegrableOn V (Ioi 0) := hV
  constructor
  · rw [setIntegral_congr_fun measurableSet_Ioi hA]
    simp only [Pi.sub_apply]
    rw [integral_sub (f := fun s => K s - J s) (hK'.sub hJ') hV',integral_sub hK' hJ']
    unfold K J V
    rw [hKE,hJE,hVE]
    simp only [purePeanoA,one_mul]
  · rw [setIntegral_congr_fun measurableSet_Ioi hB]
    simp only [Pi.sub_apply,Pi.add_apply]
    rw [integral_add (f := fun s => U s - K s) (hU'.sub hK') hJ',integral_sub hU' hK']
    unfold K U J
    rw [hUE,hKE,hJE]
    simp only [purePeanoB,one_mul]

private theorem integral_negative_of_antitone_tilt {W Q R : ℝ → ℝ}
    (hW : IntegrableOn W (Ioi 0)) (hQ : IntegrableOn (fun s => W s * Q s) (Ioi 0))
    (hR : IntegrableOn (fun s => W s * R s) (Ioi 0))
    (hP : IntegrableOn (fun s => W s * Q s * R s) (Ioi 0))
    (hW₀ : ∀ s > 0, 0 < W s) (hR₀ : ∀ s > 0, 0 < R s)
    (hQM : MonotoneOn Q (Ioi 0)) (hRM : AntitoneOn R (Ioi 0))
    (hSeed : (∫ s : ℝ in Ioi 0, W s * Q s) < 0) :
    (∫ s : ℝ in Ioi 0, W s * Q s * R s) < 0 := by
  have hC := integral_product_comparison hQ hR hP hW (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hE : W x * Q x * (W y * R y) + W y * Q y * (W x * R x) -
        W x * Q x * R x * W y - W y * Q y * R y * W x =
        (W x * W y) * ((Q y - Q x) * (R x - R y)) := by ring
    rw [hE]
    apply mul_nonneg (mul_nonneg (hW₀ x hx).le (hW₀ y hy).le)
    rcases le_total x y with hxy | hyx
    · exact mul_nonneg (sub_nonneg.mpr (hQM hx hy hxy)) (sub_nonneg.mpr (hRM hx hy hxy))
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hQM hy hx hyx)) (sub_nonpos.mpr (hRM hy hx hyx)))
  letI : NeZero (volume.restrict (Ioi (0 : ℝ))) := ⟨positiveHalfLine_ne_zero⟩
  have hPos := integral_strict_of_ae_lt (volume.restrict (Ioi (0 : ℝ))) (integrable_zero ℝ ℝ _) hR (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_pos (hW₀ s hs) (hR₀ s hs))
  rw [integral_zero] at hPos
  exact neg_of_mul_neg_left (hC.trans_lt (mul_neg_of_neg_of_pos hSeed hPos))
    (integral_nonneg_of_ae (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs; exact (hW₀ s hs).le))

theorem highIncident_actualPeano_ratio {p L b t : ℝ} (hp : 2 ≤ p) (hP : p ≤ 4) (hL : 0 < L)
    (hb : 0 < b) (hbU : b ≤ 5 / 8) (ht : b ≤ t) :
    b * imageMoment p L .b 0 t < ((p + 4) / 2) * imageMoment p L .a 0 t := by
  let W (s : ℝ) := lineDensity p s * polyB s * Real.exp (-s * b)
  let σ := (p + 4) / 2
  let Q (s : ℝ) := b - σ * (polyA s / polyB s)
  let R (s : ℝ) := (imageDensity p L s / lineDensity p s) * Real.exp (-s * (t - b))
  have hp₀ : 0 < p := by linarith only [hp]
  have ht₀ := hb.trans_le ht
  have hσ : 0 ≤ σ := by unfold σ; positivity
  have hQM : MonotoneOn Q (Ioi 0) := by
    intro x hx y hy hxy
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left (peano_ratio_antitone hx hy hxy) hσ) _
  have hRM : AntitoneOn R (Ioi 0) := by
    intro x hx y hy hxy
    apply mul_le_mul (imageDensity_div_lineDensity_antitone hp hL hx hy hxy) _ (Real.exp_pos _).le
      (div_pos (imageDensity_pos hp₀ hL hx) (lineDensity_pos hp₀ hx)).le
    exact Real.exp_le_exp.mpr (by nlinarith only [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr ht)])
  have hW : IntegrableOn W (Ioi 0) := pureSpectralPeano_integrable hp₀ hb .b
  have hW₀ (s : ℝ) (hs : 0 < s) : 0 < W s :=
    mul_pos (mul_pos (lineDensity_pos hp₀ hs) (polyB_pos hs)) (Real.exp_pos _)
  have hR₀ (s : ℝ) (hs : 0 < s) : 0 < R s :=
    mul_pos (div_pos (imageDensity_pos hp₀ hL hs) (lineDensity_pos hp₀ hs)) (Real.exp_pos _)
  have hQeq (s : ℝ) (hs : 0 < s) :
      W s * Q s = b * W s - σ * (lineDensity p s * polyA s * Real.exp (-s * b)) := by
    unfold W Q
    field_simp [(polyB_pos hs).ne'] <;> ring
  have hReq (s : ℝ) (hs : 0 < s) : W s * R s = imageDensity p L s * polyB s * Real.exp (-s * t) := by
    have he : Real.exp (-s * b) * Real.exp (-s * (t - b)) = Real.exp (-s * t) := by rw [← Real.exp_add]; congr 1; ring
    have hρ : lineDensity p s * (imageDensity p L s / lineDensity p s) = imageDensity p L s := by
      field_simp [(lineDensity_pos hp₀ hs).ne']
    calc
      W s * R s = (lineDensity p s * (imageDensity p L s / lineDensity p s)) *
          polyB s * (Real.exp (-s * b) * Real.exp (-s * (t - b))) := by unfold W R; ring
      _ = _ := by rw [hρ,he]
  have hPeq (s : ℝ) (hs : 0 < s) : W s * Q s * R s =
      b * (imageDensity p L s * polyB s * Real.exp (-s * t)) -
        σ * (imageDensity p L s * polyA s * Real.exp (-s * t)) := by
    rw [mul_right_comm,hReq s hs]
    unfold Q
    field_simp [(polyB_pos hs).ne'] <;> ring
  have hQA : IntegrableOn (fun s => lineDensity p s * polyA s * Real.exp (-s * b)) (Ioi 0) :=
    pureSpectralPeano_integrable hp₀ hb .a
  have hIA : IntegrableOn (fun s => imageDensity p L s * polyA s * Real.exp (-s * t)) (Ioi 0) :=
    spectralPeano_integrable hp₀ hL ht₀ .a
  have hIB : IntegrableOn (fun s => imageDensity p L s * polyB s * Real.exp (-s * t)) (Ioi 0) :=
    spectralPeano_integrable hp₀ hL ht₀ .b
  have hQ : IntegrableOn (fun s => W s * Q s) (Ioi 0) := by
    apply ((hW.const_mul b).sub (hQA.const_mul σ)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hQeq s hs).symm
  have hR : IntegrableOn (fun s => W s * R s) (Ioi 0) := by
    apply hIB.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hReq s hs).symm
  have hP' : IntegrableOn (fun s => W s * Q s * R s) (Ioi 0) := by
    apply ((hIB.const_mul b).sub (hIA.const_mul σ)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hPeq s hs).symm
  have hSeed : (∫ s : ℝ in Ioi 0, W s * Q s) < 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun s hs => hQeq s hs),
      integral_sub (hW.const_mul b) (hQA.const_mul σ),integral_const_mul,integral_const_mul]
    have ⟨hA,hB⟩ := pureSpectralPeano_eq hp₀ hb
    change b * (∫ s : ℝ in Ioi 0, lineDensity p s * polyB s * Real.exp (-s * b)) - _ < 0
    rw [hA,hB]
    exact sub_neg.mpr (highIncident_purePeano_ratio (by linarith only [hp]) hP hb hbU)
  have h := integral_negative_of_antitone_tilt hW hQ hR hP' hW₀ hR₀ hQM hRM hSeed
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s hs => hPeq s hs),
    integral_sub (hIB.const_mul b) (hIA.const_mul σ),integral_const_mul,integral_const_mul] at h
  exact sub_neg.mp (by simpa only [imageMoment,imageMomentWeight,densityPolynomial,pow_zero,one_mul] using h)

end ACS12.GammaMeasure

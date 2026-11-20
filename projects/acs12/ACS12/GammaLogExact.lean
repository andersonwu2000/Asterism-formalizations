import ACS12.GammaCosineMoment
import ACS12.LaplaceLog

/-! The full logarithmic Gamma modulus contrast from its Euler products. -/

namespace ACS12.GammaMeasure

open MeasureTheory Set Filter
open scoped Topology BigOperators

noncomputable def gammaLogContrast (q x y : ℝ) : ℝ :=
  Real.log (‖Complex.Gamma (gammaArgument q y)‖ / ‖Complex.Gamma (gammaArgument q x)‖)

noncomputable def logContrastIntegrand (q x y t : ℝ) : ℝ :=
  evenGammaProfile t * Real.exp (-(q - 1 / 2) * t) *
    ((Real.cos (y * t) - Real.cos (x * t)) / t ^ 2)

private theorem abs_cos_sub_cos_quadratic (x y : ℝ) :
    |Real.cos y - Real.cos x| ≤ (x ^ 2 + y ^ 2) / 2 := by
  have hx₀ := Real.one_sub_sq_div_two_le_cos (x := x)
  have hy₀ := Real.one_sub_sq_div_two_le_cos (x := y)
  have hx₁ := Real.cos_le_one x
  have hy₁ := Real.cos_le_one y
  rw [abs_le]
  constructor <;> linarith [sq_nonneg x, sq_nonneg y]

theorem norm_logContrastIntegrand_le {q : ℝ} (hq : 1 / 2 ≤ q) (x y : ℝ)
    {t : ℝ} (ht : 0 < t) :
    ‖logContrastIntegrand q x y t‖ ≤ ((x ^ 2 + y ^ 2) / 2) * evenGammaProfile t := by
  have hExp : Real.exp (-(q - 1 / 2) * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) ht.le)
  have hcos := abs_cos_sub_cos_quadratic (x * t) (y * t)
  have ht₂ := sq_pos_of_pos ht
  have hB : |Real.cos (y * t) - Real.cos (x * t)| / t ^ 2 ≤ (x ^ 2 + y ^ 2) / 2 := by
    apply (div_le_iff₀ ht₂).mpr
    exact hcos.trans_eq (by ring)
  simp only [logContrastIntegrand, Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos
    (evenGammaProfile_pos t), abs_of_pos (Real.exp_pos _), abs_of_pos ht₂]
  calc
    _ ≤ evenGammaProfile t * (|Real.cos (y * t) - Real.cos (x * t)| / t ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_of_le_one_right (evenGammaProfile_pos t).le hExp
    _ = ((|Real.cos (y * t) - Real.cos (x * t)| / t ^ 2) * evenGammaProfile t) := mul_comm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hB (evenGammaProfile_pos t).le

theorem logContrastIntegrand_integrable {q : ℝ} (hq : 1 / 2 ≤ q) (x y : ℝ) :
    IntegrableOn (logContrastIntegrand q x y) (Ioi 0) := by
  have hE : Measurable evenGammaProfile :=
    (continuous_const.mul ((continuous_gammaDensity (by norm_num : 0 < (2 : ℝ))).comp
      (by fun_prop))).measurable
  refine (evenGammaProfile_integrable.integrableOn.const_mul ((x ^ 2 + y ^ 2) / 2)).mono' ?_ ?_
  · unfold logContrastIntegrand
    exact (by fun_prop (disch := assumption) : Measurable _).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_logContrastIntegrand_le hq x y ht

private theorem gammaArgument_add_norm_pos {q : ℝ} (hq : 0 < q) (x : ℝ) (j : ℕ) :
    0 < ‖gammaArgument q x + (j : ℂ)‖ := by
  apply norm_pos_iff.mpr
  intro h
  have hRe := congrArg Complex.re h
  simp at hRe
  linarith [Nat.cast_nonneg (α := ℝ) j]

private theorem gammaSeq_logContrast_eq {q : ℝ} (hq : 0 < q) (x y : ℝ)
    {N : ℕ} (hN : 0 < N) :
    Real.log (‖Complex.GammaSeq (gammaArgument q y) N‖ /
        ‖Complex.GammaSeq (gammaArgument q x) N‖) =
      ∑ j ∈ Finset.range (N + 1),
        (Real.log ((q + j) ^ 2 + x ^ 2) - Real.log ((q + j) ^ 2 + y ^ 2)) / 2 := by
  have hp (t : ℝ) : 0 < ∏ j ∈ Finset.range (N + 1), ‖gammaArgument q t + (j : ℂ)‖ :=
    Finset.prod_pos fun j _ => gammaArgument_add_norm_pos hq t j
  have hn : 0 < (N : ℝ) ^ q * (N.factorial : ℝ) := by positivity
  rw [norm_GammaSeq hq, norm_GammaSeq hq]
  rw [show (N : ℝ) ^ q * (N.factorial : ℝ) /
      (∏ j ∈ Finset.range (N + 1), ‖gammaArgument q y + (j : ℂ)‖) /
      ((N : ℝ) ^ q * (N.factorial : ℝ) /
      (∏ j ∈ Finset.range (N + 1), ‖gammaArgument q x + (j : ℂ)‖)) =
      (∏ j ∈ Finset.range (N + 1), ‖gammaArgument q x + (j : ℂ)‖) /
      (∏ j ∈ Finset.range (N + 1), ‖gammaArgument q y + (j : ℂ)‖) by
        field_simp [(hp x).ne', (hp y).ne', hn.ne']]
  rw [Real.log_div (hp x).ne' (hp y).ne', Real.log_prod (fun j _ =>
    (gammaArgument_add_norm_pos hq x j).ne'), Real.log_prod (fun j _ =>
      (gammaArgument_add_norm_pos hq y j).ne'), ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← norm_gammaArgument_add, ← norm_gammaArgument_add, Real.log_pow, Real.log_pow]
  ring

private theorem truncatedLog_profile {q : ℝ} (x y : ℝ)
    {t : ℝ} (ht : 0 < t) (N : ℕ) :
    (∑ j ∈ Finset.range (N + 1), cosineDifference (q + j) y x t) =
      logContrastIntegrand q x y t * (1 - Real.exp (-t) ^ (N + 1)) := by
  have htE : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)
  have hden : 1 - Real.exp (-t) ≠ 0 := (sub_pos.mpr htE).ne'
  have hE (j : ℕ) : Real.exp (-(q + (j : ℝ)) * t) =
      Real.exp (-q * t) * (Real.exp (-t)) ^ j := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have hGeom : (∑ j ∈ Finset.range (N + 1), Real.exp (-t) ^ j) =
      (1 - Real.exp (-t) ^ (N + 1)) / (1 - Real.exp (-t)) := by
    exact (eq_div_iff hden).mpr (geom_sum_mul_neg _ _)
  have hE' : Real.exp (-(1 / 2 : ℝ) * t) * Real.exp (-(q - 1 / 2) * t) =
      Real.exp (-q * t) := by rw [← Real.exp_add]; congr 1; ring
  have hF : logContrastIntegrand q x y t =
      Real.exp (-q * t) / (1 - Real.exp (-t)) * ((Real.cos (y * t) - Real.cos (x * t)) / t) := by
    rw [← hE', logContrastIntegrand, evenGammaProfile_eq ht]
    field_simp [ht.ne', hden]
  simp only [cosineDifference, hE, mul_div_assoc, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [hGeom, hF]
  ring

theorem gammaLogContrast_eq_integral {q : ℝ} (hq : 1 / 2 ≤ q) (x y : ℝ) :
    gammaLogContrast q x y = ∫ t : ℝ in Ioi 0, logContrastIntegrand q x y t := by
  have hq₀ : 0 < q := by linarith
  let F (N : ℕ) (t : ℝ) := ∑ j ∈ Finset.range (N + 1), cosineDifference (q + j) y x t
  have hInt (j : ℕ) : IntegrableOn (cosineDifference (q + j) y x) (Ioi 0) :=
    cosineDifference_integrable (by positivity) y x
  have hlim : Tendsto (fun N : ℕ => ∫ t : ℝ in Ioi 0, F N t) atTop
      (𝓝 (∫ t : ℝ in Ioi 0, logContrastIntegrand q x y t)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun t => ‖logContrastIntegrand q x y t‖)
    · exact Eventually.of_forall fun N =>
        (integrable_finsetSum _ (fun j _ => hInt j)).aestronglyMeasurable
    · exact Eventually.of_forall fun N => by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        change 0 < t at ht
        dsimp only [F]
        rw [truncatedLog_profile (q := q) x y ht, norm_mul]
        have hPos := pow_nonneg (Real.exp_pos (-t)).le (N + 1)
        have hLe := pow_le_one₀ (Real.exp_pos (-t)).le
          (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.le)) (n := N + 1)
        rw [Real.norm_of_nonneg (sub_nonneg.mpr hLe)]
        exact mul_le_of_le_one_right (norm_nonneg _) (by linarith)
    · exact (logContrastIntegrand_integrable hq x y).norm
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      change 0 < t at ht
      have hZero := tendsto_pow_atTop_nhds_zero_of_lt_one
        (Real.exp_pos (-t)).le (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht))
      have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub
        (hZero.comp (tendsto_add_atTop_nat 1))).const_mul (logContrastIntegrand q x y t)
      simpa only [F, truncatedLog_profile (q := q) x y ht, sub_zero, mul_one, Function.comp_apply] using h
  have hΓ (t : ℝ) : ‖Complex.Gamma (gammaArgument q t)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by simpa using hq₀))
  have hSeq := ((Complex.GammaSeq_tendsto_Gamma (gammaArgument q y)).norm.div
    (Complex.GammaSeq_tendsto_Gamma (gammaArgument q x)).norm (hΓ x)).log
      (div_ne_zero (hΓ y) (hΓ x))
  have hEq : (fun N : ℕ => ∫ t : ℝ in Ioi 0, F N t) =ᶠ[atTop]
      fun N => Real.log (‖Complex.GammaSeq (gammaArgument q y) N‖ /
        ‖Complex.GammaSeq (gammaArgument q x) N‖) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    dsimp only [F]
    rw [integral_finsetSum _ (fun j _ => hInt j),
      gammaSeq_logContrast_eq hq₀ x y (by omega)]
    exact Finset.sum_congr rfl (fun j _ => integral_cosineDifference (by positivity) y x)
  exact tendsto_nhds_unique ((tendsto_congr' hEq).mpr hSeq) hlim

end ACS12.GammaMeasure

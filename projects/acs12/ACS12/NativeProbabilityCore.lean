import ACS12.GammaMixture
import ACS12.BoseMoments
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! Generic positive discrete and Gamma integration tools, independent of a translated representation. -/
namespace ACS12.NativeCells
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
open GammaMeasure (powerTail powerTail_pos powerTail_summable)
open GammaMixture (gammaProduct gammaTotal)

noncomputable def nativeZetaWeight (p : ℝ) (k : ℕ) : ℝ :=
  (1 + (k : ℝ)) ^ (-p) / powerTail p 1

noncomputable def nativeZetaMeasure (p : ℝ) : Measure ℕ :=
  Measure.count.withDensity (fun k => ENNReal.ofReal (nativeZetaWeight p k))

private theorem nativeZetaWeight_nonneg {p : ℝ} (hp : 1 < p) (k : ℕ) :
    0 ≤ nativeZetaWeight p k := by
  unfold nativeZetaWeight
  exact div_nonneg (Real.rpow_nonneg (by positivity) _) (powerTail_pos hp (by decide)).le

theorem nativeZeta_probability {p : ℝ} (hp : 1 < p) : IsProbabilityMeasure (nativeZetaMeasure p) := by
  have hS : Summable (nativeZetaWeight p) := by
    have h := (powerTail_summable hp 1).div_const (powerTail p 1)
    simpa only [nativeZetaWeight,Nat.cast_one] using h
  constructor
  unfold nativeZetaMeasure
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,lintegral_count,
    ← ENNReal.ofReal_tsum_of_nonneg (nativeZetaWeight_nonneg hp) hS]
  have hE : (∑' k : ℕ, nativeZetaWeight p k) = 1 := by
    unfold nativeZetaWeight
    rw [tsum_div_const]
    simpa only [powerTail,Nat.cast_one] using (div_self (powerTail_pos hp (show (0 : ℕ) < 1 by decide)).ne')
  rw [hE,ENNReal.ofReal_one]

theorem nativeZeta_integral_eq_tsum {p : ℝ} (hp : 1 < p) (f : ℕ → ℝ)
    (hF : Integrable f (nativeZetaMeasure p)) :
    (∫ k, f k ∂nativeZetaMeasure p) = ∑' k, nativeZetaWeight p k * f k := by
  rw [integral_countable hF]
  apply tsum_congr
  intro k
  unfold nativeZetaMeasure Measure.real
  rw [withDensity_apply _ (MeasurableSet.singleton k),lintegral_singleton,
    show (Measure.count : Measure ℕ) {k} = 1 by simp [Measure.count_apply],
    mul_one,ENNReal.toReal_ofReal (nativeZetaWeight_nonneg hp k),smul_eq_mul]

theorem nativeZeta_power {p r : ℝ} (hp : 1 < p) (hR : 1 < p - r) :
    Integrable (fun k : ℕ => (1 + (k : ℝ)) ^ r) (nativeZetaMeasure p) ∧
      (∫ k : ℕ, (1 + (k : ℝ)) ^ r ∂nativeZetaMeasure p) =
        powerTail (p - r) 1 / powerTail p 1 := by
  let f (k : ℕ) := (1 + (k : ℝ)) ^ r
  let w := nativeZetaWeight p
  have hM : Measurable (fun k => ENNReal.ofReal (w k)) := Measurable.of_discrete
  have hW (k : ℕ) : w k * f k = (1 + (k : ℝ)) ^ (-(p - r)) / powerTail p 1 := by
    unfold w f nativeZetaWeight
    rw [div_mul_eq_mul_div,← Real.rpow_add (by positivity)]
    congr 2
    ring
  have hS : Summable (fun k => w k * f k) := by
    simp_rw [hW]
    simpa only [Nat.cast_one] using (powerTail_summable hR 1).div_const (powerTail p 1)
  have hI : Integrable f (nativeZetaMeasure p) := by
    unfold nativeZetaMeasure
    apply (integrable_withDensity_iff hM (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
    apply integrable_count_iff.mpr
    convert hS using 1
    funext k
    rw [ENNReal.toReal_ofReal (nativeZetaWeight_nonneg hp k),mul_comm (f k)]
    exact Real.norm_of_nonneg (mul_nonneg (nativeZetaWeight_nonneg hp k) (by unfold f; positivity))
  refine ⟨hI,?_⟩
  calc
    _ = ∑' k, w k * f k := nativeZeta_integral_eq_tsum hp f hI
    _ = _ := by
      simp_rw [hW]
      rw [tsum_div_const]
      simp only [powerTail,Nat.cast_one]

theorem gammaUnitIntegral {q : ℝ} (hq : 0 < q) (f : ℝ → ℝ) :
    (∫ g : ℝ, f g ∂gammaMeasure q 1) =
      ∫ g : ℝ in Ioi 0, ((Real.Gamma q)⁻¹ * g ^ (q - 1) * Real.exp (-g)) * f g := by
  have hM : Measurable (gammaPDF q 1) := (measurable_gammaPDFReal q 1).ennreal_ofReal
  unfold gammaMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hM (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) f,
    ← integral_Ici_eq_integral_Ioi,← integral_indicator measurableSet_Ici]
  apply integral_congr_ae
  exact Eventually.of_forall fun g => by
    dsimp only
    rw [gammaPDF,ENNReal.toReal_ofReal (gammaPDFReal_nonneg hq zero_lt_one g),smul_eq_mul]
    by_cases h : 0 ≤ g
    · simp [gammaPDFReal,h,indicator_of_mem,one_div]
    · simp [gammaPDFReal,h,indicator_of_notMem]

theorem gammaUnit_ae_pos (q : ℝ) : ∀ᵐ g : ℝ ∂gammaMeasure q 1, 0 < g := by
  unfold gammaMeasure
  apply (ae_withDensity_iff (measurable_gammaPDFReal q 1).ennreal_ofReal).mpr
  have hn : ∀ᵐ g : ℝ ∂volume, g ≠ 0 := by rw [ae_iff]; simp
  filter_upwards [hn] with g hg hD
  by_contra! h
  exact hD (gammaPDF_of_neg (lt_of_le_of_ne h hg))

theorem gammaUnit_power {q r : ℝ} (hq : 0 < q) (hR : 0 < q + r) :
    Integrable (fun g : ℝ => g ^ r) (gammaMeasure q 1) ∧
      (∫ g : ℝ, g ^ r ∂gammaMeasure q 1) = Real.Gamma (q + r) / Real.Gamma q := by
  have hE : (∫ g : ℝ, g ^ r ∂gammaMeasure q 1) = Real.Gamma (q + r) / Real.Gamma q := by
    rw [gammaUnitIntegral hq]
    have hF (g : ℝ) (hg : 0 < g) :
        (Real.Gamma q)⁻¹ * g ^ (q - 1) * Real.exp (-g) * g ^ r =
          (Real.Gamma q)⁻¹ * (g ^ (q + r - 1) * Real.exp (-1 * g)) := by
      rw [show q + r - 1 = q - 1 + r by ring,Real.rpow_add hg,neg_one_mul]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi (fun g hg => hF g hg),integral_const_mul,
      GammaDeficit.gamma_exp_integral hR zero_lt_one,Real.one_rpow,mul_one,div_eq_mul_inv,mul_comm]
  exact ⟨Integrable.of_integral_ne_zero (hE ▸ (div_pos (Real.Gamma_pos_of_pos hR) (Real.Gamma_pos_of_pos hq)).ne'),hE⟩

end ACS12.NativeCells

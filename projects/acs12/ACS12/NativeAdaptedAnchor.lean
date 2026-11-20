import ACS12.NativeBoseRow
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-! The alpha-adapted tangent under the normalized original-anchor law. -/
namespace ACS12.NativeCells

open MeasureTheory Set Filter

theorem adaptedRawTangent_pos {m t : ℝ} (hm : 1 / 2 < m) (hm₁ : m ≤ 1)
    (ht : 0 < t) (ht₁ : t ≠ 1) :
    0 < (2 * m - 1) * (t - 1) - Real.log ((1 - m + m * t ^ 2) / ((1 + t ^ 2) / 2)) := by
  have hm₀ : 0 < m := by linarith only [hm]
  have hA : 0 < 1 - m + m * t ^ 2 :=
    add_pos_of_nonneg_of_pos (sub_nonneg.mpr hm₁) (mul_pos hm₀ (sq_pos_of_pos ht))
  have hB : 0 < (1 + t ^ 2) / 2 := by positivity
  have h := Real.log_le_sub_one_of_pos (div_pos hA hB)
  have hE : (2 * m - 1) * (t - 1) - ((1 - m + m * t ^ 2) / ((1 + t ^ 2) / 2) - 1) =
      (2 * m - 1) * ((t - 1) ^ 2 * t) / (1 + t ^ 2) := by
    field_simp
    ring
  have hPos : 0 < (2 * m - 1) * ((t - 1) ^ 2 * t) / (1 + t ^ 2) :=
    div_pos (mul_pos (by linarith only [hm]) (mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr ht₁)) ht)) (by positivity)
  linarith only [h,hE,hPos]

theorem adaptedAnchor_Jensen {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hY : Measurable Y)
    (hYrange : ∀ᵐ s ∂μ, Y s ∈ Icc (0 : ℝ) 1) {h t : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) :
    let m := ∫ s, Y s ∂μ
    (∫ s, (1 + Y s * (t ^ 2 - 1)) ^ h ∂μ) ≤ (1 - m + m * t ^ 2) ^ h := by
  let f (s : Ω) := 1 + Y s * (t ^ 2 - 1)
  let B := max 1 (t ^ 2)
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hF : ∀ᵐ s ∂μ, f s ∈ Icc (0 : ℝ) B := by
    filter_upwards [hYrange] with s hs
    have hE : f s = (1 - Y s) * 1 + Y s * t ^ 2 := by unfold f; ring
    rw [hE]
    have ha := sub_nonneg.mpr hs.2
    have h₀ := mul_le_mul_of_nonneg_left (le_max_left (1 : ℝ) (t ^ 2)) ha
    have h₁ := mul_le_mul_of_nonneg_left (le_max_right (1 : ℝ) (t ^ 2)) hs.1
    refine ⟨add_nonneg (mul_nonneg ha zero_le_one) (mul_nonneg hs.1 (sq_nonneg _)),?_⟩
    unfold B
    linarith only [h₀,h₁]
  have hYM : Integrable Y μ := by
    apply (integrable_const (μ := μ) (1 : ℝ)).mono' hY.aestronglyMeasurable
    filter_upwards [hYrange] with s hs
    simpa only [Real.norm_of_nonneg hs.1] using hs.2
  have hM : Measurable f := (hY.mul_const _).const_add _
  have hI : Integrable f μ := by
    apply (integrable_const (μ := μ) B).mono' hM.aestronglyMeasurable
    filter_upwards [hF] with s hs
    simpa only [Real.norm_of_nonneg hs.1] using hs.2
  have hJ : Integrable (fun s => f s ^ h) μ := by
    apply (integrable_const (μ := μ) (B ^ h)).mono'
      (hM.pow_const h).aestronglyMeasurable
    filter_upwards [hF] with s hs
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hs.1 _)]
    exact Real.rpow_le_rpow hs.1 hs.2 hh.le
  have hC := (Real.concaveOn_rpow hh.le hh₁).subset
    (show Icc (0 : ℝ) B ⊆ Ici 0 from fun _ hs => hs.1) (convex_Icc _ _)
  have hE : (∫ s, f s ∂μ) = 1 - (∫ s, Y s ∂μ) + (∫ s, Y s ∂μ) * t ^ 2 := by
    unfold f
    rw [integral_add (integrable_const _) (hYM.mul_const _),integral_const,probReal_univ,one_smul,integral_mul_const]
    ring
  have hK := hC.le_map_integral (Real.continuous_rpow_const hh.le).continuousOn
    isClosed_Icc hF hI hJ
  rw [hE] at hK
  exact hK

/-- The raw logarithmic tangent follows from the actual tilted probability and its anchor mean. -/
theorem adaptedAnchor_logTangent {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hY : Measurable Y)
    (hYrange : ∀ᵐ s ∂μ, Y s ∈ Icc (0 : ℝ) 1) {h t : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    (ht : 0 < t) (ht₁ : t ≠ 1) (hm : 1 / 2 < ∫ s, Y s ∂μ)
    (hU : 0 < ∫ s, (1 + Y s * (t ^ 2 - 1)) ^ h ∂μ) :
    0 < h * (2 * (∫ s, Y s ∂μ) - 1) * (t - 1) -
      Real.log ((∫ s, (1 + Y s * (t ^ 2 - 1)) ^ h ∂μ) / ((1 + t ^ 2) / 2) ^ h) := by
  let m := ∫ s, Y s ∂μ
  let A := 1 - m + m * t ^ 2
  let B := (1 + t ^ 2) / 2
  let U := ∫ s, (1 + Y s * (t ^ 2 - 1)) ^ h ∂μ
  have hm₁ : m ≤ 1 := by
    have h := integral_mono_of_nonneg (μ := μ) (f := Y) (g := fun _ => (1 : ℝ))
      (hYrange.mono fun _ hs => hs.1) (integrable_const _)
      (hYrange.mono fun _ hs => hs.2)
    rw [integral_const,probReal_univ,one_smul] at h
    exact h
  have hA : 0 < A := add_pos_of_nonneg_of_pos (sub_nonneg.mpr hm₁)
    (mul_pos (by linarith only [hm] : 0 < m) (sq_pos_of_pos ht))
  have hB : 0 < B := by unfold B; positivity
  have hE : U ≤ A ^ h := adaptedAnchor_Jensen hY hYrange hh hh₁
  have hP : Real.log (U / B ^ h) ≤ Real.log (A ^ h / B ^ h) :=
    Real.log_le_log (div_pos hU (Real.rpow_pos_of_pos hB h))
      (div_le_div_of_nonneg_right hE (Real.rpow_nonneg hB.le h))
  rw [← Real.div_rpow hA.le hB.le, Real.log_rpow (div_pos hA hB)] at hP
  have hS := mul_pos hh (adaptedRawTangent_pos hm hm₁ ht ht₁)
  change 0 < h * (2 * m - 1) * (t - 1) - Real.log (U / B ^ h)
  change 0 < h * ((2 * m - 1) * (t - 1) - Real.log (A / B)) at hS
  nlinarith only [hP,hS]

end ACS12.NativeCells


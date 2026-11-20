import ACS12.LeftShape
import ACS12.BoseShape
import ACS12.BoseMoments

/-! The two strict full-ray moments for the original signed left multiplier. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open scoped Topology

theorem integrable_leftMoment {w g : ℝ → ℝ} {B D c : ℝ} (hc : 0 < c)
    (hw : Measurable w) (hg : Measurable g) (hwB : ∀ s > 0, |w s| ≤ B * s)
    (hgB : ∀ s > 0, |g s| ≤ D * (s + 1) * Real.exp (-s * c)) (a z : ℝ) :
    IntegrableOn (fun s => w s * leftMultiplier a z s * g s) (Ioi 0) := by
  let A := 1 + |a| + |z|
  have hM : Measurable (leftMultiplier a z) := by unfold leftMultiplier; fun_prop
  have h := (((expMoment_nat_integrable 3 hc).add (expMoment_nat_integrable 2 hc)).const_mul
    (B * A * D))
  refine h.mono' ((hw.mul hM).mul hg).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  change 0 < s at hs
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  calc
    _ ≤ B * s * (A * s) * (D * (s + 1) * Real.exp (-s * c)) := by
      exact mul_le_mul (mul_le_mul (hwB s hs) (leftMultiplier_abs_le a z hs) (abs_nonneg _)
        ((abs_nonneg _).trans (hwB s hs))) (hgB s hs) (abs_nonneg _)
        (mul_nonneg ((abs_nonneg _).trans (hwB s hs)) (by dsimp [A]; positivity))
    _ = _ := by dsimp only [Pi.add_apply]; ring

private theorem reference_first_integrable (a z : ℝ) :
    IntegrableOn (fun s => s * leftMultiplier a z s * (s * Real.exp (-s))) (Ioi 0) := by
  refine integrable_leftMoment (B := 1) (D := 1) zero_lt_one measurable_id (by fun_prop)
    (fun s hs => by simp [abs_of_pos hs]) ?_ a z
  intro s hs
  rw [abs_of_nonneg (mul_nonneg hs.le (Real.exp_pos _).le), mul_one, one_mul]
  exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

theorem reference_second_integrable (a z : ℝ) :
    IntegrableOn (fun s => s * leftMultiplier a z s * BoseShape.C s) (Ioi 0) := by
  refine integrable_leftMoment (B := 1) (D := BoseShape.decayConstant) zero_lt_one measurable_id
    (by unfold BoseShape.C; fun_prop) (fun s hs => by simp [abs_of_pos hs]) ?_ a z
  intro s hs
  rw [abs_of_pos (BoseShape.C_pos hs), mul_one]
  exact BoseShape.C_le_decay hs

private theorem reference_first_eq (a z : ℝ) :
    (∫ s : ℝ in Ioi 0, s * leftMultiplier a z s * (s * Real.exp (-s))) =
      7 / 4 - 6 * a - 3 * z / 8 := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  let f (s : ℝ) := s ^ 2 * Real.exp (-s * 1)
  let g (s : ℝ) := s ^ 2 * Real.exp (-s * 2)
  let h (s : ℝ) := s ^ 3 * Real.exp (-s * 1)
  let k (s : ℝ) := s ^ 3 * Real.exp (-s * 2)
  have hPoint (s : ℝ) : s * leftMultiplier a z s * (s * Real.exp (-s)) =
      1 * f s + (-1) * g s - a * h s - z * k s := by
    simp only [leftMultiplier, f, g, h, k, mul_one, show -s * (2 : ℝ) = -s + -s by ring,
      Real.exp_add]
    ring
  simp_rw [hPoint]
  rw [integral_four_terms (μ := μ) (expMoment_nat_integrable 2 zero_lt_one)
    (expMoment_nat_integrable 2 (by norm_num : (0 : ℝ) < 2)) (expMoment_nat_integrable 3 zero_lt_one)
    (expMoment_nat_integrable 3 (by norm_num : (0 : ℝ) < 2))]
  dsimp only [f, g, h, k, μ]
  rw [expMoment_nat_integral 2 zero_lt_one, expMoment_nat_integral 2 (by norm_num : (0 : ℝ) < 2),
    expMoment_nat_integral 3 zero_lt_one, expMoment_nat_integral 3 (by norm_num : (0 : ℝ) < 2)]
  norm_num [Nat.factorial] <;> ring

theorem reference_second_eq (a z : ℝ) :
    (∫ s : ℝ in Ioi 0, s * leftMultiplier a z s * BoseShape.C s) =
      2 * (1 - 2 * (a + z)) * powerTail 3 1 + 6 * z * powerTail 4 1 - 1 - 2 * z := by
  let P (s : ℝ) := s * leftMultiplier a z s
  let P' (s : ℝ) := (1 - Real.exp (-s)) - 2 * a * s +
    (1 - 2 * z) * s * Real.exp (-s) + z * s ^ 2 * Real.exp (-s)
  let β := expTailFactor
  have hD (s : ℝ) : HasDerivAt P (P' s) s := by
    have hE := (hasDerivAt_id s).neg.exp
    have hH := ((hE.const_sub 1).sub ((hasDerivAt_id s).const_mul a)).sub
      (((hasDerivAt_id s).const_mul z).mul hE)
    convert (hasDerivAt_id s).mul hH using 1
    simp only [P', id_eq, mul_one, one_mul, Pi.mul_apply, Pi.sub_apply, Pi.neg_apply]
    ring
  let A := 1 + |a| + |z|
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hP (s : ℝ) (hs : 0 < s) : |P s| ≤ A * s ^ 2 := by
    change |s * leftMultiplier a z s| ≤ _
    rw [abs_mul, abs_of_pos hs, mul_comm s, pow_two]
    exact (mul_le_mul_of_nonneg_right (leftMultiplier_abs_le a z hs) hs.le).trans_eq (mul_assoc _ _ _)
  have hZ : Tendsto (P * β) (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have ht : Tendsto (fun s : ℝ => A * s ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have hc : Continuous (fun s : ℝ => A * s ^ 2) := by fun_prop
      simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero] using
        (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left
          (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    refine squeeze_zero' (Eventually.of_forall fun s => norm_nonneg _) ?_ ht
    filter_upwards [self_mem_nhdsWithin] with s hs
    obtain ⟨hb₀, hb₁⟩ := BoseShape.expTail_bounds hs
    rw [Pi.mul_apply, norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg hb₀]
    exact (mul_le_of_le_one_right (abs_nonneg _) hb₁).trans (hP s hs)
  have hI : Tendsto (P * β) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    let D := 1 - Real.exp (-1)
    have hd : 0 < D := expHead_den_pos zero_lt_one
    have ht := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).const_mul (A / D)
    simp only [mul_zero] at ht
    refine squeeze_zero' (Eventually.of_forall fun s => norm_nonneg _) ?_ ht
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    have hs₀ := zero_lt_one.trans_le hs
    have hDen : D ≤ 1 - Real.exp (-s) :=
      sub_le_sub_left (Real.exp_le_exp.mpr (neg_le_neg hs)) _
    have hb : β s ≤ s * Real.exp (-s) / D := by
      change expTailFactor s ≤ _
      rw [BoseShape.expTail_eq_decay hs₀]
      exact div_le_div_of_nonneg_left (by positivity) hd hDen
    rw [Pi.mul_apply, norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (BoseShape.expTail_bounds hs₀).1]
    calc
      _ ≤ A * s ^ 2 * (s * Real.exp (-s) / D) :=
        mul_le_mul (hP s hs₀) hb (BoseShape.expTail_bounds hs₀).1 (by positivity)
      _ = _ := by ring
  let f (s : ℝ) := s ^ (1 : ℕ) * Real.exp (-s * 1)
  let g (s : ℝ) := s ^ (2 : ℕ) * (Real.exp (-s * (2 : ℕ)) / (1 - Real.exp (-s)))
  let h (s : ℝ) := s ^ (2 : ℕ) * (Real.exp (-s * (1 : ℕ)) / (1 - Real.exp (-s)))
  let k (s : ℝ) := s ^ (3 : ℕ) * (Real.exp (-s * (2 : ℕ)) / (1 - Real.exp (-s)))
  let μ := volume.restrict (Ioi (0 : ℝ))
  have hf : Integrable f μ := expMoment_nat_integrable 1 zero_lt_one
  have hg : Integrable g μ := boseMoment_nat_integrable (by decide : 0 < 2) (by decide : 0 < 2)
  have hh : Integrable h μ := boseMoment_nat_integrable (by decide : 0 < 2) (by decide : 0 < 1)
  have hk : Integrable k μ := boseMoment_nat_integrable (by decide : 0 < 3) (by decide : 0 < 2)
  have hE (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      (P' * β) s = 1 * f s + (1 - 2 * z) * g s - (2 * a) * h s - (-z) * k s := by
    simp only [Pi.mul_apply, P', f, g, h, k, β, BoseShape.expTail_eq_decay hs,
      Nat.cast_ofNat, Nat.cast_one, pow_one, mul_one, one_mul, show -s * (2 : ℝ) = -s + -s by ring,
      Real.exp_add]
    field_simp [(expHead_den_pos hs).ne']
    ring
  have hInt : IntegrableOn (P' * β) (Ioi 0) := by
    apply (((hf.const_mul 1).add (hg.const_mul (1 - 2 * z))).sub
      (hh.const_mul (2 * a)) |>.sub (hk.const_mul (-z))).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hE s hs).symm
  have hInt' : IntegrableOn (P * fun s => -BoseShape.C s) (Ioi 0) := by
    convert (reference_second_integrable a z).neg using 1
    ext s
    simp only [Pi.mul_apply, Pi.neg_apply, P]
    ring
  have hParts := integral_Ioi_mul_deriv_eq_deriv_mul (u := P) (u' := P')
    (v := β) (v' := fun s => -BoseShape.C s) (fun s _ => hD s)
    (fun s hs => BoseShape.expTail_derivative hs) hInt' hInt hZ hI
  have hV : (∫ s : ℝ in Ioi 0, s * leftMultiplier a z s * BoseShape.C s) =
      ∫ s : ℝ in Ioi 0, (P' * β) s := by
    simpa only [mul_neg, P, integral_neg, sub_zero, zero_sub, neg_inj, Pi.mul_apply] using hParts
  rw [hV, setIntegral_congr_fun measurableSet_Ioi hE,
    integral_four_terms hf hg hh hk]
  dsimp only [f, g, h, k, μ]
  rw [expMoment_nat_integral 1 zero_lt_one,
    boseMoment_nat_integral (by decide : 0 < 2) (by decide : 0 < 2),
    boseMoment_nat_integral (by decide : 0 < 2) (by decide : 0 < 1),
    boseMoment_nat_integral (by decide : 0 < 3) (by decide : 0 < 2)]
  norm_num [Nat.factorial]
  have h3 := powerTail_shift (q := 3) (by norm_num) 1
  have h4 := powerTail_shift (q := 4) (by norm_num) 1
  norm_num at h3 h4
  rw [h3, h4]
  ring

private theorem reference_triangle_le {a z s : ℝ} (ha : a ≤ 6 / 25) (haz : a + z ≤ 1)
    (hs : 0 < s) :
    leftMultiplier (6 / 25) (19 / 25) s ≤ leftMultiplier a z s := by
  unfold leftMultiplier
  have h₁ := mul_nonneg (sub_nonneg.mpr ha)
    (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.le)))
  have h₂ := mul_nonneg (show 0 ≤ 1 - (a + z) by linarith) (Real.exp_pos (-s)).le
  have h := mul_nonneg (add_nonneg h₁ h₂) hs.le
  nlinarith only [h]

private theorem reference_first_pos {a z : ℝ} (ha : a ≤ 6 / 25) (haz : a + z ≤ 1) :
    0 < ∫ s : ℝ in Ioi 0, s * leftMultiplier a z s * (s * Real.exp (-s)) := by
  refine lt_of_lt_of_le ?_ (integral_mono_ae (reference_first_integrable (6 / 25) (19 / 25))
    (reference_first_integrable a z) ?_)
  · rw [reference_first_eq]
    norm_num
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0 < s := hs
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (reference_triangle_le ha haz hs₀) hs₀.le) (by positivity)

private theorem reference_second_pos {a z : ℝ} (ha : a ≤ 6 / 25) (haz : a + z ≤ 1) :
    0 < ∫ s : ℝ in Ioi 0, s * leftMultiplier a z s * BoseShape.C s := by
  refine lt_of_lt_of_le ?_ (integral_mono_ae (reference_second_integrable (6 / 25) (19 / 25))
    (reference_second_integrable a z) ?_)
  · rw [reference_second_eq]
    linarith only [powerTail_three_lt, powerTail_four_gt]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0 < s := hs
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (reference_triangle_le ha haz hs₀) hs₀.le) (BoseShape.C_pos hs₀).le

private theorem leftMoment_transfer {p L a z : ℝ} {g : ℝ → ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (ha : 0 < a) (ha' : a ≤ 6 / 25) (hz : 0 ≤ z) (haz : a + z ≤ 1)
    (hg : ∀ s > 0, 0 ≤ g s)
    (hRef : IntegrableOn (fun s => s * leftMultiplier a z s * g s) (Ioi 0))
    (hActual : IntegrableOn (fun s => imageDensity p L s * leftMultiplier a z s * g s) (Ioi 0))
    (hPos : 0 < ∫ s : ℝ in Ioi 0, s * leftMultiplier a z s * g s) :
    0 < ∫ s : ℝ in Ioi 0, imageDensity p L s * leftMultiplier a z s * g s := by
  obtain ⟨c, hc, hBefore, _, hAfter⟩ := leftMultiplier_one_cut ha (by linarith) hz haz
  have hEq (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      (s * leftMultiplier a z s * g s) * (imageDensity p L s / s) =
        imageDensity p L s * leftMultiplier a z s * g s := by
    field_simp [(mem_Ioi.mp hs).ne']
  have hW := hActual.congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hEq s hs).symm)
  rw [← setIntegral_congr_fun measurableSet_Ioi hEq]
  exact positive_integral_of_one_cut hc hRef hW
    (fun s hs => mul_nonneg (mul_nonneg hs.1.le (hBefore s hs).le) (hg s hs.1))
    (fun s hs => mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (hc.trans hs).le (hAfter s hs).le) (hg s (hc.trans hs)))
    (imageDensity_div_antitone hp hp₂ hL) (div_pos (imageDensity_pos hp hL hc) hc) hPos

theorem actual_left_moments {p L a z : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2) (hL : 0 < L)
    (ha : 0 < a) (ha' : a ≤ 6 / 25) (hz : 0 ≤ z) (haz : a + z ≤ 1) :
    (0 < ∫ s : ℝ in Ioi 0, imageDensity p L s * leftMultiplier a z s * (s * Real.exp (-s))) ∧
    (0 < ∫ s : ℝ in Ioi 0, imageDensity p L s * leftMultiplier a z s * BoseShape.C s) := by
  obtain ⟨B, _, hB⟩ := imageDensity_linear_bound hp hp₂ hL
  have hW := (continuous_imageDensity hp hL).measurable
  have hBW (s : ℝ) (hs : 0 < s) : |imageDensity p L s| ≤ B * s := by
    rw [abs_of_pos (imageDensity_pos hp hL hs)]
    exact hB s hs
  constructor
  · apply leftMoment_transfer hp hp₂ hL ha ha' hz haz
      (fun s hs => mul_nonneg hs.le (Real.exp_pos _).le) (reference_first_integrable a z)
    · refine integrable_leftMoment (D := 1) zero_lt_one hW (by fun_prop) hBW ?_ a z
      intro s hs
      rw [abs_of_nonneg (mul_nonneg hs.le (Real.exp_pos _).le), mul_one, one_mul]
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    · exact reference_first_pos ha' haz
  · apply leftMoment_transfer hp hp₂ hL ha ha' hz haz (fun s hs => (BoseShape.C_pos hs).le)
      (reference_second_integrable a z)
    · refine integrable_leftMoment (D := BoseShape.decayConstant) zero_lt_one hW
        (by unfold BoseShape.C; fun_prop) hBW ?_ a z
      intro s hs
      rw [abs_of_pos (BoseShape.C_pos hs), mul_one]
      exact BoseShape.C_le_decay hs
    · exact reference_second_pos ha' haz

end ACS12.GammaMeasure


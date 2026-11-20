import ACS12.MiddleCovector
import ACS12.ConvexRightSampling
import ACS12.PowerSine
import ACS12.WeightedPositivePart

/-! The whole positive-part receiver of the original signed right kernel. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter

noncomputable def rightMultiplier (a z s : ℝ) : ℝ :=
  z + a * Real.exp (-s) - (1 - Real.exp (-s)) / s

theorem rightMultiplier_bound (a z : ℝ) {s : ℝ} (hs : 0 < s) :
    |rightMultiplier a z s| ≤ |z| + |a| + 1 := by
  have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.le)
  have h₀ : 0 ≤ (1 - Real.exp (-s)) / s := div_nonneg (sub_nonneg.mpr he) hs.le
  have h₁ : (1 - Real.exp (-s)) / s ≤ 1 := by
    apply (div_le_one hs).mpr
    linarith [Real.add_one_le_exp (-s)]
  unfold rightMultiplier
  apply (abs_sub _ _).trans
  rw [abs_of_nonneg h₀]
  apply add_le_add _ h₁
  refine (show |z + a * Real.exp (-s)| ≤ |z| + |a * Real.exp (-s)| by
    simpa only [Real.norm_eq_abs] using norm_add_le z (a * Real.exp (-s))).trans ?_
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  exact add_le_add le_rfl (mul_le_of_le_one_right (abs_nonneg _) he)

theorem rightMultiplier_mono {a z : ℝ} (ha : a ≤ 1 / 2) :
    MonotoneOn (rightMultiplier a z) (Ioi 0) := by
  have hd (s : ℝ) (hs : 0 < s) : HasDerivAt (rightMultiplier a z)
      (Real.exp (-s) * ((Real.exp s - 1 - s) / s ^ 2 - a)) s := by
    have he := (hasDerivAt_neg s).exp
    have h := ((he.const_mul a).const_add z).sub ((he.const_sub 1).div (hasDerivAt_id s) hs.ne')
    convert h using 1
    simp only [id_eq]
    have hE : Real.exp (-s) * Real.exp s = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    field_simp [hs.ne']
    linear_combination hE
  apply monotoneOn_of_deriv_nonneg (convex_Ioi _)
  · intro s hs
    exact (hd s hs).continuousAt.continuousWithinAt
  · intro s hs
    have hs₀ : 0 < s := by simpa only [interior_Ioi, mem_Ioi] using hs
    exact (hd s hs₀).differentiableAt.differentiableWithinAt
  · intro s hs
    have hs₀ : 0 < s := by simpa only [interior_Ioi, mem_Ioi] using hs
    rw [(hd s hs₀).deriv]
    apply mul_nonneg (Real.exp_pos _).le
    apply sub_nonneg.mpr
    apply ha.trans
    apply (le_div_iff₀ (sq_pos_of_pos hs₀)).mpr
    linarith [Real.quadratic_le_exp_of_nonneg hs₀.le]

noncomputable def rightWeight (p L t s : ℝ) : ℝ :=
  imageDensity p L s * s * Real.exp (-s * t)

private theorem rightWeight_pos {p L t s : ℝ} (hp : 0 < p) (hL : 0 < L) (hs : 0 < s) :
    0 < rightWeight p L t s := mul_pos (mul_pos (imageDensity_pos hp hL hs) hs) (Real.exp_pos _)

private theorem rightWeight_mul_integrable {p L t : ℝ} (hp : 0 < p) (hL : 0 < L) (ht : 0 < t)
    (a z : ℝ) :
    IntegrableOn (fun s => rightWeight p L t s * rightMultiplier a z s) (Ioi 0) := by
  have hW := imageSlope_integrable hp hL ht
  have hM : Measurable (rightMultiplier a z) := by unfold rightMultiplier; fun_prop
  refine (hW.const_mul (|z| + |a| + 1)).mono' (hW.aestronglyMeasurable.mul hM.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hP := (rightWeight_pos (t := t) hp hL (mem_Ioi.mp hs)).le
  rw [norm_mul, Real.norm_of_nonneg hP, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (rightMultiplier_bound a z hs) hP).trans_eq (mul_comm _ _)

theorem rightTest_eq_integral {p L t : ℝ} (hp : 0 < p) (hL : 0 < L) (ht : 0 < t)
    (a z : ℝ) :
    rightTest p L a z t = ∫ s : ℝ in Ioi 0, rightWeight p L t s * rightMultiplier a z s := by
  let f (s : ℝ) := imageDensity p L s * s * Real.exp (-s * t)
  let g (s : ℝ) := imageDensity p L s * s * Real.exp (-s * (t + 1))
  let h (s : ℝ) := imageDensity p L s * Real.exp (-s * t)
  let k (s : ℝ) := imageDensity p L s * Real.exp (-s * (t + 1))
  have hf := imageSlope_integrable hp hL ht
  have hg := imageSlope_integrable hp hL (show 0 < t + 1 by positivity)
  have hh := imagePotential_integrable hp hL ht
  have hk := imagePotential_integrable hp hL (show 0 < t + 1 by positivity)
  have hPoint (s : ℝ) (hs : 0 < s) :
      z * f s + a * g s - h s + k s = rightWeight p L t s * rightMultiplier a z s := by
    dsimp only [f, g, h, k, rightWeight, rightMultiplier]
    rw [show -s * (t + 1) = -s * t + -s by ring, Real.exp_add]
    field_simp [hs.ne']
    ring
  have hI : (∫ s : ℝ in Ioi 0, z * f s + a * g s - h s + k s) =
      ∫ s : ℝ in Ioi 0, rightWeight p L t s * rightMultiplier a z s :=
    setIntegral_congr_fun measurableSet_Ioi hPoint
  have hCalc := integral_four_terms (μ := volume.restrict (Ioi (0 : ℝ))) hf hg hh hk z a 1 (-1)
  simp only [one_mul, neg_one_mul, sub_neg_eq_add] at hCalc
  exact hCalc.symm.trans hI

noncomputable def rightClip (p L a z t : ℝ) : ℝ := max 0 (rightTest p L a z t)

private theorem rightWeight_tilt (p L t x s : ℝ) :
    rightWeight p L t s * Real.exp (s * (t - x)) = rightWeight p L x s := by
  rw [rightWeight, mul_assoc, ← Real.exp_add,
    show -s * t + s * (t - x) = -s * x by ring]
  rfl

theorem rightClip_antitone {p L a z : ℝ} (hp : 0 < p) (hL : 0 < L) (ha : a ≤ 1 / 2) :
    AntitoneOn (rightClip p L a z) (Ioi 0) :=
  weightedPositivePart_antitone (fun _ ht => imageSlope_integrable hp hL ht)
    (fun _ ht => rightWeight_mul_integrable hp hL ht a z)
    (fun _ ht => rightTest_eq_integral hp hL ht a z)
    (fun _ _ hs => rightWeight_pos hp hL hs) (rightWeight_tilt p L) (rightMultiplier_mono ha)

theorem rightClip_convex {p L a z : ℝ} (hp : 0 < p) (hL : 0 < L) (ha : a ≤ 1 / 2) :
    ConvexOn ℝ (Ioi 0) (rightClip p L a z) :=
  weightedPositivePart_convex (fun _ ht => imageSlope_integrable hp hL ht)
    (fun _ ht => rightWeight_mul_integrable hp hL ht a z)
    (fun _ ht => rightTest_eq_integral hp hL ht a z)
    (fun _ _ hs => rightWeight_pos hp hL hs) (rightWeight_tilt p L) (rightMultiplier_mono ha)

theorem rightClip_quadratureData {p L a z d : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (ha : a ≤ 1 / 2) (hd : 0 < d) :
    QuadratureData (rightClip p L a z) d := by
  obtain ⟨C, hC, hBound⟩ := imageDensity_linear_bound hp hp₂ hL
  let B := |z| + |a| + 1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  apply convex_right_quadratureData (C := B * C * 2)
    (rightClip_convex hp hL ha) (fun t _ => le_max_left 0 _) (by positivity) _ hd
  intro t ht
  have hJ := GammaDeficit.integrable_gamma_exp (a := 3) (by norm_num) ht
  have hJ' : IntegrableOn (fun s : ℝ => s ^ 2 * Real.exp (-s * t)) (Ioi 0) := by
    simpa only [show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_two, neg_mul, mul_comm t] using hJ
  have hCmp : |rightTest p L a z t| ≤ B * C * 2 / t ^ 3 := by
    rw [rightTest_eq_integral hp hL ht, ← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hM := (rightWeight_mul_integrable hp hL ht a z).norm
    have hN := hJ'.const_mul (B * C)
    refine (integral_mono_ae hM hN ?_).trans_eq ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      change 0 < s at hs
      rw [norm_mul, Real.norm_of_nonneg (rightWeight_pos (t := t) hp hL hs).le,
        Real.norm_eq_abs]
      calc
        rightWeight p L t s * |rightMultiplier a z s| ≤ rightWeight p L t s * B :=
          mul_le_mul_of_nonneg_left (rightMultiplier_bound a z hs) (rightWeight_pos hp hL hs).le
        _ ≤ (C * s * s * Real.exp (-s * t)) * B := by
          unfold rightWeight
          gcongr
          exact hBound s hs
        _ = B * C * (s ^ 2 * Real.exp (-s * t)) := by ring
    · rw [integral_const_mul]
      have hEq := GammaDeficit.gamma_exp_integral (a := 3) (by norm_num) ht
      have hGam : Real.Gamma 3 = 2 := by
        convert Real.Gamma_nat_eq_factorial 2 using 1 <;> norm_num
      have hPow : t ^ (-(3 : ℝ)) = (t ^ (3 : ℕ))⁻¹ := by
        rw [Real.rpow_neg ht.le, ← Real.rpow_natCast]
        norm_num
      rw [hGam, show (3 : ℝ) - 1 = 2 by norm_num, hPow] at hEq
      have hEq' : (∫ s : ℝ in Ioi 0, s ^ 2 * Real.exp (-s * t)) = 2 * (t ^ 3)⁻¹ := by
        simpa only [Real.rpow_two, neg_mul, mul_comm t] using hEq
      rw [hEq']
      ring
  exact max_le (by positivity) ((le_abs_self _).trans hCmp)

end ACS12.GammaMeasure

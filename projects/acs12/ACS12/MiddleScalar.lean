import ACS12.LeftPacking

/-! The original scalar receiver, including both complete exterior rays. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open scoped Topology

noncomputable def middleA (u : ℝ) : ℝ := (6 / 25) * u * (2 - u)
noncomputable def middleZ (u : ℝ) : ℝ := u - middleA u
noncomputable def unitSlopeTotal (p L : ℝ) : ℝ := samplingTail (imageSlope p L) 0 1

theorem middleA_pos {u : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) : 0 < middleA u := by
  unfold middleA
  exact mul_pos (mul_pos (by norm_num) hu) (by linarith)

theorem middleA_le (u : ℝ) : middleA u ≤ 6 / 25 := by
  unfold middleA
  nlinarith only [sq_nonneg (1 - u)]

theorem middleZ_nonneg {u : ℝ} (hu : 0 < u) : 0 ≤ middleZ u := by
  unfold middleZ middleA
  nlinarith only [hu, sq_nonneg u]

private theorem unitSlopeTotal_eq {p L : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2) (hL : 0 < L) :
    IntegrableOn (fun s => imageDensity p L s * s * scaledExpTail s 1) (Ioi 0) ∧
      unitSlopeTotal p L = ∫ s : ℝ in Ioi 0, imageDensity p L s * s * scaledExpTail s 1 := by
  let g (s : ℝ) := imageDensity p L s * s
  obtain ⟨B, _, hB⟩ := imageDensity_linear_bound hp hp₂ hL
  have hg : Measurable g := (continuous_imageDensity hp hL).measurable.mul measurable_id
  have hG (s : ℝ) (hs : 0 < s) : |g s| ≤ B * s ^ 2 := by
    rw [abs_of_nonneg (mul_nonneg (imageDensity_pos hp hL hs).le hs.le), pow_two, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hB s hs) hs.le
  have h := signedTail_sampling (t := 0) hg hG le_rfl zero_lt_one
  simpa only [unitSlopeTotal, signedLaplace, imageSlope, g, mul_zero, Real.exp_zero, mul_one] using h

private theorem left_unit_sum {p L a z : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2) (hL : 0 < L) :
    samplingTail (leftTest p L a z) 0 1 =
      imagePotential p L 1 - (a + z) * unitSlopeTotal p L + z * imageSlope p L 1 := by
  obtain ⟨B, _, hB⟩ := leftDensity_bound hp hp₂ hL a z
  obtain ⟨_, hSum⟩ := signedTail_sampling (t := 0) (leftDensity_measurable hp hL a z) hB
    le_rfl zero_lt_one
  have hTail : samplingTail (leftTest p L a z) 0 1 =
      samplingTail (signedLaplace (leftDensity p L a z)) 0 1 := by
    unfold samplingTail
    apply congrArg (1 * ·)
    apply tsum_congr
    intro j
    exact leftTest_eq_signedLaplace hp hL (by positivity) a z
  rw [hTail, hSum]
  simp only [mul_zero, Real.exp_zero, mul_one]
  obtain ⟨hZ, hZE⟩ := unitSlopeTotal_eq hp hp₂ hL
  have hPot := imagePotential_integrable hp hL zero_lt_one
  have hSl := imageSlope_integrable hp hL zero_lt_one
  have hPoint (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      leftDensity p L a z s * scaledExpTail s 1 =
        imageDensity p L s * Real.exp (-s) - (a + z) * (imageDensity p L s * s * scaledExpTail s 1) +
        z * (imageDensity p L s * s * Real.exp (-s)) := by
    have hBose : (1 - Real.exp (-s)) * scaledExpTail s 1 = Real.exp (-s) := by
      have he : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      unfold scaledExpTail
      field_simp [(expTail_den_pos hs).ne']
      nlinarith only [he]
    unfold leftDensity leftMultiplier
    linear_combination imageDensity p L s * (1 + z * s) * hBose
  rw [setIntegral_congr_fun measurableSet_Ioi hPoint]
  have hP : IntegrableOn (fun s => imageDensity p L s * Real.exp (-s)) (Ioi 0) := by
    simpa only [mul_one] using hPot
  have hS : IntegrableOn (fun s => imageDensity p L s * s * Real.exp (-s)) (Ioi 0) := by
    simpa only [mul_one] using hSl
  have hPZ : IntegrableOn (fun s => imageDensity p L s * Real.exp (-s) -
      (a + z) * (imageDensity p L s * s * scaledExpTail s 1)) (Ioi 0) := hP.sub (hZ.const_mul (a + z))
  rw [integral_add hPZ (hS.const_mul z),
    integral_sub hP (hZ.const_mul (a + z)), integral_const_mul, integral_const_mul, hZE,
    imagePotential, imageSlope]
  simp only [mul_one]

theorem unitSlopeTotal_gt_baseline {p L a : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2) (hL : 0 < L)
    (ha : a ≤ 6 / 25) :
    imagePotential p L 1 + a * imageSlope p L 1 < unitSlopeTotal p L := by
  obtain ⟨hZ, hZE⟩ := unitSlopeTotal_eq hp hp₂ hL
  have hP := imagePotential_integrable hp hL zero_lt_one
  have hS := imageSlope_integrable hp hL zero_lt_one
  letI : NeZero (volume.restrict (Ioi (0 : ℝ))) := ⟨positiveHalfLine_ne_zero⟩
  rw [hZE, imagePotential, imageSlope, ← integral_const_mul, ← integral_add hP (hS.const_mul a)]
  apply integral_strict_of_ae_lt _ (hP.add (hS.const_mul a)) hZ
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs₀ : 0 < s := hs
  have hBose : s * scaledExpTail s 1 = Real.exp (-s) * expHeadFactor s := by
    have hβ := BoseShape.expTail_eq_decay hs₀
    have hS : s * scaledExpTail s 1 = expTailFactor s := by
      rw [scaledExpTail_eq_factor hs₀, mul_one, mul_div_cancel₀ _ hs₀.ne']
    rw [hS, hβ, expHeadFactor]
    ring
  have h := BoseShape.expHeadFactor_gt_one_add_half hs₀
  have ha' : a * s ≤ s / 2 := by
    nlinarith only [mul_le_mul_of_nonneg_right ha hs₀.le, hs₀]
  have hlt := mul_lt_mul_of_pos_left (show 1 + a * s < expHeadFactor s by linarith)
    (mul_pos (imageDensity_pos hp hL hs₀) (Real.exp_pos (-s)))
  simp only [Pi.add_apply, mul_one]
  calc
    _ = imageDensity p L s * Real.exp (-s) * (1 + a * s) := by ring
    _ < imageDensity p L s * Real.exp (-s) * expHeadFactor s := hlt
    _ = imageDensity p L s * s * scaledExpTail s 1 := by
      rw [mul_assoc (imageDensity p L s) s (scaledExpTail s 1), hBose]
      ring

/-- P1510 AB1 with its original masses and all nonzero images. -/
theorem _root_.ACS12.Configuration.clipped_scalar_necessary {n : ℕ} {p : ℝ}
    (F : Configuration n p) (hn : 2 ≤ n) (hp : 0 < p) (hp₂ : p ≤ 2)
    (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi)) {j k : Fin n}
    (hj : C.source.IsNext C.source.neighbor j) (hk : C.source.IsNext j k)
    (hu₁ : C.source.forwardDistance C.source.neighbor j ≤ 1) :
    let S := C.source
    let L := S.period
    let u := S.forwardDistance S.neighbor j
    let v := S.forwardDistance j k
    let a := middleA u
    let z := middleZ u
    let b := S.mass S.neighbor
    let m := S.mass j
    let r := S.mass k
    0 ≤ b * (imagePotential p L 1 + a * imageSlope p L 1) - u * unitSlopeTotal p L +
      (b - 1) * imageSelf p L + m * rightTest p L a z u +
      samplingHead (rightClip p L a z) (u + v) r := by
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  let S := C.source
  let L := S.period
  let u := S.forwardDistance S.neighbor j
  let a := middleA u
  let z := middleZ u
  have hu : 0 < u := S.forwardDistance_pos _ _
  have hL : 0 < L := S.period_pos
  have ha := middleA_le u
  have haz : a + z = u := by change middleA u + (u - middleA u) = u; ring
  have hK := leftTest_quadratureData hp hp₂ hL (middleA_pos hu hu₁) ha
    (middleZ_nonneg hu) (haz.trans_le hu₁)
  have hK' : QuadratureData (leftTest p L a z) (S.mass S.root) := by
    rw [S.mass_root]
    exact hK
  have hLeft := S.backwardExterior_le_tail C.circular_caps S.root hK'
  rw [S.mass_root, left_unit_sum hp hp₂ hL] at hLeft
  have hRight := F.rightExterior_le_clipped hn hp hp₂ C hj hk a z (by linarith)
  have hRow := F.exact_middle_covector hp C a z
  change S.forwardExterior (rightTest p L a z) S.neighbor ≤
    S.mass j * rightTest p L a z u + samplingHead (rightClip p L a z)
      (u + S.forwardDistance j k) (S.mass k) at hRight
  change S.backwardExterior (leftTest p L a z) S.root +
    S.forwardExterior (rightTest p L a z) S.neighbor =
      (1 - S.mass S.neighbor) * (imagePotential p L 1 + imageSelf p L) -
        a * S.mass S.neighbor * imageSlope p L 1 + z * imageSlope p L 1 at hRow
  change 0 ≤ S.mass S.neighbor * (imagePotential p L 1 + a * imageSlope p L 1) -
    u * unitSlopeTotal p L + (S.mass S.neighbor - 1) * imageSelf p L +
      S.mass j * rightTest p L a z u +
      samplingHead (rightClip p L a z) (u + S.forwardDistance j k) (S.mass k)
  rw [haz] at hLeft
  nlinarith only [hLeft, hRight, hRow]

end ACS12.GammaMeasure


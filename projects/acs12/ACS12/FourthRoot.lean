import ACS12.BoseGrowth

/-! The original fourth source and its unique root on the complete spacing range. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter

noncomputable def fourthSourceRow (p L θ u v r m : ℝ) : ℝ :=
  let A := lawPeanoKernel p L θ v .a
  let B := lawPeanoKernel p L θ v .b
  u * B u + samplingTail B u 1 + samplingTail A 0 r -
    v * r * lawMoment p L θ 1 v + (m - r) * (lawMoment p L θ 0 v + lawSelf p L θ)

theorem lawSelf_nonneg {p L θ : ℝ} (hp : 0 < p) (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) :
    0 ≤ lawSelf p L θ := mul_nonneg hθ.1 (imageSelf_pos hp hL).le

theorem lawPeanoTail_nonneg {p L θ h t q : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hh : 0 < h) (ht : 0 ≤ t) (hq : 0 < q)
    (kind : CircleKernelKind) :
    0 ≤ samplingTail (lawPeanoKernel p L θ h kind) t q := by
  rw [(lawPeanoTail_sampling hp hp₂ hL hθ hh ht hq kind).2]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact mul_nonneg (mul_pos (lawPeanoDensity_pos (zero_lt_one.trans_le hp) hL hθ hh hs kind)
    (Real.exp_pos _)).le (div_pos hq (expTail_den_pos (mul_pos hs hq))).le

theorem scaledExpTail_strictAnti {s : ℝ} (hs : 0 < s) :
    StrictAntiOn (scaledExpTail s) (Ioi 0) := by
  intro r hr q hq hrq
  rw [scaledExpTail_eq_factor hs, scaledExpTail_eq_factor hs]
  exact div_lt_div_of_pos_right (strictAntiOn_expTailFactor
    (mul_pos hs hr) (mul_pos hs hq) (mul_lt_mul_of_pos_left hrq hs)) hs

theorem scaledExpTail_bridge {s q : ℝ} (hs : 0 < s) (hq : 0 < q) :
    Real.exp (-s * q) * (q + scaledExpTail s q) = scaledExpTail s q := by
  have hE : Real.exp (s * q) * Real.exp (-s * q) = 1 := by
    rw [← Real.exp_add, show s * q + -s * q = 0 by ring, Real.exp_zero]
  unfold scaledExpTail
  let D := Real.exp (s * q) - 1
  have hD : D ≠ 0 := (expTail_den_pos (mul_pos hs hq)).ne'
  have hQ : q + q / D = q * Real.exp (s * q) / D := by
    calc
      q + q / D = (q * D + q) / D := by rw [add_div, mul_div_cancel_right₀ _ hD]
      _ = q * Real.exp (s * q) / D := by congr 1; dsimp [D]; ring
  change Real.exp (-s * q) * (q + q / D) = q / D
  rw [hQ, ← mul_div_assoc]
  have h : Real.exp (-s * q) * (q * Real.exp (s * q)) = q := by
    calc
      _ = q * (Real.exp (s * q) * Real.exp (-s * q)) := by ring
      _ = _ := by rw [hE, mul_one]
  rw [h]

theorem fourthSourceRow_strictAnti {p L θ u v m : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hv : 0 < v) :
    StrictAntiOn (fun r => fourthSourceRow p L θ u v r m) (Ioi 0) := by
  intro r hr q hq hrq
  have hr₀ : 0 < r := hr
  have hq₀ : 0 < q := hq
  obtain ⟨hrI, hrE⟩ := lawPeanoTail_sampling hp hp₂ hL hθ hv (t := 0) le_rfl hr₀ .a
  obtain ⟨hqI, hqE⟩ := lawPeanoTail_sampling hp hp₂ hL hθ hv (t := 0) le_rfl hq₀ .a
  have hStream : samplingTail (lawPeanoKernel p L θ v .a) 0 q ≤
      samplingTail (lawPeanoKernel p L θ v .a) 0 r := by
    rw [hrE, hqE]
    apply integral_mono_ae hqI hrI
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_le_mul_of_nonneg_left ((scaledExpTail_strictAnti hs hr hq hrq).le)
      (mul_pos (lawPeanoDensity_pos (zero_lt_one.trans_le hp) hL hθ hv hs .a) (Real.exp_pos _)).le
  have hU := lawMoment_pos hp hp₂ hL hθ hv 1
  have hD := add_pos_of_pos_of_nonneg (lawMoment_pos hp hp₂ hL hθ hv 0)
    (lawSelf_nonneg (zero_lt_one.trans_le hp) hL hθ)
  have hSlope := mul_lt_mul_of_pos_right hrq (mul_pos hv hU)
  have hMass := mul_le_mul_of_nonneg_right (sub_le_sub_left hrq.le m) hD.le
  change fourthSourceRow p L θ u v q m < fourthSourceRow p L θ u v r m
  unfold fourthSourceRow
  nlinarith only [hStream, hSlope, hMass]

theorem fourthSourceRow_continuousOn {p L θ u v m : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hv : 0 < v) :
    ContinuousOn (fun r => fourthSourceRow p L θ u v r m) (Ioi 0) := by
  intro r hr
  have hA := (lawPeanoTail_derivative hp hp₂ hL hθ hv (t := 0) le_rfl hr .a).continuousAt
  have hP : ContinuousAt (fun q : ℝ => v * q * lawMoment p L θ 1 v) r := by fun_prop
  have hM : ContinuousAt (fun q : ℝ => (m - q) *
      (lawMoment p L θ 0 v + lawSelf p L θ)) r := by fun_prop
  exact (((hA.const_add _).sub hP).add hM).continuousWithinAt

theorem fourthSourceRow_at_equal_spacing_neg {p L θ u v m : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hv : 0 < v) (hvu : v ≤ u) (hu₁ : u < 1)
    (hmv : m ≤ v) :
    fourthSourceRow p L θ u v v m < 0 := by
  have hu := hv.trans_le hvu
  have hp₀ := zero_lt_one.trans_le hp
  let w := lawDensity p L θ
  let f (s : ℝ) := lawPeanoDensity p L θ v .b s * Real.exp (-s * u)
  let g (s : ℝ) := f s * scaledExpTail s 1
  let h (s : ℝ) := lawPeanoDensity p L θ v .a s * scaledExpTail s v
  let k (s : ℝ) := w s * s * Real.exp (-s * v)
  let μ := volume.restrict (Ioi (0 : ℝ))
  have hf : Integrable f μ := lawPeanoKernel_integrable hp hp₂ hL hθ hv hu .b
  obtain ⟨hg, hgE⟩ := lawPeanoTail_sampling hp hp₂ hL hθ hv hu.le zero_lt_one .b
  obtain ⟨hh, hhE⟩ := lawPeanoTail_sampling hp hp₂ hL hθ hv (t := 0) le_rfl hv .a
  simp only [mul_zero, Real.exp_zero, mul_one] at hh hhE
  have hgI : Integrable g μ := hg
  have hhI : Integrable h μ := hh
  have hk : Integrable k μ := by simpa only [pow_one] using lawMoment_integrable hp hp₂ hL hθ hv 1
  have hI : Integrable (fun s => u * f s + g s + h s - (v * v) * k s) μ :=
    (((hf.const_mul u).add hgI).add hhI).sub (hk.const_mul (v * v))
  have hEq : fourthSourceRow p L θ u v v m =
      (∫ s : ℝ in Ioi 0, u * f s + g s + h s - (v * v) * k s) +
      (m - v) * (lawMoment p L θ 0 v + lawSelf p L θ) := by
    have hE := integral_four_terms hf hgI hhI hk u 1 (-1) (v * v)
    simp only [one_mul, neg_one_mul, sub_neg_eq_add] at hE
    rw [hE, fourthSourceRow, hgE, hhE, lawPeanoKernel, signedLaplace]
    simp only [f, g, h, k, lawMoment, pow_one, w, μ]
  have hPoint (s : ℝ) (hs : 0 < s) :
      u * f s + g s + h s - (v * v) * k s =
        w s * polyB (v * s) * (Real.exp (-s * u) * (u + scaledExpTail s 1) - scaledExpTail s v) := by
    have hBridge := scaledExpTail_bridge hs hv
    have hPoly : polyA (v * s) + polyB (v * s) = v * s * (1 - Real.exp (-s * v)) := by
      simp only [polyA, polyB, show -(v * s) = -s * v by ring]
      ring
    have hTotal : (polyA (v * s) + polyB (v * s)) * scaledExpTail s v =
        v * v * s * Real.exp (-s * v) := by
      rw [hPoly]
      linear_combination -(v * s) * hBridge
    simp only [f, g, h, k, lawPeanoDensity, densityPolynomial, w]
    linear_combination lawDensity p L θ s * hTotal
  have hN : (∫ s : ℝ in Ioi 0, u * f s + g s + h s - (v * v) * k s) < 0 := by
    letI : NeZero μ := ⟨positiveHalfLine_ne_zero⟩
    have h := integral_strict_of_ae_lt μ hI (integrable_zero ℝ ℝ μ) ?_
    · simpa only [integral_zero] using h
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs₀ : 0 < s := hs
      rw [hPoint s hs₀]
      have hT : Real.exp (-s * u) * (u + scaledExpTail s 1) < scaledExpTail s v := by
        calc
          _ < Real.exp (-s * u) * (u + scaledExpTail s u) :=
            mul_lt_mul_of_pos_left (add_lt_add_right (scaledExpTail_strictAnti hs₀ hu (mem_Ioi.mpr zero_lt_one) hu₁) _) (Real.exp_pos _)
          _ = scaledExpTail s u := scaledExpTail_bridge hs₀ hu
          _ ≤ _ := (scaledExpTail_strictAnti hs₀).antitoneOn hv hu hvu
      exact mul_neg_of_pos_of_neg (mul_pos (lawDensity_pos hp₀ hL hθ hs₀)
        (polyB_pos (mul_pos hv hs₀))) (sub_neg.mpr hT)
  rw [hEq]
  exact add_neg_of_neg_of_nonpos hN (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hmv)
    (add_nonneg (lawMoment_pos hp hp₂ hL hθ hv 0).le (lawSelf_nonneg hp₀ hL hθ)))

theorem exists_fourthSource_root {p L θ u v m : ℝ} (hp : 1 ≤ p) (hp₂ : p < 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hv : 0 < v) (hvu : v ≤ u) (hu₁ : u < 1)
    (hm : 0 ≤ m) (hmv : m ≤ v) :
    ∃ r ∈ Ioo 0 v, fourthSourceRow p L θ u v r m = 0 ∧
      ∀ q > 0, 0 ≤ fourthSourceRow p L θ u v q m → q ≤ r := by
  let H (r : ℝ) := fourthSourceRow p L θ u v r m
  let U := lawMoment p L θ 1 v
  let D := lawMoment p L θ 0 v + lawSelf p L θ
  have hu := hv.trans_le hvu
  have hU : 0 < U := lawMoment_pos hp hp₂.le hL hθ hv 1
  have hD : 0 < D := add_pos_of_pos_of_nonneg (lawMoment_pos hp hp₂.le hL hθ hv 0)
    (lawSelf_nonneg (zero_lt_one.trans_le hp) hL hθ)
  obtain ⟨r₀, hr₀, hrBig⟩ := lawPeanoTail_unbounded_at_small_step hp hp₂ hL hθ hv hv
    (v * v * U + v * D)
  have hPos : 0 < H r₀ := by
    have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr₀.2.le hv.le) hU.le
    have h2 := mul_le_mul_of_nonneg_right (show -v ≤ m - r₀ by linarith [hr₀.2]) hD.le
    have hB := mul_nonneg hu.le (lawPeanoKernel_pos hp hp₂.le hL hθ hv hu .b).le
    have hT := lawPeanoTail_nonneg hp hp₂.le hL hθ hv hu.le zero_lt_one .b
    change 0 < u * lawPeanoKernel p L θ v .b u + samplingTail (lawPeanoKernel p L θ v .b) u 1 +
      samplingTail (lawPeanoKernel p L θ v .a) 0 r₀ - v * r₀ * U + (m - r₀) * D
    linarith only [h1, h2, hB, hT, hrBig]
  have hNeg : H v < 0 := fourthSourceRow_at_equal_spacing_neg hp hp₂.le hL hθ hv hvu hu₁ hmv
  have hCont : ContinuousOn H (Icc r₀ v) :=
    (fourthSourceRow_continuousOn hp hp₂.le hL hθ hv).mono (fun _ h => hr₀.1.trans_le h.1)
  obtain ⟨r, hr, he⟩ := intermediate_value_Icc' hr₀.2.le hCont ⟨hNeg.le, hPos.le⟩
  have hrP := hr₀.1.trans_le hr.1
  have hrv : r < v := lt_of_le_of_ne hr.2 (fun hv' => hNeg.ne (hv' ▸ he))
  refine ⟨r, ⟨hrP, hrv⟩, he, ?_⟩
  intro q hq hQ
  apply le_of_not_gt
  intro h
  have hStrict := fourthSourceRow_strictAnti (u := u) (m := m) hp hp₂.le hL hθ hv hrP hq h
  exact (lt_of_lt_of_le hStrict he.le).not_ge hQ

/-- The original occupied fourth row licenses the same comparison law at θ = 1. -/
theorem _root_.ACS12.Configuration.fourthSource_nonneg {n : ℕ} {p : ℝ} (F : Configuration n p)
    (hn : 2 ≤ n) (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi)) {j k : Fin n}
    (hj : C.source.IsNext C.source.neighbor j) (hk : C.source.IsNext j k) :
    let S := C.source
    0 ≤ fourthSourceRow p S.period 1 (S.forwardDistance S.neighbor j)
      (S.forwardDistance j k) (S.mass k) (S.mass j) := by
  let S := C.source
  let L := S.period
  let u := S.forwardDistance S.neighbor j
  let v := S.forwardDistance j k
  let b := S.mass S.neighbor
  let m := S.mass j
  let r := S.mass k
  let A := peanoKernel p L v .a
  let B := peanoKernel p L v .b
  let D := imagePotential p L v + imageSelf p L
  have hp₀ := zero_lt_one.trans_le hp
  have hL : 0 < L := S.period_pos
  have hu : 0 < u := S.forwardDistance_pos _ _
  have hv : 0 < v := S.forwardDistance_pos _ _
  have hB := lawPeanoKernel_pos (θ := 1) hp hp₂ hL ⟨zero_le_one, le_rfl⟩ hv hu .b
  rw [lawPeanoKernel_one] at hB
  have hb : b ≤ u := (S.forwardDistance_caps C.circular_caps (fun he => (lt_irrefl _) (he ▸ hj.1))).1
  have hB' : b * B u ≤ u * B u := mul_le_mul_of_nonneg_right hb hB.le
  have hTail : samplingTail (fun x => B (x + u)) 0 1 = samplingTail B u 1 := by
    unfold samplingTail
    exact congrArg (1 * ·) (tsum_congr fun q => congrArg B (by ring))
  have h := F.fourth_source_necessary hn hp₀ hp₂ C hj hk
  change 0 ≤ b * B u + samplingTail (fun x => B (x + u)) 0 1 +
    samplingTail A 0 r - v * r * imageSlope p L v + (m - r) * D at h
  rw [hTail] at h
  change 0 ≤ fourthSourceRow p L 1 u v r m
  simp only [fourthSourceRow, lawPeanoKernel_one, lawMoment_one_radial, lawMoment_one_slope,
    lawSelf, one_mul]
  change 0 ≤ u * B u + samplingTail B u 1 + samplingTail A 0 r -
    v * r * imageSlope p L v + (m - r) * D
  linarith only [h, hB']

end ACS12.GammaMeasure


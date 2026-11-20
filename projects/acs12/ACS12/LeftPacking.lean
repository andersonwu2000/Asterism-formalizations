import ACS12.LeftMoments
import ACS12.SignedSampling
import ACS12.RightPacking

/-! Complete signed sampling on the original left exterior. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open scoped Topology

noncomputable def leftDensity (p L a z s : ℝ) : ℝ :=
  imageDensity p L s * leftMultiplier a z s

theorem leftDensity_measurable {p L : ℝ} (hp : 0 < p) (hL : 0 < L) (a z : ℝ) :
    Measurable (leftDensity p L a z) := by
  unfold leftDensity leftMultiplier
  exact (continuous_imageDensity hp hL).measurable.mul (by fun_prop)

theorem leftDensity_bound {p L : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2) (hL : 0 < L)
    (a z : ℝ) : ∃ B ≥ 0, ∀ s > 0, |leftDensity p L a z s| ≤ B * s ^ 2 := by
  obtain ⟨B, hB, h⟩ := imageDensity_linear_bound hp hp₂ hL
  refine ⟨B * (1 + |a| + |z|), by positivity, ?_⟩
  intro s hs
  rw [leftDensity, abs_mul, abs_of_pos (imageDensity_pos hp hL hs)]
  calc
    _ ≤ (B * s) * ((1 + |a| + |z|) * s) :=
      mul_le_mul (h s hs) (leftMultiplier_abs_le a z hs) (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem leftTest_eq_signedLaplace {p L t : ℝ} (hp : 0 < p) (hL : 0 < L)
    (ht : 0 < t) (a z : ℝ) :
    leftTest p L a z t = signedLaplace (leftDensity p L a z) t := by
  have h₁ := imagePotential_integrable hp hL ht
  have h₂ := imagePotential_integrable hp hL (show 0 < t + 1 by positivity)
  have h₃ := (imageSlope_integrable hp hL ht).const_mul a
  have h₄ := (imageSlope_integrable hp hL (show 0 < t + 1 by positivity)).const_mul z
  have h₁₂ : IntegrableOn (fun s => imageDensity p L s * Real.exp (-s * t) -
      imageDensity p L s * Real.exp (-s * (t + 1))) (Ioi 0) := h₁.sub h₂
  have h₁₂₃ : IntegrableOn (fun s => imageDensity p L s * Real.exp (-s * t) -
      imageDensity p L s * Real.exp (-s * (t + 1)) -
      a * (imageDensity p L s * s * Real.exp (-s * t))) (Ioi 0) := h₁₂.sub h₃
  unfold leftTest signedLaplace imagePotential imageSlope
  rw [← integral_const_mul, ← integral_const_mul, ← integral_sub h₁ h₂,
    ← integral_sub h₁₂ h₃, ← integral_sub h₁₂₃ h₄]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s _
  simp only [leftDensity, leftMultiplier, show -s * (t + 1) = -s * t + -s by ring, Real.exp_add]
  ring

private theorem leftTest_summable {p L t q : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2) (hL : 0 < L)
    (ht : 0 < t) (hq : 0 < q) (a z : ℝ) :
    Summable (fun j : ℕ => leftTest p L a z (t + j * q)) := by
  obtain ⟨B, _, hB⟩ := leftDensity_bound hp hp₂ hL a z
  have h := (hasSum_signedTail (t := t) (q := q)
    (leftDensity_measurable hp hL a z) hB ht.le hq).summable
  apply (summable_nat_add_iff 1).mp
  refine h.congr fun j => ?_
  have hPos : 0 < t + q + (j : ℝ) * q := by positivity
  rw [← leftTest_eq_signedLaplace hp hL hPos]
  push_cast
  congr 1
  ring

private theorem antitone_product {f g : ℝ → ℝ} (hf : AntitoneOn f (Ioi 0))
    (hg : AntitoneOn g (Ioi 0)) (hf₀ : ∀ s > 0, 0 ≤ f s) (hg₀ : ∀ s > 0, 0 ≤ g s) :
    AntitoneOn (fun s => f s * g s) (Ioi 0) := by
  intro x hx y hy hxy
  exact mul_le_mul (hf hx hy hxy) (hg hx hy hxy) (hg₀ y hy) (hf₀ x hx)

private theorem inverse_antitone : AntitoneOn (fun s : ℝ => s⁻¹) (Ioi 0) := by
  intro x hx y _ hxy
  exact inv_anti₀ hx hxy

private theorem C_div_antitone {q : ℝ} (hq : 0 < q) :
    AntitoneOn (fun s => BoseShape.C (s * q) / s) (Ioi 0) := by
  simp only [div_eq_mul_inv]
  exact antitone_product (fun x hx y hy hxy => BoseShape.C_antitone
    (mul_pos hx hq) (mul_pos hy hq) (mul_le_mul_of_nonneg_right hxy hq.le)) inverse_antitone
    (fun s hs => (BoseShape.C_pos (mul_pos hs hq)).le) (fun _ hs => (inv_pos.mpr hs).le)

private theorem E_div_antitone {q : ℝ} (hq : 0 < q) :
    AntitoneOn (fun s => BoseShape.E (s * q) / s) (Ioi 0) := by
  have hEq (s : ℝ) (hs : 0 < s) :
      BoseShape.E (s * q) / s = q * (BoseShape.E (s * q) / (s * q)) := by
    field_simp [hs.ne', hq.ne']
  intro x hx y hy hxy
  change BoseShape.E (y * q) / y ≤ BoseShape.E (x * q) / x
  rw [hEq x hx, hEq y hy]
  exact mul_le_mul_of_nonneg_left (BoseShape.E_div_antitone
    (mul_pos hx hq) (mul_pos hy hq) (mul_le_mul_of_nonneg_right hxy hq.le)) hq.le

private theorem leftTilt_pos {p L a z t : ℝ} {ψ : ℝ → ℝ} (hp : 0 < p) (hL : 0 < L)
    (ht : 1 ≤ t) (ha : 0 < a) (ha' : a ≤ 6 / 25) (hz : 0 ≤ z) (haz : a + z ≤ 1)
    (hψ : ∀ s > 0, 0 < ψ s) (hAnti : AntitoneOn (fun s => ψ s / s) (Ioi 0))
    (hI : IntegrableOn (fun s => leftDensity p L a z s * Real.exp (-s * t) * ψ s) (Ioi 0))
    (hFirst : 0 < ∫ s : ℝ in Ioi 0, leftDensity p L a z s * (s * Real.exp (-s))) :
    0 < ∫ s : ℝ in Ioi 0, leftDensity p L a z s * Real.exp (-s * t) * ψ s := by
  let f (s : ℝ) := leftDensity p L a z s * (s * Real.exp (-s))
  let g (s : ℝ) := Real.exp (-s * (t - 1)) * (ψ s / s)
  obtain ⟨c, hc, hBefore, _, hAfter⟩ := leftMultiplier_one_cut ha (by linarith) hz haz
  have hF : IntegrableOn f (Ioi 0) := Integrable.of_integral_ne_zero hFirst.ne'
  have hEq (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      f s * g s = leftDensity p L a z s * Real.exp (-s * t) * ψ s := by
    dsimp only [f, g]
    rw [show -s * t = -s + -s * (t - 1) by ring, Real.exp_add]
    field_simp [(mem_Ioi.mp hs).ne']
  have hG := hI.congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hEq s hs).symm)
  have hAntiG : AntitoneOn g (Ioi 0) := by
    refine antitone_product ?_ hAnti (fun s _ => (Real.exp_pos _).le)
      (fun s hs => (div_pos (hψ s hs) hs).le)
    intro x hx y hy hxy
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg hxy) (sub_nonneg.mpr ht)
  rw [← setIntegral_congr_fun measurableSet_Ioi hEq]
  exact positive_integral_of_one_cut hc hF hG
    (fun s hs => mul_nonneg (mul_nonneg (imageDensity_pos hp hL hs.1).le (hBefore s hs).le)
      (mul_nonneg hs.1.le (Real.exp_pos _).le))
    (fun s hs => mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (imageDensity_pos hp hL (hc.trans hs)).le (hAfter s hs).le)
      (by have hs₀ := hc.trans hs; positivity))
    hAntiG (mul_pos (Real.exp_pos _) (div_pos (hψ c hc) hc)) hFirst

private theorem leftTail_derivative {p L a z t q : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (ht : 0 ≤ t) (hq : 0 < q) :
    HasDerivAt (samplingTail (leftTest p L a z) t)
      (-(∫ s : ℝ in Ioi 0, leftDensity p L a z s * Real.exp (-s * t) * BoseShape.C (s * q))) q := by
  obtain ⟨B, _, hB⟩ := leftDensity_bound hp hp₂ hL a z
  apply (signedTail_derivative (leftDensity_measurable hp hL a z) hB ht hq).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hq] with r hr
  unfold samplingTail
  apply congrArg (r * ·)
  apply tsum_congr
  intro j
  have hj : 0 < ((j + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  exact leftTest_eq_signedLaplace hp hL (add_pos_of_nonneg_of_pos ht (mul_pos hj hr)) a z

private theorem scaledC_integrable {p L a z q : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hq : 0 < q) :
    IntegrableOn (fun s => leftDensity p L a z s * BoseShape.C (s * q)) (Ioi 0) := by
  obtain ⟨B, _, hB⟩ := imageDensity_linear_bound hp hp₂ hL
  refine integrable_leftMoment (B := B) (D := BoseShape.decayConstant * (q + 1)) hq
    (continuous_imageDensity hp hL).measurable (by unfold BoseShape.C; fun_prop) ?_ ?_ a z
  · intro s hs
    rw [abs_of_pos (imageDensity_pos hp hL hs)]
    exact hB s hs
  · intro s hs
    rw [abs_of_pos (BoseShape.C_pos (mul_pos hs hq))]
    refine (BoseShape.C_le_decay (mul_pos hs hq)).trans ?_
    simp only [neg_mul]
    have hArg : s * q + 1 ≤ (q + 1) * (s + 1) := by
      nlinarith only [hs, hq]
    calc
      _ ≤ BoseShape.decayConstant * ((q + 1) * (s + 1)) * Real.exp (-(s * q)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hArg BoseShape.decayConstant_pos.le)
          (Real.exp_pos _).le
      _ = _ := by ring

private theorem leftBoundary_pos {p L a z q : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hq : 1 ≤ q) (ha : 0 < a) (ha' : a ≤ 6 / 25) (hz : 0 ≤ z) (haz : a + z ≤ 1)
    (hSecond : 0 < ∫ s : ℝ in Ioi 0, leftDensity p L a z s * BoseShape.C s) :
    0 < ∫ s : ℝ in Ioi 0, leftDensity p L a z s * BoseShape.C (s * q) := by
  have hq₀ := zero_lt_one.trans_le hq
  obtain ⟨c, hc, hBefore, _, hAfter⟩ := leftMultiplier_one_cut ha (by linarith) hz haz
  let f (s : ℝ) := leftDensity p L a z s * BoseShape.C s
  let g (s : ℝ) := BoseShape.C (s * q) / BoseShape.C s
  have hEq (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      f s * g s = leftDensity p L a z s * BoseShape.C (s * q) := by
    dsimp only [f, g]
    field_simp [(BoseShape.C_pos hs).ne']
  have hG := (scaledC_integrable (a := a) (z := z) hp hp₂ hL hq₀).congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hEq s hs).symm)
  rw [← setIntegral_congr_fun measurableSet_Ioi hEq]
  exact positive_integral_of_one_cut hc (Integrable.of_integral_ne_zero hSecond.ne') hG
    (fun s hs => mul_nonneg (mul_nonneg (imageDensity_pos hp hL hs.1).le (hBefore s hs).le)
      (BoseShape.C_pos hs.1).le)
    (fun s hs => mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (imageDensity_pos hp hL (hc.trans hs)).le (hAfter s hs).le)
      (BoseShape.C_pos (hc.trans hs)).le)
    (by simpa only [g, mul_comm q] using BoseShape.C_ratio_antitone hq)
    (div_pos (BoseShape.C_pos (mul_pos hc hq₀)) (BoseShape.C_pos hc)) hSecond

theorem leftTest_quadratureData {p L a z : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2) (hL : 0 < L)
    (ha : 0 < a) (ha' : a ≤ 6 / 25) (hz : 0 ≤ z) (haz : a + z ≤ 1) :
    QuadratureData (leftTest p L a z) 1 := by
  let g := leftDensity p L a z
  let f := leftTest p L a z
  have ⟨hFirst, hSecond⟩ := actual_left_moments hp hp₂ hL ha ha' hz haz
  obtain ⟨B, _, hB⟩ := imageDensity_linear_bound hp hp₂ hL
  have hI (t : ℝ) (ht : 0 < t) (ψ : ℝ → ℝ) (hm : Measurable ψ)
      (hψ : ∀ s > 0, 0 ≤ ψ s ∧ ψ s ≤ 1) :
      IntegrableOn (fun s => g s * Real.exp (-s * t) * ψ s) (Ioi 0) := by
    have hW (s : ℝ) (hs : 0 < s) : |imageDensity p L s| ≤ B * s := by
      rw [abs_of_pos (imageDensity_pos hp hL hs)]
      exact hB s hs
    have h := integrable_leftMoment (D := 1) ht (continuous_imageDensity hp hL).measurable
      ((show Measurable (fun s : ℝ => Real.exp (-s * t)) by fun_prop).mul hm) hW ?_ a z
    · convert h using 1
      ext s
      simp only [g, leftDensity, mul_assoc]
    · intro s hs
      obtain ⟨hψ₀, hψ₁⟩ := hψ s hs
      rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg hψ₀, one_mul]
      have h := mul_le_of_le_one_right (Real.exp_pos (-s * t)).le hψ₁
      exact h.trans (le_mul_of_one_le_left (Real.exp_pos _).le (by linarith))
  have hC (q : ℝ) (hq : 0 < q) (s : ℝ) (hs : 0 < s) :
      0 ≤ BoseShape.C (s * q) ∧ BoseShape.C (s * q) ≤ 1 :=
    ⟨(BoseShape.C_pos (mul_pos hs hq)).le, (BoseShape.C_lt_one (mul_pos hs hq)).le⟩
  have hE (q : ℝ) (hq : 0 < q) (s : ℝ) (hs : 0 < s) :
      0 ≤ BoseShape.E (s * q) ∧ BoseShape.E (s * q) ≤ 1 :=
    ⟨(BoseShape.E_pos (mul_pos hs hq)).le, sub_le_self _ (hC q hq s hs).1⟩
  have hCInt (t : ℝ) (ht : 0 < t) (q : ℝ) (hq : 0 < q) :=
    hI t ht (fun s => BoseShape.C (s * q)) (by unfold BoseShape.C; fun_prop) (hC q hq)
  have hEInt (t : ℝ) (ht : 0 < t) (q : ℝ) (hq : 0 < q) :=
    hI t ht (fun s => BoseShape.E (s * q)) (by unfold BoseShape.E BoseShape.C; fun_prop) (hE q hq)
  have hFInt (t : ℝ) (ht : 0 < t) :
      IntegrableOn (fun s => g s * Real.exp (-s * t)) (Ioi 0) := by
    simpa only [mul_one] using hI t ht (fun _ => 1) measurable_const (fun _ _ => ⟨zero_le_one, le_rfl⟩)
  have hSum (t q : ℝ) (ht : 1 ≤ t) (hq : 0 < q) : Summable (fun j : ℕ => f (t + j * q)) :=
    leftTest_summable hp hp₂ hL (zero_lt_one.trans_le ht) hq a z
  have hHead (t q : ℝ) (ht : 1 ≤ t) (hq : 0 < q) :
      HasDerivAt (samplingHead f t)
        (∫ s : ℝ in Ioi 0, g s * Real.exp (-s * t) * BoseShape.E (s * q)) q := by
    have ht₀ := zero_lt_one.trans_le ht
    have h := ((hasDerivAt_id q).mul_const (f t)).add
      (leftTail_derivative (a := a) (z := z) hp hp₂ hL ht₀.le hq)
    have hEq : f t + -(∫ s : ℝ in Ioi 0, g s * Real.exp (-s * t) * BoseShape.C (s * q)) =
        ∫ s : ℝ in Ioi 0, g s * Real.exp (-s * t) * BoseShape.E (s * q) := by
      rw [show f t = signedLaplace g t from leftTest_eq_signedLaplace hp hL ht₀ a z,
        signedLaplace, ← sub_eq_add_neg, ← integral_sub (hFInt t ht₀) (hCInt t ht₀ q hq)]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s _
      unfold BoseShape.E
      ring
    have h' : HasDerivAt (fun r => r * f t + samplingTail f t r)
        (f t + -(∫ s : ℝ in Ioi 0, g s * Real.exp (-s * t) * BoseShape.C (s * q))) q := by
      simpa only [Pi.add_apply, id_eq, one_mul] using h
    rw [hEq] at h'
    apply h'.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hq] with r hr
    exact samplingHead_split f t r (hSum t r ht hr)
  refine ⟨?_, hSum, ?_, ?_, ?_⟩
  · intro t ht
    rw [leftTest_eq_signedLaplace hp hL (zero_lt_one.trans_le ht), signedLaplace]
    exact (by
      simpa only [mul_one] using leftTilt_pos hp hL ht ha ha' hz haz
        (ψ := fun _ => 1) (fun _ _ => zero_lt_one)
        (by simpa only [one_div] using inverse_antitone)
        (by simpa only [mul_one] using hFInt t (zero_lt_one.trans_le ht)) hFirst :
      0 < ∫ s : ℝ in Ioi 0, g s * Real.exp (-s * t)).le
  · intro t ht
    apply StrictMonoOn.monotoneOn
    apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
    · exact fun q hq => (hHead t q ht hq).continuousAt.continuousWithinAt
    · intro q hq
      have hq₀ : 0 < q := by simpa only [interior_Ioi, mem_Ioi] using hq
      rw [(hHead t q ht hq₀).deriv]
      exact leftTilt_pos hp hL ht ha ha' hz haz (fun s hs => BoseShape.E_pos (mul_pos hs hq₀))
        (E_div_antitone hq₀) (hEInt t (zero_lt_one.trans_le ht) q hq₀) hFirst
  · intro t ht
    have ht₀ := zero_lt_one.trans_le ht
    apply StrictAntiOn.antitoneOn
    apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
    · exact fun q hq => (leftTail_derivative hp hp₂ hL ht₀.le hq).continuousAt.continuousWithinAt
    · intro q hq
      have hq₀ : 0 < q := by simpa only [interior_Ioi, mem_Ioi] using hq
      rw [(leftTail_derivative hp hp₂ hL ht₀.le hq₀).deriv]
      exact neg_neg_of_pos (leftTilt_pos hp hL ht ha ha' hz haz
        (fun s hs => BoseShape.C_pos (mul_pos hs hq₀)) (C_div_antitone hq₀)
        (hCInt t ht₀ q hq₀) hFirst)
  · apply StrictAntiOn.antitoneOn
    apply strictAntiOn_of_deriv_neg (convex_Ici 1)
    · exact fun q hq => (leftTail_derivative hp hp₂ hL le_rfl
        (zero_lt_one.trans_le hq)).continuousAt.continuousWithinAt
    · intro q hq
      have hq₁ : 1 < q := by simpa only [interior_Ici, mem_Ioi] using hq
      rw [(leftTail_derivative hp hp₂ hL le_rfl (zero_lt_one.trans hq₁)).deriv]
      simp only [mul_zero, Real.exp_zero, mul_one]
      exact neg_neg_of_pos (leftBoundary_pos hp hp₂ hL hq₁.le ha ha' hz haz hSecond)

end ACS12.GammaMeasure


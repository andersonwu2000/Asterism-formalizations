import ACS12.JointFourthSecant

/-! The complete fourth-root bracket C5, with the image self mass paid once. -/
namespace ACS12.GammaMeasure
open CenteredCircle.AllN MeasureTheory Set Filter
open GammaDeficit (lineDensity signedDensity)

private theorem fourthSource_diag_deficit_le {p L θ u m : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hm : 0 < m) (hmu : m ≤ u) (hu₁ : u < 1)
    (hmL : 2 * u - 1 ≤ m) :
    -fourthSourceRow p L θ u m m m ≤ (1 - u) * m ^ (-p) *
      (1 + 2 * p + 2 * pureP p - pureQ p + (2 : ℝ) ^ (-p)) := by
  let w := lawDensity p L θ
  let B (s : ℝ) := polyB s * BoseShape.C s
  let E (s : ℝ) := polyB s * Real.exp (-s) * BoseShape.C s
  let F := fourthDensity u m m m
  let δ := 1 - u
  have hu := hm.trans_le hmu
  have hδ : 0 < δ := sub_pos.mpr hu₁
  have hp₂ : p < 2 := hP.trans_lt (by norm_num)
  have hB : (∫ s : ℝ in Ioi 0, lineDensity p s * B s) = 1 + pureP p := by
    simpa only [B, pureP, mul_assoc, Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one, zero_add,
      Nat.zero_add, Real.one_rpow, zero_mul, sub_zero] using pureBoseB_moment hp hp₂.le 0
  have hBI : IntegrableOn (fun s => lineDensity p s * B s) (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [hB]
    linarith only [pureP_nonneg hp]
  have hEI : IntegrableOn (fun s => lineDensity p s * E s) (Ioi 0) := by
    simpa only [E, mul_assoc] using shiftedBoseMoment_integrable hp hp₂.le
  have hEE : (∫ s : ℝ in Ioi 0, lineDensity p s * E s) =
      2 * p + pureP p - pureQ p + (2 : ℝ) ^ (-p) := by
    simpa only [E, mul_assoc] using pureBoseBX_moment hp hp₂.le
  have hScI : IntegrableOn (fun s => lineDensity p s * (B (m * s) + E (m * s))) (Ioi 0) := by
    simpa only [Pi.add_apply, mul_add] using
      (pureIntegral_integrable_scale hm hBI).add (pureIntegral_integrable_scale hm hEI)
  have hSc : (∫ s : ℝ in Ioi 0, lineDensity p s * (B (m * s) + E (m * s))) =
      m ^ (-p) * (1 + 2 * p + 2 * pureP p - pureQ p + (2 : ℝ) ^ (-p)) := by
    simp only [mul_add]
    rw [integral_add (pureIntegral_integrable_scale hm hBI) (pureIntegral_integrable_scale hm hEI),
      pureIntegral_scale hm B, pureIntegral_scale hm E, hB, hEE]
    ring
  obtain ⟨hF, hFE⟩ := fourthSourceRow_integral (m := m) hp hp₂.le hL hθ hu hm hm
  have hPoint (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) : -(w s * F s) ≤
      δ * (lineDensity p s * (B (m * s) + E (m * s))) := by
    have hs₀ : 0 < s := hs
    have hβm := (scaledExpTail_secant hs₀ hm hmu).2
    have hβu := (scaledExpTail_secant hs₀ hu hu₁.le).2
    have hC := BoseShape.C_antitone (mul_pos hs₀ hm) (mul_pos hs₀ hu)
      (mul_le_mul_of_nonneg_left hmu hs₀.le)
    have hCm := (BoseShape.C_pos (mul_pos hs₀ hm)).le
    have hCu := (BoseShape.C_pos (mul_pos hs₀ hu)).le
    have hβ₁ : scaledExpTail s m - scaledExpTail s u ≤ δ * BoseShape.C (s * m) :=
      hβm.trans (mul_le_mul_of_nonneg_right (by dsimp only [δ]; linarith only [hmL]) hCm)
    have hβ₂ : scaledExpTail s u - scaledExpTail s 1 ≤ δ * BoseShape.C (s * m) :=
      hβu.trans (mul_le_mul_of_nonneg_left hC hδ.le)
    have hβ₀ : 0 ≤ scaledExpTail s u - scaledExpTail s 1 :=
      sub_nonneg.mpr ((scaledExpTail_strictAnti hs₀).antitoneOn hu (mem_Ioi.mpr zero_lt_one) hu₁.le)
    have hExp : Real.exp (-s * u) ≤ Real.exp (-(m * s)) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_le_mul_of_nonneg_left hmu hs₀.le]
    have hβ₃ := mul_le_mul hExp hβ₂ hβ₀ (Real.exp_pos _).le
    have hA : adjacentBoseGap m m s = 0 := by unfold adjacentBoseGap; ring
    have hD := fourthSourceResponse_eq (r := m) hu hm hs₀
    rw [hA, mul_zero, add_zero, fourthSourceResponse, sub_self, zero_sub] at hD
    have hBE : 0 ≤ polyB (m * s) := (polyB_pos (mul_pos hm hs₀)).le
    have hB₀ : 0 ≤ B (m * s) := mul_nonneg hBE (BoseShape.C_pos (mul_pos hm hs₀)).le
    have hE₀ : 0 ≤ E (m * s) := mul_nonneg (mul_nonneg hBE (Real.exp_pos _).le)
      (BoseShape.C_pos (mul_pos hm hs₀)).le
    have hPos := (lawDensity_pos (zero_lt_one.trans_le hp) hL hθ hs₀).le
    have hρ := lawDensity_le_pure hp hp₂ hL hθ hs₀
    have hBR := mul_le_mul_of_nonneg_left (add_le_add hβ₁ hβ₃) hBE
    rw [mul_comm s m] at hBR
    have hR : -F s ≤ δ * (B (m * s) + E (m * s)) := by
      dsimp only [F, B, E]
      rw [hD]
      linear_combination hBR
    calc
      _ = w s * (-F s) := by ring
      _ ≤ w s * (δ * (B (m * s) + E (m * s))) := mul_le_mul_of_nonneg_left hR hPos
      _ ≤ lineDensity p s * (δ * (B (m * s) + E (m * s))) :=
        mul_le_mul_of_nonneg_right hρ (mul_nonneg hδ.le (add_nonneg hB₀ hE₀))
      _ = _ := by ring
  have hCmp := setIntegral_mono_on hF.neg (hScI.const_mul δ) measurableSet_Ioi hPoint
  change (∫ s : ℝ in Ioi 0, -(w s * F s)) ≤
    (∫ s : ℝ in Ioi 0, δ * (lineDensity p s * (B (m * s) + E (m * s)))) at hCmp
  rw [integral_neg, integral_const_mul, hSc] at hCmp
  simpa only [hFE, sub_self, zero_mul, add_zero, δ, mul_assoc] using hCmp

theorem fourthComparisonRoot_high_bracket {p L θ u m : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hm : 0 < m) (hmu : m ≤ u) (hu₁ : u < 1)
    (hmL : 2 * u - 1 ≤ m) :
    m - fourthComparisonRoot p L θ u m m < (4 / 5) * (1 - u) := by
  let r := fourthComparisonRoot p L θ u m m
  have hp₂ : p < 2 := hP.trans_lt (by norm_num)
  obtain ⟨⟨hr, hrm⟩, hRoot, _⟩ := fourthComparisonRoot_spec hp hp₂ hL hθ hm hmu hu₁ hm.le le_rfl
  have hSlope := fourthSource_diag_secant hp hp₂ hL hθ (hm.trans_le hmu) hr hrm.le
  have hDef := fourthSource_diag_deficit_le hp hP hL hθ hm hmu hu₁ hmL
  change fourthSourceRow p L θ u m r m = 0 at hRoot
  rw [hRoot, zero_sub] at hSlope
  have hQ : 0 < pureQ p - pureP p := by
    linarith only [jointSource_Q_sub_twoP_gt hp hP, pureP_nonneg hp]
  have hPow := Real.rpow_pos_of_pos hm (-p)
  have hC := (div_lt_iff₀ hQ).mp (jointSource_c0_lt hp hP)
  have hδ := sub_pos.mpr hu₁
  have hStrict := mul_lt_mul_of_pos_left hC (mul_pos hδ hPow)
  have hAll := (hSlope.trans hDef).trans_lt hStrict
  change m - r < _
  apply lt_of_mul_lt_mul_right _ (mul_nonneg hPow.le hQ.le)
  nlinarith only [hAll]

end ACS12.GammaMeasure

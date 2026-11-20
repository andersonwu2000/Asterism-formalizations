import ACS12.JointMomentScaling

/-! C6 pure test for the retained joint source, using its full A-stream debit. -/
namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaDeficit (lineDensity)

private theorem pureJoint_head_integral {p L u m r : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hu : 0 < u) (hm : 0 < m) (hr : 0 < r) :
    let H (s : ℝ) := lineDensity p s * polyA (u * s) *
      (Real.exp (-s * m) * (r + scaledExpTail s r))
    IntegrableOn H (Ioi 0) ∧
      samplingHead (lawPeanoKernel p L 0 u .a) m r = ∫ s : ℝ in Ioi 0, H s := by
  obtain ⟨hI, hE⟩ := lawPeanoHead_sampling hp hp₂ hL ⟨le_rfl, zero_le_one⟩ hu hm hr .a
  simp only [lawPeanoDensity, densityPolynomial, lawDensity, sub_zero, one_mul, zero_mul, add_zero] at hI hE
  have hEq (s : ℝ) : lineDensity p s * polyA (u * s) * Real.exp (-s * m) * (r + scaledExpTail s r) =
      lineDensity p s * polyA (u * s) * (Real.exp (-s * m) * (r + scaledExpTail s r)) := by ring
  exact ⟨hI.congr (Eventually.of_forall hEq), hE.trans (setIntegral_congr_fun measurableSet_Ioi (fun s _ => hEq s))⟩

private noncomputable def pureJointDensity (u m r s : ℝ) : ℝ :=
  (u - m) * ((1 + u * s) * Real.exp (-s * u)) +
    polyA (u * s) * (scaledExpTail s m - scaledExpTail s u) -
    polyB (u * s) * (scaledExpTail s u - scaledExpTail s 1) -
    polyA (u * s) * jointRetainedGap m r s

private theorem pureJoint_integral {p L u m r : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hu : 0 < u) (hm : 0 < m) (hr : 0 < r) :
    IntegrableOn (fun s => lineDensity p s * pureJointDensity u m r s) (Ioi 0) ∧
      adjacentSourceLaw p L 0 u m m r = ∫ s : ℝ in Ioi 0, lineDensity p s * pureJointDensity u m r s := by
  let F (s : ℝ) := lineDensity p s * outerSourceDensity u m s
  let A (v q s : ℝ) := lineDensity p s * polyA (u * s) * (Real.exp (-s * v) * (q + scaledExpTail s q))
  obtain ⟨hF, hFE⟩ := outerSourceLaw_integral (m := m) hp hp₂ hL ⟨le_rfl, zero_le_one⟩ hu
  simp only [lawDensity, sub_zero, one_mul, zero_mul, add_zero, lawSelf, mul_zero] at hF hFE
  obtain ⟨hAI, hAE⟩ := pureJoint_head_integral hp hp₂ hL hu hm hr
  obtain ⟨hUI, hUE⟩ := pureJoint_head_integral hp hp₂ hL hu hu hu
  change IntegrableOn F (Ioi 0) at hF
  change IntegrableOn (A m r) (Ioi 0) at hAI
  change IntegrableOn (A u u) (Ioi 0) at hUI
  have hEq (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      lineDensity p s * pureJointDensity u m r s = F s + A m r s - A u u s := by
    have hs₀ : 0 < s := hs
    simp only [F, A, pureJointDensity, outerSourceDensity, jointRetainedGap_eq hm hs₀,
      scaledExpTail_bridge hs₀ hu]
    linear_combination -(lineDensity p s) * peanoBose_total hu hs₀
  constructor
  · apply ((hF.add hAI).sub hUI).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hEq s hs).symm
  · rw [setIntegral_congr_fun measurableSet_Ioi hEq]
    change _ = ∫ s : ℝ in Ioi 0, (F + A m r) s - A u u s
    rw [integral_sub (hF.add hAI) hUI]
    change _ = (∫ s : ℝ in Ioi 0, F s + A m r s) - ∫ s : ℝ in Ioi 0, A u u s
    rw [integral_add hF hAI]
    dsimp only [F, A]
    rw [← hFE, ← hAE, ← hUE]
    unfold adjacentSourceLaw
    ring

private theorem pureSourceCore_moment {p : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) :
    let f (s : ℝ) := (1 + s) * Real.exp (-s) + polyA s * BoseShape.C s - polyB s * BoseShape.C s
    IntegrableOn (fun s => lineDensity p s * f s) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, lineDensity p s * f s) = pureQ p - 2 * pureP p - 1 := by
  let D (s : ℝ) := lineDensity p s * fourthD 1 1 s
  let B (s : ℝ) := lineDensity p s * polyB s * BoseShape.C s
  obtain ⟨hD, hDE⟩ := pureFourth_moment hp hp₂ zero_lt_one
  change IntegrableOn D (Ioi 0) at hD
  rw [Real.one_rpow, one_mul] at hDE
  have hBE : (∫ s : ℝ in Ioi 0, B s) = 1 + pureP p := by
    simpa only [B, pureP, Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one, zero_add,
      Nat.zero_add, Real.one_rpow, zero_mul, sub_zero] using pureBoseB_moment hp hp₂ 0
  have hB : IntegrableOn B (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [hBE]
    linarith only [pureP_nonneg hp]
  have hEq (s : ℝ) :
      lineDensity p s * ((1 + s) * Real.exp (-s) + polyA s * BoseShape.C s - polyB s * BoseShape.C s) =
        D s - B s := by simp only [D, B, fourthD, one_mul, mul_one]; ring
  constructor
  · exact (hD.sub hB).congr (Eventually.of_forall fun s => (hEq s).symm)
  · rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => hEq s), integral_sub hD hB]
    change (∫ s : ℝ in Ioi 0, lineDensity p s * fourthD 1 1 s) - _ = _
    rw [hDE, hBE]
    ring

theorem pureJoint_at_lowMass_pos {p L u r : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hL : 0 < L) (huL : 7 / 8 ≤ u) (hu₁ : u < 1) (hr : 0 < r) (hrm : r ≤ 2 * u - 1)
    (hBracket : 2 * u - 1 - r < (4 / 5) * (1 - u)) :
    adjacentSourceLaw p L 0 u (2 * u - 1) (2 * u - 1) r > 0 := by
  let m := 2 * u - 1
  let δ := 1 - u
  let k := u / m
  have hm : 0 < m := by dsimp only [m]; linarith only [huL]
  have hu : 0 < u := by linarith only [huL]
  have hδ : 0 < δ := sub_pos.mpr hu₁
  have hmu : m ≤ u := by dsimp only [m]; linarith only [hu₁]
  have hk : 1 ≤ k := (le_div_iff₀ hm).mpr (by simpa only [one_mul] using hmu)
  have hkU : k ≤ 7 / 6 := (div_le_iff₀ hm).mpr (by dsimp only [m]; linarith only [huL])
  have hku : k * m = u := div_mul_cancel₀ u hm.ne'
  have hp₂ : p ≤ 2 := hP.trans (by norm_num)
  let E (s : ℝ) := polyA s * Real.exp (-s)
  let C (s : ℝ) := (1 + s) * Real.exp (-s) + polyA s * BoseShape.C s - polyB s * BoseShape.C s
  obtain ⟨hC, hCE⟩ := pureSourceCore_moment hp hp₂
  obtain ⟨hI, hVal⟩ := pureJoint_integral hp hp₂ hL hu hm hr
  have hC₀ : IntegrableOn (fun s => lineDensity p s * C (u * s)) (Ioi 0) :=
    pureIntegral_integrable_scale hu hC
  have hE₀ : IntegrableOn (fun s => lineDensity p s * E (m * s)) (Ioi 0) := by
    apply pureIntegral_integrable_scale hm
    simpa only [E, mul_assoc] using (pureA_exp_moment hp hp₂).1
  have hPoint (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      δ * (lineDensity p s * C (u * s)) - ((m - r) * k ^ 2) * (lineDensity p s * E (m * s)) ≤
      lineDensity p s * pureJointDensity u m r s := by
    have hs₀ : 0 < s := hs
    have hρ := (lineDensity_pos (zero_lt_one.trans_le hp) hs₀).le
    have hGap : u - m = δ := by dsimp only [m, δ]; ring
    have hA := (scaledExpTail_secant hs₀ hm hmu).1
    have hB := (scaledExpTail_secant hs₀ hu hu₁.le).2
    rw [hGap, mul_comm s u] at hA
    rw [show 1 - u = δ from rfl, mul_comm s u] at hB
    have hAM := mul_le_mul_of_nonneg_left hA (polyA_pos (mul_pos hu hs₀)).le
    have hBM := mul_le_mul_of_nonneg_left hB (polyB_pos (mul_pos hu hs₀)).le
    have hK := (adjacentBoseGap_bounds hs₀ hr hrm).2
    have hK₀ := (adjacentBoseGap_bounds hs₀ hr hrm).1
    have hSc := polyA_scale_upper hk (mul_nonneg hm.le hs₀.le)
    rw [← mul_assoc, hku] at hSc
    have hDebit : polyA (u * s) * jointRetainedGap m r s ≤ (m - r) * k ^ 2 * E (m * s) := by
      have hP := mul_le_mul hSc hK hK₀ (mul_nonneg (sq_nonneg k) (polyA_pos (mul_pos hm hs₀)).le)
      have h := mul_le_mul_of_nonneg_right hP (Real.exp_pos (-(m * s))).le
      unfold jointRetainedGap E
      rw [show -(m * s) = -s * m by ring] at h ⊢
      linear_combination h
    have h : δ * C (u * s) - (m - r) * k ^ 2 * E (m * s) ≤ pureJointDensity u m r s := by
      simp only [C, pureJointDensity, hGap, show -(u * s) = -s * u by ring]
      linear_combination hAM + hBM + hDebit
    linear_combination lineDensity p s * h
  have hCmp := setIntegral_mono_on ((hC₀.const_mul δ).sub (hE₀.const_mul ((m - r) * k ^ 2)))
    hI measurableSet_Ioi hPoint
  change (∫ s : ℝ in Ioi 0, δ * (lineDensity p s * C (u * s)) -
    ((m - r) * k ^ 2) * (lineDensity p s * E (m * s))) ≤ _ at hCmp
  rw [integral_sub (hC₀.const_mul δ) (hE₀.const_mul ((m - r) * k ^ 2)),
    integral_const_mul, integral_const_mul, pureIntegral_scale hu C, pureIntegral_scale hm E, ← hVal] at hCmp
  change (∫ s : ℝ in Ioi 0, lineDensity p s * C s) = _ at hCE
  rw [hCE] at hCmp
  have hE : (∫ s : ℝ in Ioi 0, lineDensity p s * E s) < 91 / 200 := by
    simpa only [E, mul_assoc] using pureA_exp_moment_lt hp hP
  have hPow : m ^ (-p) = u ^ (-p) * k ^ p := by
    dsimp only [k]
    rw [Real.div_rpow hu.le hm.le, Real.rpow_neg hu.le, Real.rpow_neg hm.le]
    field_simp [(Real.rpow_pos_of_pos hu p).ne', (Real.rpow_pos_of_pos hm p).ne']
  have hP₀ := Real.rpow_pos_of_pos hu (-p)
  have hK₀ := Real.rpow_nonneg (zero_le_one.trans hk) p
  have hK₂ : k ^ p ≤ k ^ 2 := (Real.rpow_le_rpow_of_exponent_le hk hp₂).trans_eq (Real.rpow_two _)
  have hDebit : ((m - r) * k ^ 2) * (m ^ (-p) * ∫ s : ℝ in Ioi 0, lineDensity p s * E s) <
      δ * u ^ (-p) * (27 / 40) := by
    have hMR : 0 ≤ m - r := sub_nonneg.mpr hrm
    have hK₄ : k ^ 4 ≤ (7 / 6 : ℝ) ^ 4 := pow_le_pow_left₀ (zero_le_one.trans hk) hkU 4
    have h₁ := mul_le_mul_of_nonneg_left hE.le
      (mul_nonneg (mul_nonneg (mul_nonneg hMR (sq_nonneg k)) hP₀.le) hK₀)
    have h₂ := mul_le_mul_of_nonneg_left hK₂
      (mul_nonneg (mul_nonneg (mul_nonneg hMR (sq_nonneg k)) hP₀.le) (by norm_num : (0 : ℝ) ≤ 91 / 200))
    have h₃ := mul_le_mul_of_nonneg_left hK₄
      (mul_nonneg (mul_nonneg hMR hP₀.le) (by norm_num : (0 : ℝ) ≤ 91 / 200))
    change m - r < 4 / 5 * δ at hBracket
    have h₄ := mul_le_mul_of_nonneg_right hBracket.le
      (show 0 ≤ u ^ (-p) * ((7 / 6 : ℝ) ^ 4 * (91 / 200)) from mul_nonneg hP₀.le (by norm_num))
    have h₅ := mul_lt_mul_of_pos_left
      (by norm_num : (4 / 5 : ℝ) * ((7 / 6 : ℝ) ^ 4 * (91 / 200)) < 27 / 40) (mul_pos hδ hP₀)
    rw [hPow]
    nlinarith only [h₁, h₂, h₃, h₄, h₅]
  have hCore := mul_lt_mul_of_pos_left (jointSource_Q_sub_twoP_gt hp hP) (mul_pos hδ hP₀)
  nlinarith only [hCmp, hCore, hDebit, mul_pos hδ hP₀]

end ACS12.GammaMeasure

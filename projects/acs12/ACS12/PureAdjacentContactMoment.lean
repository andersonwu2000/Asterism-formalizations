import ACS12.PureAdjacentArc

/-! The exact normalized B deficit and its contact-side exponent loss. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaDeficit (lineDensity)

theorem pureBStack_integral {p u : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hu : 0 < u) :
    let f (s : ℝ) := lineDensity p s * polyB s * scaledExpTail s (1 / u)
    IntegrableOn f (Ioi 0) ∧ pureBStack p u = ∫ s : ℝ in Ioi 0, f s := by
  have hθ : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have hq : 0 < 1 / u := one_div_pos.mpr hu
  obtain ⟨hI, _⟩ := lawPeanoTail_sampling hp hp₂ zero_lt_one hθ zero_lt_one (t := 0) le_rfl hq .b
  obtain ⟨_, hE⟩ := lawPeanoTail_sampling hp hp₂ zero_lt_one hθ hu (t := 0) le_rfl zero_lt_one .b
  simp only [lawPeanoDensity, lawDensity, sub_zero, one_mul, zero_mul, add_zero,
    densityPolynomial, mul_zero, Real.exp_zero, mul_one] at hI hE
  refine ⟨hI, ?_⟩
  have hTail : samplingTail (purePeanoB p u) 0 1 =
      samplingTail (lawPeanoKernel p 1 0 u .b) 0 1 := by
    unfold samplingTail
    apply congrArg ((1 : ℝ) * ·)
    apply tsum_congr
    intro j
    exact (lawPeanoKernel_zero hp hp₂ zero_lt_one hu (by positivity)).2.symm
  let f (s : ℝ) := polyB s * scaledExpTail s (1 / u)
  have hBeta (s : ℝ) : scaledExpTail s 1 = u * scaledExpTail (u * s) (1 / u) := by
    unfold scaledExpTail
    rw [mul_one, show u * s * (1 / u) = s by field_simp [hu.ne']]
    field_simp [hu.ne']
  have hQ (s : ℝ) : lineDensity p s * polyB (u * s) * scaledExpTail s 1 =
      u * (lineDensity p s * f (u * s)) := by
    rw [hBeta]
    dsimp only [f]
    ring
  rw [pureBStack, hTail, hE, setIntegral_congr_fun measurableSet_Ioi (fun s _ => hQ s),
    integral_const_mul, pureIntegral_scale hu f]
  have hP' : u ^ (p - 1) * u ^ (-p) = u⁻¹ := by
    rw [← Real.rpow_add hu, show p - 1 + -p = -1 by ring, Real.rpow_neg_one]
  have hP : u ^ (p - 1) * u * u ^ (-p) = 1 := by
    rw [mul_right_comm, hP', inv_mul_cancel₀ hu.ne']
  rw [← mul_assoc, ← mul_assoc, hP, one_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s _
  dsimp only [f]
  ring

theorem pureBStack_one_eq {p : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) :
    pureBStack p 1 = pureZ p - 1 := by
  rw [(pureBStack_integral hp hp₂ zero_lt_one).2]
  simp only [div_one]
  have hEq (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      lineDensity p s * polyB s * scaledExpTail s 1 =
        lineDensity p s * (1 - Real.exp (-s)) * BoseShape.C s := by
    have hB := scaledExpTail_bridge hs zero_lt_one
    simp only [mul_one] at hB
    have hE : scaledExpTail s 1 = Real.exp (-s) / (1 - Real.exp (-s)) := by
      apply (eq_div_iff (expHead_den_pos hs).ne').mpr
      linear_combination -hB
    have hP := boseC_paired_eq hs
    rw [hE, mul_assoc (lineDensity p s), mul_assoc (lineDensity p s), hP]
    unfold polyB
    field_simp [(expHead_den_pos hs).ne']
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hEq, (pureC_difference hp).2]

private theorem beta_gap_half {s u : ℝ} (hs : 0 < s) (hu : 0 < u) (hu₁ : u ≤ 1) :
    scaledExpTail s 1 - scaledExpTail s (1 / u) ≤ (1 / u - 1) / 2 := by
  have hU : 1 ≤ 1 / u := (le_div_iff₀ hu).mpr (by simpa only [one_mul] using hu₁)
  let F (t : ℝ) := scaledExpTail s t + t / 2
  have hD (t : ℝ) (ht : 0 < t) : HasDerivAt F (1 / 2 - BoseShape.C (s * t)) t := by
    convert (scaledExpTail_derivative hs ht).add ((hasDerivAt_id t).div_const 2) using 1
    ring
  have hM : MonotoneOn F (Icc 1 (1 / u)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun t ht => (hD t (zero_lt_one.trans_le ht.1)).continuousAt.continuousWithinAt
    · exact fun t ht => (hD t (zero_lt_one.trans_le (interior_subset ht).1)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Icc (1 : ℝ) (1 / u) := interior_subset ht
      have ht₀ := zero_lt_one.trans_le ht'.1
      rw [(hD t ht₀).deriv]
      exact sub_nonneg.mpr (boseC_lt_half (mul_pos hs ht₀)).le
  have h := hM ⟨le_rfl, hU⟩ ⟨hU, le_rfl⟩ hU
  dsimp only [F] at h
  linarith only [h]

theorem pureBDeficit_exponent_loss {p u : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hu : 0 < u) (hu₁ : u ≤ 1) :
    pureZ 1 - 1 - pureBStack 1 u - (1 - u) / (48 * u) ≤ pureZ p - 1 - pureBStack p u := by
  let k (s : ℝ) := polyB s * (scaledExpTail s 1 - scaledExpTail s (1 / u))
  have hU : 1 ≤ 1 / u := (le_div_iff₀ hu).mpr (by simpa only [one_mul] using hu₁)
  have hK₀ (s : ℝ) (hs : 0 < s) : 0 ≤ k s := by
    unfold k
    apply mul_nonneg (polyB_pos hs).le
    exact sub_nonneg.mpr ((scaledExpTail_strictAnti hs).antitoneOn (mem_Ioi.mpr (show (0 : ℝ) < 1 from zero_lt_one))
      (one_div_pos.mpr hu) hU)
  have hK (s : ℝ) (hs : 0 < s) : k s ≤ ((1 - u) / (4 * u)) * s ^ 2 := by
    have hB := (densityPolynomial_lt_quadratic .b hs).le
    have h := mul_le_mul hB (beta_gap_half hs hu hu₁)
      (sub_nonneg.mpr ((scaledExpTail_strictAnti hs).antitoneOn (mem_Ioi.mpr (show (0 : ℝ) < 1 from zero_lt_one)) (one_div_pos.mpr hu) hU))
      (by positivity : 0 ≤ s ^ 2 / 2)
    have hE : (s ^ 2 / 2) * ((1 / u - 1) / 2) = ((1 - u) / (4 * u)) * s ^ 2 := by
      field_simp [hu.ne']
      ring
    exact h.trans_eq hE
  have hF (q : ℝ) (hq : 1 ≤ q) (hq₂ : q ≤ 2) :
      IntegrableOn (fun s => lineDensity q s * k s) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, lineDensity q s * k s) = pureZ q - 1 - pureBStack q u := by
    obtain ⟨h1, h1E⟩ := pureBStack_integral hq hq₂ zero_lt_one
    obtain ⟨huI, huE⟩ := pureBStack_integral hq hq₂ hu
    simp only [div_one] at h1 h1E
    have hEq (s : ℝ) : lineDensity q s * k s =
        lineDensity q s * polyB s * scaledExpTail s 1 -
          lineDensity q s * polyB s * scaledExpTail s (1 / u) := by dsimp only [k]; ring
    refine ⟨(h1.sub huI).congr (Eventually.of_forall fun s => (hEq s).symm), ?_⟩
    simp_rw [hEq]
    rw [integral_sub h1 huI, ← h1E, ← huE, pureBStack_one_eq hq hq₂]
  obtain ⟨h1, h1E⟩ := hF 1 le_rfl (by norm_num)
  obtain ⟨hpI, hpE⟩ := hF p hp hp₂
  let C := (1 - u) / (4 * u)
  let f (s : ℝ) := C * (s ^ 2 - s ^ 3)
  let g := (Ioc (0 : ℝ) 1).indicator f
  have hC : 0 ≤ C := div_nonneg (sub_nonneg.mpr hu₁) (by positivity)
  have hInter : Ioc (0 : ℝ) 1 ∩ Ioi 0 = Ioc 0 1 :=
    inter_eq_left.mpr (fun _ hs => (show _ ∧ _ from hs).1)
  have hG : IntegrableOn g (Ioi 0) := by
    have hI : IntervalIntegrable f volume 0 1 := (by unfold f; fun_prop : Continuous f).intervalIntegrable _ _
    dsimp only [g]
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioc, IntegrableOn,
      Measure.restrict_restrict measurableSet_Ioc,
      hInter]
    exact hI.1
  have hGE : (∫ s : ℝ in Ioi 0, g s) = (1 - u) / (48 * u) := by
    dsimp only [g]
    rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
      hInter, ← intervalIntegral.integral_of_le zero_le_one]
    dsimp only [f]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub ((continuous_pow 2).intervalIntegrable (μ := volume) 0 1) ((continuous_pow 3).intervalIntegrable (μ := volume) 0 1),
      integral_pow, integral_pow]
    norm_num [C]
    field_simp [hu.ne']
    ring
  have hΓ := Real.Gamma_pos_of_pos (zero_lt_one.trans_le hp)
  have hΓ₁ := Gamma_le_one_of_band hp hp₂
  have hPoint (s : ℝ) (hs : 0 < s) : lineDensity 1 s * k s - lineDensity p s * k s ≤ g s := by
    have hOne : lineDensity 1 s = 1 := by simp [lineDensity, Real.Gamma_one]
    rw [hOne, one_mul]
    rcases le_or_gt s 1 with h | h
    · dsimp only [g]
      rw [indicator_of_mem (show s ∈ Ioc (0 : ℝ) 1 from ⟨hs, h⟩)]
      have hL : s ≤ lineDensity p s := by
        unfold lineDensity
        refine le_trans ?_ (le_div_self (Real.rpow_nonneg hs.le _) hΓ hΓ₁)
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hs h (by linarith : p - 1 ≤ 1)
      have hA := mul_le_mul_of_nonneg_right hL (hK₀ s hs)
      have hB := mul_le_mul_of_nonneg_left (hK s hs) (sub_nonneg.mpr h)
      dsimp only [f, C]
      nlinarith only [hA, hB]
    · dsimp only [g]
      rw [indicator_of_notMem (show s ∉ Ioc (0 : ℝ) 1 from fun hs => (not_le_of_gt h) hs.2)]
      have hL : 1 ≤ lineDensity p s := by
        unfold lineDensity
        exact (Real.one_le_rpow h.le (sub_nonneg.mpr hp)).trans
          (le_div_self (Real.rpow_nonneg hs.le _) hΓ hΓ₁)
      exact sub_nonpos.mpr (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hL (hK₀ s hs))
  have h := integral_mono_ae (h1.sub hpI) hG (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact hPoint s hs)
  simp only [Pi.sub_apply] at h
  rw [integral_sub h1 hpI, h1E, hpE, hGE] at h
  linarith only [h]

end ACS12.GammaMeasure

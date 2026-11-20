import ACS12.QuarticCrossPrimitive
import Mathlib.Analysis.Convex.Continuous

/-! The smooth circular torque kernel and its continuous zero extension. -/
namespace ACS12.HighCurrent

open Set Filter MeasureTheory
open scoped Topology

private noncomputable def arcKernelInterior (p t : ℝ) : ℝ :=
  Real.cos t * Real.sin t ^ (-(p + 1))

noncomputable def quarticArcKernel (p t : ℝ) : ℝ :=
  if t ≤ Real.pi / 2 then arcKernelInterior p t else 0

private noncomputable def arcKernelFirst (p t : ℝ) : ℝ :=
  -(Real.sin t ^ (-(p + 2))) * (p + 1 - p * Real.sin t ^ 2)

private theorem arcKernelInterior_deriv (p : ℝ) {t : ℝ} (ht : t ∈ Ioo 0 Real.pi) :
    HasDerivAt (arcKernelInterior p) (arcKernelFirst p t) t := by
  have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
  have hPow := (Real.hasDerivAt_sin t).rpow_const (p := -(p + 1))
    (Or.inl hs.ne')
  have h := (Real.hasDerivAt_cos t).mul hPow
  convert h using 1
  simp only [arcKernelFirst, show -(p + 1) - 1 = -(p + 2) by ring]
  rw [show -(p + 1) = -(p + 2) + 1 by ring, Real.rpow_add hs, Real.rpow_one]
  linear_combination ((p + 1) * Real.sin t ^ (-(p + 2))) * Real.sin_sq_add_cos_sq t

private theorem arcKernelFirst_deriv (p : ℝ) {t : ℝ} (ht : t ∈ Ioo 0 Real.pi) :
    HasDerivAt (arcKernelFirst p)
      (Real.cos t * Real.sin t ^ (-(p + 3)) *
        ((p + 1) * (p + 2) - p ^ 2 * Real.sin t ^ 2)) t := by
  have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
  have hSin := Real.hasDerivAt_sin t
  have hPow := (hSin.rpow_const (p := -(p + 2)) (Or.inl hs.ne')).neg
  have hB := ((hSin.pow 2).const_mul p).const_sub (p + 1)
  convert hPow.mul hB using 1
  simp only [Pi.neg_apply, Pi.pow_apply, Nat.reduceSub, pow_one, Nat.cast_ofNat,
    show -(p + 2) - 1 = -(p + 3) by ring]
  rw [show -(p + 2) = -(p + 3) + 1 by ring, Real.rpow_add hs, Real.rpow_one]
  ring

private theorem arcKernelInterior_convex {p a : ℝ} (hp : 0 ≤ p) (ha : 0 < a) :
    ConvexOn ℝ (Icc a (Real.pi / 2)) (arcKernelInterior p) := by
  have hMem (t : ℝ) (ht : t ∈ Icc a (Real.pi / 2)) : t ∈ Ioo 0 Real.pi :=
    ⟨ha.trans_le ht.1, ht.2.trans_lt (by linarith only [Real.pi_pos])⟩
  apply convexOn_of_deriv2_nonneg (convex_Icc _ _)
  · exact fun t ht => (arcKernelInterior_deriv p (hMem t ht)).continuousAt.continuousWithinAt
  · exact fun t ht => (arcKernelInterior_deriv p (hMem t (interior_subset ht))).differentiableAt.differentiableWithinAt
  · intro t ht
    have ht' := hMem t (interior_subset ht)
    have hEq : deriv (arcKernelInterior p) =ᶠ[𝓝 t] arcKernelFirst p := by
      filter_upwards [Ioo_mem_nhds ht'.1 ht'.2] with u hu
      exact (arcKernelInterior_deriv p hu).deriv
    exact ((arcKernelFirst_deriv p ht').congr_of_eventuallyEq hEq).differentiableAt.differentiableWithinAt
  · intro t ht
    have hCap := interior_subset ht
    have ht' := hMem t hCap
    have hEq : deriv (arcKernelInterior p) =ᶠ[𝓝 t] arcKernelFirst p := by
      filter_upwards [Ioo_mem_nhds ht'.1 ht'.2] with u hu
      exact (arcKernelInterior_deriv p hu).deriv
    have hcos : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith only [Real.pi_pos, ht'.1], hCap.2⟩
    have hB : 0 ≤ (p + 1) * (p + 2) - p ^ 2 * Real.sin t ^ 2 := by
      nlinarith only [hp, mul_nonneg (sq_nonneg p) (sq_nonneg (Real.cos t)),
        congrArg (p ^ 2 * ·) (Real.sin_sq_add_cos_sq t)]
    rw [Function.iterate_succ_apply', Function.iterate_one, hEq.deriv_eq, (arcKernelFirst_deriv p ht').deriv]
    exact mul_nonneg (mul_nonneg hcos (Real.rpow_nonneg (Real.sin_pos_of_pos_of_lt_pi ht'.1 ht'.2).le _)) hB

theorem quarticArcKernel_zero (p : ℝ) {t : ℝ} (ht : Real.pi / 2 ≤ t) :
    quarticArcKernel p t = 0 := by
  rcases ht.eq_or_lt with rfl | h
  · simp [quarticArcKernel, arcKernelInterior, Real.sin_pi_div_two, Real.cos_pi_div_two]
  · exact if_neg (not_le_of_gt h)

theorem quarticArcKernel_nonneg (p : ℝ) {t : ℝ} (ht : 0 < t) : 0 ≤ quarticArcKernel p t := by
  unfold quarticArcKernel
  split_ifs with h
  · exact mul_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith only [Real.pi_pos, ht], h⟩)
      (Real.rpow_nonneg (Real.sin_pos_of_pos_of_lt_pi ht (by linarith only [Real.pi_pos, h])).le _)
  · exact le_rfl

theorem quarticArcKernel_antitone {p : ℝ} (hp : 0 ≤ p) :
    AntitoneOn (quarticArcKernel p) (Ioi 0) := by
  intro a ha b hb hab
  by_cases hB : b ≤ Real.pi / 2
  · have hA := hab.trans hB
    simp only [quarticArcKernel, if_pos hA, if_pos hB]
    suffices h : AntitoneOn (arcKernelInterior p) (Icc a (Real.pi / 2)) from
      h ⟨le_rfl, hA⟩ ⟨hab, hB⟩ hab
    have hMem (t : ℝ) (ht : t ∈ Icc a (Real.pi / 2)) : t ∈ Ioo 0 Real.pi :=
      ⟨ha.trans_le ht.1, ht.2.trans_lt (by linarith only [Real.pi_pos])⟩
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · exact fun t ht => (arcKernelInterior_deriv p (hMem t ht)).continuousAt.continuousWithinAt
    · exact fun t ht => (arcKernelInterior_deriv p (hMem t (interior_subset ht))).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' := hMem t (interior_subset ht)
      rw [(arcKernelInterior_deriv p ht').deriv]
      have hB : 0 ≤ p + 1 - p * Real.sin t ^ 2 := by
        nlinarith only [hp, mul_nonneg hp (sq_nonneg (Real.cos t)),
          congrArg (p * ·) (Real.sin_sq_add_cos_sq t)]
      exact mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (Real.rpow_nonneg (Real.sin_pos_of_pos_of_lt_pi ht'.1 ht'.2).le _)) hB
  · rw [quarticArcKernel_zero p (le_of_not_ge hB)]
    exact quarticArcKernel_nonneg p ha

theorem quarticArcKernel_convex {p : ℝ} (hp : 0 ≤ p) :
    ConvexOn ℝ (Ioi 0) (quarticArcKernel p) := by
  have hPi := Real.pi_pos
  let K := quarticArcKernel p
  have hCore {s t a b : ℝ} (hs : 0 < s) (ht : 0 < t)
      (hS : s ≤ Real.pi / 2) (hT : t ≤ Real.pi / 2)
      (ha : 0 ≤ a) (hb : 0 ≤ b) (hAB : a + b = 1) :
      K (a * s + b * t) ≤ a * K s + b * K t := by
    have hMin : 0 < min s t := lt_min hs ht
    have hC := arcKernelInterior_convex hp hMin
    have h := hC.2 ⟨min_le_left _ _, hS⟩ ⟨min_le_right _ _, hT⟩ ha hb hAB
    have hUpper : a * s + b * t ≤ Real.pi / 2 := by
      nlinarith only [mul_le_mul_of_nonneg_left hS ha, mul_le_mul_of_nonneg_left hT hb,
        congrArg ((Real.pi / 2) * ·) hAB]
    simpa only [smul_eq_mul, quarticArcKernel, K, if_pos hS, if_pos hT, if_pos hUpper] using h
  have hMixed {s t a b : ℝ} (hs : 0 < s) (hS : s ≤ Real.pi / 2) (hT : Real.pi / 2 ≤ t)
      (ha : 0 ≤ a) (hb : 0 ≤ b) (hAB : a + b = 1) :
      K (a * s + b * t) ≤ a * K s + b * K t := by
    have hPos : 0 < a * s + b * (Real.pi / 2) := by
      rcases ha.eq_or_lt with h | h
      · rw [← h, zero_mul, zero_add]
        have hb₁ : b = 1 := by linarith only [hAB, h]
        rw [hb₁, one_mul]
        positivity
      · exact add_pos_of_pos_of_nonneg (mul_pos h hs) (by positivity)
    have hRange : a * s + b * (Real.pi / 2) ≤ a * s + b * t :=
      add_le_add_right (mul_le_mul_of_nonneg_left hT hb) _
    have hMono := quarticArcKernel_antitone hp hPos (hPos.trans_le hRange) hRange
    have hC := hCore hs (by positivity : 0 < Real.pi / 2) hS le_rfl ha hb hAB
    change K (a * s + b * t) ≤ K (a * s + b * (Real.pi / 2)) at hMono
    rw [show K (Real.pi / 2) = 0 from quarticArcKernel_zero p le_rfl] at hC
    rw [show K t = 0 from quarticArcKernel_zero p hT]
    exact hMono.trans hC
  refine ⟨convex_Ioi _, ?_⟩
  intro s hs t ht a b ha hb hAB
  change K (a * s + b * t) ≤ a * K s + b * K t
  by_cases hS : s ≤ Real.pi / 2
  · by_cases hT : t ≤ Real.pi / 2
    · exact hCore hs ht hS hT ha hb hAB
    · exact hMixed hs hS (le_of_not_ge hT) ha hb hAB
  · by_cases hT : t ≤ Real.pi / 2
    · simpa only [add_comm] using hMixed ht hT (le_of_not_ge hS) hb ha (by linarith only [hAB])
    · have hAbove : Real.pi / 2 ≤ a * s + b * t := by
        nlinarith only [mul_le_mul_of_nonneg_left (le_of_not_ge hS) ha,
          mul_le_mul_of_nonneg_left (le_of_not_ge hT) hb, congrArg ((Real.pi / 2) * ·) hAB]
      simp only [K, quarticArcKernel_zero p hAbove, quarticArcKernel_zero p (le_of_not_ge hS),
        quarticArcKernel_zero p (le_of_not_ge hT), mul_zero, add_zero, le_refl]

theorem quarticArcKernel_continuousOn {p : ℝ} (hp : 0 ≤ p) :
    ContinuousOn (quarticArcKernel p) (Ioi 0) := by
  simpa only [interior_Ioi] using (quarticArcKernel_convex hp).continuousOn_interior

theorem quarticArcKernel_value (p : ℝ) {t : ℝ} (ht : 0 < t) (htL : t ≤ Real.pi / 2) :
    quarticArcKernel p t = Real.cos t / Real.sin t ^ (p + 1) := by
  have hs := Real.sin_pos_of_pos_of_lt_pi ht (by linarith only [htL, Real.pi_pos])
  rw [quarticArcKernel, if_pos htL, arcKernelInterior, Real.rpow_neg hs.le, div_eq_mul_inv]

theorem quarticArcKernel_slice_eq {p θ : ℝ} (hp : 0 < p) (hθ : 0 < θ) (hθL : θ ≤ Real.pi / 2) :
    2 * (∫ v in (0 : ℝ)..(Real.pi / 2), crossSlice (quarticArcKernel p) θ v) =
      Real.sin θ ^ (-p) *
        (if θ < Real.pi / 4 then (2 * Real.cos θ) ^ (-p) *
          (3 * (1 - Real.sin (2 * θ) ^ p) / (2 * p) +
            θ * (Real.cos (2 * θ) / Real.sin (2 * θ))) else 0) := by
  let L := Real.pi / 2
  let K := quarticArcKernel p
  have hI := crossSlice_integral hθ hθL (quarticArcKernel_continuousOn hp.le)
    (fun _ ht => quarticArcKernel_zero p ht)
  change (∫ v in (0 : ℝ)..L, crossSlice K θ v) =
    θ / 2 * K (2 * θ) + (3 / 4) * ∫ v in (2 * θ)..(2 * L), K v at hI
  change 2 * (∫ v in (0 : ℝ)..L, crossSlice K θ v) = _
  rw [hI]
  by_cases hSmall : θ < Real.pi / 4
  · have hθ₂ : 2 * θ ≤ L := by dsimp [L]; linarith only [hSmall]
    have hSin₂ := Real.sin_pos_of_pos_of_lt_pi (show 0 < 2 * θ by positivity)
      (by linarith only [Real.pi_pos, hSmall])
    have hExact : (∫ v in (2 * θ)..(2 * L), K v) = (Real.sin (2 * θ) ^ (-p) - 1) / p := by
      let F (v : ℝ) := -(Real.sin v ^ (-p)) / p
      have hDer (v : ℝ) (hv : v ∈ Icc (2 * θ) L) : HasDerivAt F (K v) v := by
        have hv₀ : 0 < v := by linarith only [hv.1, hθ]
        have hSin := Real.sin_pos_of_pos_of_lt_pi hv₀ (by dsimp [L] at hv; linarith only [Real.pi_pos, hv.2])
        have hPow := ((Real.hasDerivAt_sin v).rpow_const (p := -p) (Or.inl hSin.ne')).neg.div_const p
        convert hPow using 1
        dsimp only [K]
        rw [quarticArcKernel, if_pos hv.2, arcKernelInterior, show -p - 1 = -(p + 1) by ring]
        field_simp [hp.ne']
      have hInt {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : IntervalIntegrable K volume a b :=
        ((quarticArcKernel_continuousOn hp.le).mono (by
          rw [uIcc_of_le hab]
          exact fun _ hx => ha.trans_le hx.1)).intervalIntegrable
      have hL₀ : 0 < L := by dsimp [L]; positivity
      have hL₂ : L ≤ 2 * L := by linarith
      have hLZ : (∫ v in L..(2 * L), K v) = 0 := by
        rw [← intervalIntegral.integral_zero]
        apply intervalIntegral.integral_congr
        intro v hv
        rw [uIcc_of_le hL₂] at hv
        exact quarticArcKernel_zero p hv.1
      rw [← intervalIntegral.integral_add_adjacent_intervals (hInt (by positivity) hθ₂) (hInt hL₀ hL₂),
        hLZ, add_zero, intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun v hv => hDer v (by simpa only [uIcc_of_le hθ₂] using hv)) (hInt (by positivity) hθ₂)]
      simp only [F, L, Real.sin_pi_div_two, Real.one_rpow]
      ring
    have hS := Real.sin_pos_of_pos_of_lt_pi hθ (by linarith only [hθL, Real.pi_pos])
    have hC : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith only [Real.pi_pos, hθ],
      by linarith only [Real.pi_pos, hSmall]⟩
    have hFactor : Real.sin θ ^ (-p) * (2 * Real.cos θ) ^ (-p) = Real.sin (2 * θ) ^ (-p) := by
      rw [← Real.mul_rpow hS.le (by positivity), Real.sin_two_mul]
      congr 1
      ring
    have hK : K (2 * θ) = Real.cos (2 * θ) / Real.sin (2 * θ) ^ (p + 1) :=
      quarticArcKernel_value p (by positivity) hθ₂
    rw [if_pos hSmall, ← mul_assoc, hFactor, hExact, hK]
    rw [Real.rpow_add hSin₂, Real.rpow_one]
    simp only [Real.rpow_neg hSin₂.le]
    field_simp [hSin₂.ne', hp.ne', (Real.rpow_pos_of_pos hSin₂ p).ne']
    ring
  · have hLarge : L ≤ 2 * θ := by dsimp [L]; linarith only [le_of_not_gt hSmall]
    have hZ : (∫ v in (2 * θ)..(2 * L), K v) = 0 := by
      rw [← intervalIntegral.integral_zero]
      apply intervalIntegral.integral_congr
      intro v hv
      rw [uIcc_of_le (mul_le_mul_of_nonneg_left hθL (by norm_num : (0 : ℝ) ≤ 2))] at hv
      exact quarticArcKernel_zero p (hLarge.trans hv.1)
    have hK : K (2 * θ) = 0 := quarticArcKernel_zero p hLarge
    simp only [if_neg hSmall, hK, hZ, mul_zero, add_zero]

end ACS12.HighCurrent

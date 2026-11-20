import ACS12.FourthVariation

/-! The two signed motion directions used by the original fourth-source cap. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter

theorem fourthMotion_derivative_pos {p L θ u v r m e t : ℝ}
    (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hu : 0 < u) (hv : 0 < v + t) (hr : 0 < r) (he : 0 ≤ e)
    (hmv : m + e * t ≤ v + t) :
    ∃ d > 0, HasDerivAt (fun x => fourthSourceRow p L θ u (v + x) r (m + e * x)) d t := by
  let w := lawDensity p L θ
  let K (s : ℝ) := fourthV u (v + t) r (m + e * t) s + e * Real.exp (-s * (v + t))
  have h := fourthSourceRow_variation (m := m) (dv := 1) (dr := 0) (dm := e) (t := t)
    hp hp₂ hL hθ hu (by simpa only [one_mul] using hv) (by simpa only [zero_mul, add_zero] using hr)
  simp only [one_mul, zero_mul, add_zero, sub_zero] at h
  have hInt : IntegrableOn (fun s => w s * K s) (Ioi 0) := h.1
  letI : NeZero (volume.restrict (Ioi (0 : ℝ))) := ⟨positiveHalfLine_ne_zero⟩
  have hP : 0 < ∫ s : ℝ in Ioi 0, w s * K s := by
    have hP := integral_strict_of_ae_lt (volume.restrict (Ioi (0 : ℝ))) (integrable_zero ℝ ℝ _) hInt ?_
    · simpa only [integral_zero] using hP
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact mul_pos (lawDensity_pos (zero_lt_one.trans_le hp) hL hθ hs)
        (add_pos_of_pos_of_nonneg (fourthV_pos hu hv hr hs hmv) (mul_nonneg he (Real.exp_pos _).le))
  have hS : 0 ≤ e * lawSelf p L θ := mul_nonneg he
    (mul_nonneg hθ.1 (imageSelf_pos (zero_lt_one.trans_le hp) hL).le)
  exact ⟨_, add_pos_of_pos_of_nonneg hP hS, h.2⟩

theorem fourthMotion_derivative_neg {p L θ u v r m e t : ℝ}
    (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hv : 0 < v + t) (hvu : v + t ≤ u) (hu₁ : u < 1) (hr : 0 < r + 2 * t)
    (hrv : r + 2 * t ≤ v + t)
    (hMode : (e = 0 ∧ (v + t) / 3 ≤ m ∧ m ≤ v + t) ∨ (e = 1 ∧ m = v)) :
    ∃ d < 0, HasDerivAt
      (fun x => fourthSourceRow p L θ u (v + x) (r + 2 * x) (m + e * x)) d t := by
  let V := v + t
  let R := r + 2 * t
  let M := m + e * t
  let w := lawDensity p L θ
  let K (s : ℝ) := fourthV u V R M s - 2 * fourthD V R s + e * Real.exp (-s * V)
  have h := fourthSourceRow_variation (m := m) (dv := 1) (dr := 2) (dm := e) (t := t)
    hp hp₂ hL hθ (hv.trans_le hvu) (by simpa only [one_mul] using hv) hr
  simp only [one_mul] at h
  have hInt : IntegrableOn (fun s => w s * K s) (Ioi 0) := h.1
  have hP : (∫ s : ℝ in Ioi 0, w s * K s) < 0 := by
    rcases hMode with ⟨he, hLow, hHigh⟩ | ⟨he, hm⟩
    · have hLow' : 1 / 3 ≤ m / V := (le_div_iff₀ hv).mpr (by linarith only [hLow])
      have hHigh' : m / V ≤ 1 := (div_le_one hv).mpr hHigh
      have hRef := law_fixed_mass_speedIntegral_neg hp hp₂ hL hθ hv hLow' hHigh'
      refine lt_of_le_of_lt (integral_mono_ae hInt (Integrable.of_integral_ne_zero hRef.ne) ?_) hRef
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      apply mul_le_mul_of_nonneg_left _ (lawDensity_pos (zero_lt_one.trans_le hp) hL hθ hs).le
      dsimp only [K, M]
      rw [he, zero_mul, add_zero, zero_mul, add_zero]
      exact (fourth_fixed_speed_lt hv hvu hu₁ hr hrv hs).le
    · have hRef := law_diagonal_speedIntegral_neg hp hp₂ hL hθ hv
      refine lt_of_le_of_lt (integral_mono_ae hInt (Integrable.of_integral_ne_zero hRef.ne) ?_) hRef
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      apply mul_le_mul_of_nonneg_left _ (lawDensity_pos (zero_lt_one.trans_le hp) hL hθ hs).le
      have hS := fourth_diagonal_speed_lt hv hvu hu₁ hr hrv hs
      dsimp only [K, M]
      rw [he, hm, one_mul, one_mul]
      linarith only [hS]
  have hE : e ≤ 2 := by rcases hMode with ⟨rfl, _, _⟩ | ⟨rfl, _⟩ <;> norm_num
  have hS : (e - 2) * lawSelf p L θ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hE)
    (mul_nonneg hθ.1 (imageSelf_pos (zero_lt_one.trans_le hp) hL).le)
  exact ⟨_, add_neg_of_neg_of_nonpos hP hS, h.2⟩

end ACS12.GammaMeasure


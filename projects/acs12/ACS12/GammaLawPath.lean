import ACS12.GammaDeficitMass

/-! Exact actual-to-pure density interpolation and its once-only self term. -/

namespace ACS12.GammaMeasure

open MeasureTheory Set Filter
open scoped Topology
open GammaDeficit (lineDensity signedDensity lineDensity_exp_integrable lineDensity_exp_integral
  gamma_exp_integral integrable_gamma_exp)

noncomputable def lawDensity (p L θ s : ℝ) : ℝ :=
  (1 - θ) * lineDensity p s + θ * imageDensity p L s

noncomputable def lawSelf (p L θ : ℝ) : ℝ := θ * imageSelf p L

theorem lawDensity_pos {p L θ s : ℝ} (hp : 0 < p) (hL : 0 < L)
    (hθ : θ ∈ Icc (0 : ℝ) 1) (hs : 0 < s) : 0 < lawDensity p L θ s := by
  unfold lawDensity
  rcases lt_or_eq_of_le hθ.2 with h | h
  · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr h) (lineDensity_pos hp hs))
      (mul_nonneg hθ.1 (imageDensity_pos hp hL hs).le)
  · simpa only [h, sub_self, zero_mul, one_mul, zero_add] using imageDensity_pos hp hL hs

theorem lawDensity_div_antitone {p L θ : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) :
    AntitoneOn (fun s => lawDensity p L θ s / s) (Ioi 0) := by
  have hLine (s : ℝ) (hs : 0 < s) : lineDensity p s / s = s ^ (p - 2) / Real.Gamma p := by
    have hPow : s ^ (p - 1) / s = s ^ (p - 2) := by
      calc
        _ = s ^ (p - 1) / s ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_sub hs]; congr 1; ring
    unfold lineDensity
    rw [div_right_comm, hPow]
  have hρ : AntitoneOn (fun s => lineDensity p s / s) (Ioi 0) := by
    intro s hs t ht hst
    dsimp only
    rw [hLine s hs, hLine t ht]
    exact div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hs hst (by linarith))
      (Real.Gamma_pos_of_pos hp).le
  intro s hs t ht hst
  have hw := imageDensity_div_antitone hp hp₂ hL hs ht hst
  dsimp only at hw ⊢
  simp only [lawDensity, add_div, mul_div_assoc]
  exact add_le_add (mul_le_mul_of_nonneg_left (hρ hs ht hst) (sub_nonneg.mpr hθ.2))
    (mul_le_mul_of_nonneg_left hw hθ.1)

theorem signedDensity_div_lawDensity_antitone {p L θ : ℝ} (hp : 1 ≤ p) (hp₂ : p < 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) :
    AntitoneOn (fun s => signedDensity p L s / lawDensity p L θ s) (Ioi 0) := by
  have hp₀ : 0 < p := zero_lt_one.trans_le hp
  let r (s : ℝ) := imageDensity p L s / lineDensity p s
  have hEq (s : ℝ) (hs : 0 < s) : signedDensity p L s / lawDensity p L θ s =
      (1 - r s) / (1 - θ + θ * r s) := by
    have hρ := lineDensity_pos hp₀ hs
    have hw := lawDensity_pos hp₀ hL hθ hs
    have he : (1 - θ + θ * r s) * lineDensity p s = lawDensity p L θ s := by
      dsimp [r, lawDensity]
      field_simp [hρ.ne']
    have hd : 1 - θ + θ * r s ≠ 0 := by
      intro h
      rw [h, zero_mul] at he
      exact hw.ne' he.symm
    unfold signedDensity
    apply (div_eq_div_iff hw.ne' hd).mpr
    rw [← he]
    dsimp only [r]
    field_simp [hρ.ne']
  have hR := (imageDensity_div_lineDensity_strictMono hp hp₂ hL).monotoneOn
  intro s hs t ht hst
  dsimp only
  rw [hEq t ht, hEq s hs]
  have hden (x : ℝ) (hx : 0 < x) : 0 < 1 - θ + θ * r x := by
    rcases lt_or_eq_of_le hθ.2 with h | h
    · exact add_pos_of_pos_of_nonneg (sub_pos.mpr h)
        (mul_nonneg hθ.1 (div_pos (imageDensity_pos hp₀ hL hx) (lineDensity_pos hp₀ hx)).le)
    · simpa only [h, sub_self, one_mul, zero_add] using
        div_pos (imageDensity_pos hp₀ hL hx) (lineDensity_pos hp₀ hx)
  apply (div_le_div_iff₀ (hden t ht) (hden s hs)).mpr
  nlinarith only [show r s ≤ r t from hR hs ht hst]

theorem lawDensity_div_lineDensity_tendsto_one {p L θ : ℝ} (hp : 1 ≤ p) (hp₂ : p < 2)
    (hL : 0 < L) :
    Tendsto (fun s => lawDensity p L θ s / lineDensity p s) atTop (𝓝 1) := by
  have h := ((imageDensity_div_lineDensity_tendsto_one hp hp₂ hL).const_mul θ).const_add (1 - θ)
  have h₁ : (1 - θ) + θ * 1 = 1 := by ring
  rw [h₁] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  have hρ := lineDensity_pos (zero_lt_one.trans_le hp) hs
  simp only [lawDensity, add_div, mul_div_assoc, div_self hρ.ne', mul_one]

theorem lawIntegral_eq {p L θ : ℝ} {f : ℝ → ℝ}
    (hρ : IntegrableOn (fun s => lineDensity p s * f s) (Ioi 0))
    (hw : IntegrableOn (fun s => imageDensity p L s * f s) (Ioi 0)) :
    (∫ s : ℝ in Ioi 0, lawDensity p L θ s * f s) =
      (1 - θ) * (∫ s : ℝ in Ioi 0, lineDensity p s * f s) +
        θ * (∫ s : ℝ in Ioi 0, imageDensity p L s * f s) := by
  calc
    _ = ∫ s : ℝ in Ioi 0, (1 - θ) * (lineDensity p s * f s) +
        θ * (imageDensity p L s * f s) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun s => by unfold lawDensity; ring
    _ = _ := by
      have h : (∫ s : ℝ in Ioi 0, (1 - θ) * (lineDensity p s * f s) +
            θ * (imageDensity p L s * f s)) =
          (∫ s : ℝ in Ioi 0, (1 - θ) * (lineDensity p s * f s)) +
            ∫ s : ℝ in Ioi 0, θ * (imageDensity p L s * f s) :=
        integral_add (hρ.const_mul (1 - θ)) (hw.const_mul θ)
      rw [h, integral_const_mul, integral_const_mul]

theorem hasDerivAt_lawIntegral {p L θ : ℝ} {f : ℝ → ℝ}
    (hρ : IntegrableOn (fun s => lineDensity p s * f s) (Ioi 0))
    (hw : IntegrableOn (fun s => imageDensity p L s * f s) (Ioi 0)) :
    HasDerivAt (fun u : ℝ => ∫ s : ℝ in Ioi 0, lawDensity p L u s * f s)
      (-(∫ s : ℝ in Ioi 0, signedDensity p L s * f s)) θ := by
  let Iρ := ∫ s : ℝ in Ioi 0, lineDensity p s * f s
  let Iw := ∫ s : ℝ in Ioi 0, imageDensity p L s * f s
  have he : (∫ s : ℝ in Ioi 0, signedDensity p L s * f s) = Iρ - Iw := by
    calc
      _ = ∫ s : ℝ in Ioi 0, lineDensity p s * f s - imageDensity p L s * f s := by
        apply integral_congr_ae
        exact Eventually.of_forall fun s => by unfold signedDensity; ring
      _ = _ := integral_sub hρ hw
  simp_rw [lawIntegral_eq hρ hw]
  rw [he]
  have h := (((hasDerivAt_id θ).const_sub 1).mul_const Iρ).add ((hasDerivAt_id θ).mul_const Iw)
  convert h using 1 <;> dsimp [Iρ, Iw] <;> ring

end ACS12.GammaMeasure

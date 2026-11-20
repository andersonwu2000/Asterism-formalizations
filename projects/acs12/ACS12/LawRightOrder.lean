import ACS12.LawRight

/-! The original deficit order controls the complete negative tail. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaDeficit (lineDensity signedDensity)

theorem integral_antitone_product_nonpos {W Q R : ℝ → ℝ}
    (hW : IntegrableOn W (Ioi 0)) (hQ : IntegrableOn (fun s => W s * Q s) (Ioi 0))
    (hR : IntegrableOn (fun s => W s * R s) (Ioi 0))
    (hQR : IntegrableOn (fun s => W s * Q s * R s) (Ioi 0))
    (hWp : ∀ s > 0, 0 < W s) (hR₀ : ∀ s > 0, 0 ≤ R s)
    (hM : MonotoneOn Q (Ioi 0)) (hA : AntitoneOn R (Ioi 0))
    (hQ₀ : (∫ s : ℝ in Ioi 0, W s * Q s) ≤ 0) :
    (∫ s : ℝ in Ioi 0, W s * Q s * R s) ≤ 0 := by
  have h := integral_product_comparison hQ hR hQR hW ?_
  · have hPos : 0 < ∫ s : ℝ in Ioi 0, W s := by
      letI : NeZero (volume.restrict (Ioi (0 : ℝ))) := ⟨positiveHalfLine_ne_zero⟩
      have hP := integral_strict_of_ae_lt (volume.restrict (Ioi (0 : ℝ))) (integrable_zero ℝ ℝ _) hW ?_
      · simpa only [integral_zero] using hP
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        exact hWp s hs
    have hR₁ : 0 ≤ ∫ s : ℝ in Ioi 0, W s * R s := by
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact mul_nonneg (hWp s hs).le (hR₀ s hs)
    by_contra! hneg
    exact (not_lt_of_ge (h.trans (mul_nonpos_of_nonpos_of_nonneg hQ₀ hR₁))) (mul_pos hneg hPos)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hE : (W x * Q x) * (W y * R y) + (W y * Q y) * (W x * R x) -
        (W x * Q x * R x) * W y - (W y * Q y * R y) * W x =
        (W x * W y) * ((Q y - Q x) * (R x - R y)) := by ring
    rw [hE]
    apply mul_nonneg (mul_nonneg (hWp x hx).le (hWp y hy).le)
    rcases le_total x y with hxy | hyx
    · exact mul_nonneg (sub_nonneg.mpr (hM hx hy hxy)) (sub_nonneg.mpr (hA hx hy hxy))
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hM hy hx hyx))
        (sub_nonpos.mpr (hA hy hx hyx))

private theorem lawRight_deficit_nonpos {p L θ u t : ℝ} (hp : 1 ≤ p) (hp₂ : p < 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (ht : 0 < t) (hG : lawRightTest p L θ u t ≤ 0) :
    (∫ s : ℝ in Ioi 0, signedDensity p L s * (middleRightDensity u s * Real.exp (-s * t))) ≤ 0 := by
  let w := lawDensity p L θ
  let e := signedDensity p L
  let W (s : ℝ) := w s * s * Real.exp (-s * t)
  let Q := rightMultiplier (middleA u) (middleZ u)
  let R (s : ℝ) := e s / w s
  let G (s : ℝ) := lawRightDensity p L θ u s * Real.exp (-s * t)
  let F (s : ℝ) := e s * (middleRightDensity u s * Real.exp (-s * t))
  have hp₀ := zero_lt_one.trans_le hp
  have hW : IntegrableOn W (Ioi 0) := by
    simpa only [W, w, pow_one] using lawMoment_integrable hp hp₂.le hL hθ ht 1
  have hGInt : IntegrableOn G (Ioi 0) := lawRightDensity_integrable hp hp₂.le hL hθ ht
  have hF : IntegrableOn F (Ioi 0) :=
    (lawRightTest_difference (θ₁ := 0) (θ₂ := 1) hp hp₂.le hL ht (u := u)).1
  have hρ : IntegrableOn (fun s => lineDensity p s * s * Real.exp (-s * t)) (Ioi 0) := by
    simpa only [lawDensity, sub_zero, one_mul, zero_mul, add_zero, pow_one] using
      lawMoment_integrable hp hp₂.le hL (θ := 0) ⟨le_rfl, zero_le_one⟩ ht 1
  have hw : IntegrableOn (fun s => imageDensity p L s * s * Real.exp (-s * t)) (Ioi 0) :=
    imageSlope_integrable hp₀ hL ht
  have hE : IntegrableOn (fun s => e s * s * Real.exp (-s * t)) (Ioi 0) := by
    refine (hρ.sub hw).congr (Eventually.of_forall fun s => ?_)
    dsimp only [e, signedDensity, Pi.sub_apply]
    ring
  have hEqQ (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) : W s * Q s = G s := by
    simp only [W, Q, G, lawRightDensity, w, middleRightDensity_eq hs]
    ring
  have hEqR (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) : W s * R s = e s * s * Real.exp (-s * t) := by
    dsimp only [W, R, w]
    field_simp [(lawDensity_pos hp₀ hL hθ hs).ne']
  have hEqQR (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) : W s * Q s * R s = F s := by
    rw [mul_right_comm, hEqR s hs]
    simp only [Q, F, middleRightDensity_eq hs]
    ring
  have hQ : IntegrableOn (fun s => W s * Q s) (Ioi 0) := hGInt.congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hEqQ s hs).symm)
  have hR : IntegrableOn (fun s => W s * R s) (Ioi 0) := hE.congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hEqR s hs).symm)
  have hQR : IntegrableOn (fun s => W s * Q s * R s) (Ioi 0) := hF.congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hEqQR s hs).symm)
  have hP : (∫ s : ℝ in Ioi 0, W s * Q s) ≤ 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioi hEqQ]
    exact hG
  have h := integral_antitone_product_nonpos hW hQ hR hQR
    (fun s hs => mul_pos (mul_pos (lawDensity_pos hp₀ hL hθ hs) hs) (Real.exp_pos _))
    (fun s hs => (div_pos (signedDensity_pos hp hp₂ hL hs) (lawDensity_pos hp₀ hL hθ hs)).le)
    (rightMultiplier_mono ((middleA_le u).trans (by norm_num)))
    (signedDensity_div_lawDensity_antitone hp hp₂ hL hθ) hP
  rw [setIntegral_congr_fun measurableSet_Ioi hEqQR] at h
  exact h

noncomputable def lawRightNegative (p L θ u t : ℝ) : ℝ := max 0 (-lawRightTest p L θ u t)

theorem lawRightNegative_antitone {p L u t : ℝ} (hp : 1 ≤ p) (hp₂ : p < 2)
    (hL : 0 < L) (ht : 0 < t) :
    AntitoneOn (fun θ => lawRightNegative p L θ u t) (Icc 0 1) := by
  intro θ₁ hθ₁ θ₂ hθ₂ hθ
  by_cases h : 0 ≤ lawRightTest p L θ₂ u t
  · change max 0 (-lawRightTest p L θ₂ u t) ≤ max 0 (-lawRightTest p L θ₁ u t)
    rw [max_eq_left (neg_nonpos.mpr h)]
    exact le_max_left _ _
  · have hI := lawRight_deficit_nonpos hp hp₂ hL hθ₂ ht (le_of_not_ge h)
    have hE := (lawRightTest_difference (θ₁ := θ₁) (θ₂ := θ₂) hp hp₂.le hL ht (u := u)).2
    have hG := mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (sub_nonneg.mpr hθ)) hI
    have hD : lawRightTest p L θ₁ u t ≤ lawRightTest p L θ₂ u t := sub_nonneg.mp (hE.symm ▸ hG)
    exact max_le_max le_rfl (neg_le_neg hD)

theorem lawRightNegative_tail_antitone {p L θ₁ θ₂ u t q : ℝ} (hp : 1 ≤ p) (hp₂ : p < 2)
    (hL : 0 < L) (hθ₁ : θ₁ ∈ Icc (0 : ℝ) 1) (hθ₂ : θ₂ ∈ Icc (0 : ℝ) 1) (hθ : θ₁ ≤ θ₂)
    (ht : 0 ≤ t) (hq : 0 < q) :
    samplingTail (lawRightNegative p L θ₂ u) t q ≤ samplingTail (lawRightNegative p L θ₁ u) t q := by
  have hSum (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
      Summable (fun j : ℕ => lawRightNegative p L θ u (t + ((j + 1 : ℕ) : ℝ) * q)) := by
    apply (lawRight_abs_samples_summable hp hp₂.le hL hθ ht hq).of_nonneg_of_le
    · exact fun j => le_max_left _ _
    · exact fun j => max_le (abs_nonneg _) (neg_le_abs _)
  unfold samplingTail
  refine mul_le_mul_of_nonneg_left ((hSum θ₂ hθ₂).tsum_le_tsum ?_ (hSum θ₁ hθ₁)) hq.le
  intro j
  have hJ : 0 < ((j + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  exact lawRightNegative_antitone hp hp₂ hL (add_pos_of_nonneg_of_pos ht (mul_pos hJ hq)) hθ₁ hθ₂ hθ

end ACS12.GammaMeasure


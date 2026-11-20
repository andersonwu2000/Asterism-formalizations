import ACS12.LawRight

/-! Whole clipped quadrature along the original and pure law path. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter

noncomputable def lawRightClip (p L θ u t : ℝ) : ℝ := max 0 (lawRightTest p L θ u t)

private noncomputable def lawRightWeight (p L θ t s : ℝ) : ℝ :=
  lawDensity p L θ s * s * Real.exp (-s * t)

private theorem lawRightWeight_mul {p L θ u t s : ℝ} (hs : 0 < s) :
    lawRightWeight p L θ t s * rightMultiplier (middleA u) (middleZ u) s =
      lawRightDensity p L θ u s * Real.exp (-s * t) := by
  rw [lawRightWeight, lawRightDensity, middleRightDensity_eq hs]
  ring

private theorem lawRightClip_inputs {p L θ u : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) :
    let W := lawRightWeight p L θ
    let Q := rightMultiplier (middleA u) (middleZ u)
    (∀ t > 0, IntegrableOn (W t) (Ioi 0)) ∧
    (∀ t > 0, IntegrableOn (fun s => W t s * Q s) (Ioi 0)) ∧
    (∀ t > 0, lawRightTest p L θ u t = ∫ s : ℝ in Ioi 0, W t s * Q s) ∧
    (∀ t s, 0 < s → 0 < W t s) ∧
    (∀ t x s, W t s * Real.exp (s * (t - x)) = W x s) ∧
    MonotoneOn Q (Ioi 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, rightMultiplier_mono ((middleA_le u).trans (by norm_num))⟩
  · intro t ht
    simpa only [lawRightWeight, pow_one] using lawMoment_integrable hp hp₂ hL hθ ht 1
  · intro t ht
    apply (lawRightDensity_integrable hp hp₂ hL hθ ht).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (lawRightWeight_mul hs).symm
  · intro t ht
    exact setIntegral_congr_fun measurableSet_Ioi (fun s hs => (lawRightWeight_mul hs).symm)
  · intro t s hs
    exact mul_pos (mul_pos (lawDensity_pos (zero_lt_one.trans_le hp) hL hθ hs) hs) (Real.exp_pos _)
  · intro t x s
    simp only [lawRightWeight, mul_assoc, ← Real.exp_add, show -s * t + s * (t - x) = -s * x by ring]

theorem lawRightClip_antitone {p L θ u : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) :
    AntitoneOn (lawRightClip p L θ u) (Ioi 0) := by
  obtain ⟨hW, hQ, hRep, hPos, hTilt, hM⟩ := lawRightClip_inputs (u := u) hp hp₂ hL hθ
  exact weightedPositivePart_antitone hW hQ hRep hPos hTilt hM

theorem lawRightClip_convex {p L θ u : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) :
    ConvexOn ℝ (Ioi 0) (lawRightClip p L θ u) := by
  obtain ⟨hW, hQ, hRep, hPos, hTilt, hM⟩ := lawRightClip_inputs (u := u) hp hp₂ hL hθ
  exact weightedPositivePart_convex hW hQ hRep hPos hTilt hM

theorem lawRightClip_quadratureData {p L θ u d : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hd : 0 < d) :
    QuadratureData (lawRightClip p L θ u) d := by
  apply convex_right_quadratureData_of_quadratic_decay (lawRightClip_convex hp hp₂ hL hθ)
    (fun _ _ => le_max_left _ _) _ hd
  intro a ha
  obtain ⟨B, hB, hBound⟩ := lawRightDensity_bound hp hp₂ hL hθ (u := u)
  let C := B * (1 + 2 / a)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro t ht
  have ht₀ := ha.trans_le ht
  apply max_le (div_nonneg hC (sq_nonneg _))
  apply (le_abs_self _).trans
  rw [lawRightTest, signedLaplace, ← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  let f (s : ℝ) := s ^ 1 * Real.exp (-s * t)
  let g (s : ℝ) := s ^ 2 * Real.exp (-s * t)
  have hf : IntegrableOn f (Ioi 0) := expMoment_nat_integrable 1 ht₀
  have hg : IntegrableOn g (Ioi 0) := expMoment_nat_integrable 2 ht₀
  have hI := (hf.add hg).const_mul B
  have hM := (lawRightDensity_integrable (u := u) hp hp₂ hL hθ ht₀).norm
  refine (integral_mono_ae hM hI ?_).trans ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    apply (mul_le_mul_of_nonneg_right (hBound s hs) (Real.exp_pos _).le).trans_eq
    simp only [Pi.add_apply, f, g, pow_one]
    ring
  · rw [integral_const_mul]
    simp only [Pi.add_apply]
    rw [integral_add hf hg]
    dsimp only [f, g, C]
    rw [expMoment_nat_integral 1 ht₀, expMoment_nat_integral 2 ht₀]
    norm_num
    calc
      B * ((t ^ 2)⁻¹ + 2 / t ^ 3) = B * (1 + 2 / t) / t ^ 2 := by ring
      _ ≤ B * (1 + 2 / a) / t ^ 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
          (add_le_add_right (div_le_div_of_nonneg_left zero_le_two ha ht) 1) hB) (sq_nonneg _)

end ACS12.GammaMeasure

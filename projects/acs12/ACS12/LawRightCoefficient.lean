import ACS12.LawRightOrder

/-! The full-ray same-law coefficient bound in the outer return. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaDeficit (lineDensity)

theorem lawRightTest_eq_moments {p L θ u t : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (ht : 0 < t) :
    lawRightTest p L θ u t =
      middleZ u * lawMoment p L θ 1 t + middleA u * lawMoment p L θ 1 (t + 1) -
        lawMoment p L θ 0 t + lawMoment p L θ 0 (t + 1) := by
  let w := lawDensity p L θ
  let f (s : ℝ) := w s * s * Real.exp (-s * t)
  let g (s : ℝ) := w s * s * Real.exp (-s * (t + 1))
  let h (s : ℝ) := w s * Real.exp (-s * t)
  let k (s : ℝ) := w s * Real.exp (-s * (t + 1))
  let μ := volume.restrict (Ioi (0 : ℝ))
  have ht' := add_pos ht zero_lt_one
  have hf : Integrable f μ := by simpa only [pow_one] using lawMoment_integrable hp hp₂ hL hθ ht 1
  have hg : Integrable g μ := by simpa only [pow_one] using lawMoment_integrable hp hp₂ hL hθ ht' 1
  have hh : Integrable h μ := by simpa only [pow_zero, mul_one] using lawMoment_integrable hp hp₂ hL hθ ht 0
  have hk : Integrable k μ := by simpa only [pow_zero, mul_one] using lawMoment_integrable hp hp₂ hL hθ ht' 0
  have hE (s : ℝ) : lawRightDensity p L θ u s * Real.exp (-s * t) =
      middleZ u * f s + middleA u * g s - 1 * h s - (-1) * k s := by
    simp only [lawRightDensity, middleRightDensity, middleA0, f, g, h, k, w,
      show -s * (t + 1) = -s * t + -s by ring, Real.exp_add]
    ring
  simp only [lawRightTest, signedLaplace, hE]
  rw [integral_four_terms hf hg hh hk]
  simp only [f, g, h, k, w, μ, lawMoment, pow_zero, pow_one, mul_one, one_mul, neg_one_mul, sub_neg_eq_add]

private noncomputable def referenceCoefficient (u : ℝ) : ℝ :=
  (1 + (u / (1 + u)) ^ 2 - 2 * ((6 / 25) * (2 - u)) * (1 - (u / (1 + u)) ^ 3)) / 3

private theorem referenceCoefficient_bounds {u : ℝ} (hu : 0 < u) (hu₁ : u < 1) :
    0 ≤ referenceCoefficient u ∧ referenceCoefficient u < 83 / 300 := by
  let R := u / (1 + u)
  let a := (6 / 25) * (2 - u)
  have hR : 0 < R := div_pos hu (by positivity)
  have hR' : R < 1 / 2 := (div_lt_iff₀ (by positivity : 0 < 1 + u)).mpr (by linarith)
  have ha₀ : 6 / 25 ≤ a := by dsimp only [a]; linarith
  have ha₁ : a ≤ 12 / 25 := by dsimp only [a]; linarith
  have ha : 0 ≤ a := (by norm_num : (0 : ℝ) ≤ 6 / 25).trans ha₀
  have hR₂ : R ^ 2 < 1 / 4 := by
    have h := pow_lt_pow_left₀ hR' hR.le (by decide : 2 ≠ 0)
    norm_num at h
    exact h
  have hR₃ : R ^ 3 ≤ 1 / 8 := by
    have h := pow_le_pow_left₀ hR.le hR'.le 3
    norm_num at h
    exact h
  have hC₀ : 2 * a * (1 - R ^ 3) ≤ 24 / 25 := by
    have h := mul_le_of_le_one_right (mul_nonneg zero_le_two ha)
      (sub_le_self 1 (pow_nonneg hR.le 3))
    linarith only [h, ha₁]
  have hC₁ : 21 / 50 ≤ 2 * a * (1 - R ^ 3) := by
    have h := mul_le_mul (show 2 * (6 / 25) ≤ 2 * a by linarith only [ha₀])
      (show 7 / 8 ≤ 1 - R ^ 3 by linarith only [hR₃])
      (by norm_num : (0 : ℝ) ≤ 7 / 8) (mul_nonneg zero_le_two ha)
    norm_num at h ⊢
    exact h
  change 0 ≤ (1 + R ^ 2 - 2 * a * (1 - R ^ 3)) / 3 ∧
    (1 + R ^ 2 - 2 * a * (1 - R ^ 3)) / 3 < 83 / 300
  constructor
  · linarith only [hC₀, sq_nonneg R]
  · linarith only [hC₁, hR₂]

private theorem referenceCoefficient_exact {L u : ℝ} (hL : 0 < L) (hu : 0 < u) :
    lawRightTest 2 L 0 u u =
      referenceCoefficient u * (u * lawMoment 2 L 0 1 u + lawMoment 2 L 0 0 u) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have ht := add_pos hu zero_lt_one
  rw [lawRightTest_eq_moments (by norm_num) le_rfl hL ⟨le_rfl, zero_le_one⟩ hu,
    lawMoment_zero_slope h2 hu, lawMoment_zero_slope h2 ht,
    lawMoment_zero_radial h2 hu, lawMoment_zero_radial h2 ht]
  have hE₂ (x : ℝ) (hx : 0 < x) : x ^ (-(2 : ℝ)) = (x ^ 2)⁻¹ := by
    rw [Real.rpow_neg hx.le, Real.rpow_two]
  have hE₃ (x : ℝ) (hx : 0 < x) : x ^ (-((2 : ℝ) + 1)) = (x ^ 3)⁻¹ := by
    rw [show (2 : ℝ) + 1 = 3 by norm_num, Real.rpow_neg hx.le,
      show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
  rw [hE₂ _ hu, hE₂ _ ht, hE₃ _ hu, hE₃ _ ht]
  unfold referenceCoefficient middleZ middleA
  field_simp [hu.ne', ht.ne', (add_pos zero_lt_one hu).ne']
  ring

private noncomputable def rightResidual (p L θ u c s : ℝ) : ℝ :=
  lawDensity p L θ s * (middleRightDensity u s - c * (u * s + 1)) * Real.exp (-s * u)

private theorem rightResidual_integral {p L θ u c : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hu : 0 < u) :
    IntegrableOn (rightResidual p L θ u c) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, rightResidual p L θ u c s) =
        lawRightTest p L θ u u - c * (u * lawMoment p L θ 1 u + lawMoment p L θ 0 u) := by
  let w := lawDensity p L θ
  let f (s : ℝ) := lawRightDensity p L θ u s * Real.exp (-s * u)
  let g (s : ℝ) := w s * s * Real.exp (-s * u)
  let h (s : ℝ) := w s * Real.exp (-s * u)
  let μ := volume.restrict (Ioi (0 : ℝ))
  have hf : Integrable f μ := lawRightDensity_integrable hp hp₂ hL hθ hu
  have hg : Integrable g μ := by simpa only [pow_one] using lawMoment_integrable hp hp₂ hL hθ hu 1
  have hh : Integrable h μ := by simpa only [pow_zero, mul_one] using lawMoment_integrable hp hp₂ hL hθ hu 0
  have hI : Integrable (fun s => u * g s + h s) μ := (hg.const_mul u).add hh
  have hEq (s : ℝ) : rightResidual p L θ u c s = f s - c * (u * g s + h s) := by
    simp only [rightResidual, lawRightDensity, f, g, h, w]
    ring
  constructor
  · exact (hf.sub (hI.const_mul c)).congr (Eventually.of_forall fun s => (hEq s).symm)
  · simp_rw [hEq]
    rw [integral_sub hf (hI.const_mul c), integral_const_mul, integral_add (hg.const_mul u) hh,
      integral_const_mul]
    simp only [f, g, h, w, μ, lawMoment, lawRightTest, signedLaplace, pow_one, pow_zero, mul_one]

private theorem lawDensity_two_zero (L s : ℝ) : lawDensity 2 L 0 s = s := by
  have hG : Real.Gamma 2 = 1 := by convert Real.Gamma_nat_eq_factorial 1 using 1 <;> norm_num
  simp only [lawDensity, sub_zero, one_mul, zero_mul, add_zero, lineDensity,
    show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, hG, div_one]

theorem lawRightCoefficient_lt {p L θ u : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hu : 0 < u) (hu₁ : u < 1) :
    lawRightTest p L θ u u / outerLawDenom p L θ u < 83 / 300 := by
  let c := referenceCoefficient u
  let W (s : ℝ) := s ^ 2 * Real.exp (-s * u)
  let Q (s : ℝ) := rightMultiplier (middleA u) (middleZ u) s - c * (u + s⁻¹)
  let R (s : ℝ) := lawDensity p L θ s / s
  have hp₀ := zero_lt_one.trans_le hp
  obtain ⟨hc, hc'⟩ := referenceCoefficient_bounds hu hu₁
  obtain ⟨hRef, hRefEq⟩ := rightResidual_integral (p := 2) (L := L) (θ := 0) (c := c)
    (by norm_num) le_rfl hL ⟨le_rfl, zero_le_one⟩ hu
  obtain ⟨hAct, hActEq⟩ := rightResidual_integral (c := c) hp hp₂ hL hθ hu
  have hW : IntegrableOn W (Ioi 0) := expMoment_nat_integrable 2 hu
  have hE (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) : W s * Q s = rightResidual 2 L 0 u c s := by
    simp only [W, Q, rightResidual, lawDensity_two_zero, middleRightDensity_eq hs]
    field_simp [(mem_Ioi.mp hs).ne']
  have hRE (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      W s * R s = lawDensity p L θ s * s * Real.exp (-s * u) := by
    dsimp only [W, R]
    field_simp [(mem_Ioi.mp hs).ne']
  have hPE (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) : W s * Q s * R s = rightResidual p L θ u c s := by
    simp only [W, Q, R, rightResidual, middleRightDensity_eq hs]
    field_simp [(mem_Ioi.mp hs).ne']
  have hQ : IntegrableOn (fun s => W s * Q s) (Ioi 0) := hRef.congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hE s hs).symm)
  have hR : IntegrableOn (fun s => W s * R s) (Ioi 0) := by
    have h := lawMoment_integrable hp hp₂ hL hθ hu 1
    simp only [pow_one] at h
    exact h.congr (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact (hRE s hs).symm)
  have hP : IntegrableOn (fun s => W s * Q s * R s) (Ioi 0) := hAct.congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hPE s hs).symm)
  have hQ₀ : (∫ s : ℝ in Ioi 0, W s * Q s) ≤ 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioi hE, hRefEq, referenceCoefficient_exact hL hu]
    change c * _ - c * _ ≤ 0
    exact sub_nonpos.mpr le_rfl
  have hQmono : MonotoneOn Q (Ioi 0) := by
    intro x hx y hy hxy
    have hx₀ : 0 < x := hx
    have hA := rightMultiplier_mono (z := middleZ u) ((middleA_le u).trans (by norm_num)) hx hy hxy
    have hInv : u + y⁻¹ ≤ u + x⁻¹ := add_le_add le_rfl (inv_anti₀ hx₀ hxy)
    have hB := mul_le_mul_of_nonneg_left hInv hc
    dsimp only [Q]
    exact sub_le_sub hA hB
  have h := integral_antitone_product_nonpos hW hQ hR hP
    (fun s hs => mul_pos (sq_pos_of_pos hs) (Real.exp_pos _))
    (fun s hs => (div_pos (lawDensity_pos hp₀ hL hθ hs) hs).le)
    hQmono (lawDensity_div_antitone hp₀ hp₂ hL hθ) hQ₀
  rw [setIntegral_congr_fun measurableSet_Ioi hPE, hActEq] at h
  have hS := mul_nonneg hc (lawSelf_nonneg hp₀ hL hθ)
  have hC : lawRightTest p L θ u u ≤ c * outerLawDenom p L θ u := by
    unfold outerLawDenom
    nlinarith only [h, hS]
  exact ((div_le_iff₀ (outerLawDenom_pos hp hp₂ hL hθ hu)).mpr hC).trans_lt hc'

end ACS12.GammaMeasure


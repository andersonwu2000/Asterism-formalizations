import ACS12.JointConeCurvature
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! The normalized positive part of the coupled pure-law gap derivative. -/
namespace ACS12.GammaMeasure

open Set MeasureTheory Filter CenteredCircle.AllN
open GammaDeficit (lineDensity)

noncomputable def conePricePolynomial (y : ℝ) : ℝ := (1 + y) / 6 + (47 / 500) * y ^ 2

noncomputable def coneCurvatureUpper (y : ℝ) : ℝ :=
  Real.exp (-y) * conePricePolynomial y

noncomputable def conePriceRadius (g t : ℝ) : ℝ := 1 - (9 / 10) * g * t

theorem coneCurvatureUpper_pos {y : ℝ} (hy : 0 ≤ y) : 0 < coneCurvatureUpper y := by
  unfold coneCurvatureUpper conePricePolynomial
  positivity

theorem coneCurvatureUpper_deriv (y : ℝ) :
    HasDerivAt coneCurvatureUpper
      (Real.exp (-y) * (y * (8 / 375 - (47 / 500) * y))) y := by
  have h := hasDerivAt_id y
  have hP := (((h.const_add 1).div_const 6).add ((h.pow 2).const_mul (47 / 500 : ℝ)))
  convert h.neg.exp.mul hP using 1
  simp only [id_eq,Pi.neg_apply,Pi.add_apply,Pi.pow_apply,one_mul,Nat.cast_ofNat,
    show (2 : ℕ) - 1 = 1 by decide,pow_one]
  ring

private theorem coneCurvatureUpper_scale_debit {g t x : ℝ} (hg : g ∈ Icc (0 : ℝ) (1 / 6))
    (ht : t ∈ Icc (0 : ℝ) 1) (hx : 0 < x) :
    -(1 / 100) * coneCurvatureUpper (conePriceRadius g t * x) ≤
      -(9 / 10) * t * x * (Real.exp (-(conePriceRadius g t * x)) *
        ((conePriceRadius g t * x) * (8 / 375 - (47 / 500) * (conePriceRadius g t * x)))) := by
  let r := conePriceRadius g t
  let y := r * x
  have hr : 17 / 20 ≤ r := by
    unfold r conePriceRadius
    have h := mul_le_mul hg.2 ht.2 ht.1 (by norm_num : (0 : ℝ) ≤ 1 / 6)
    norm_num at h
    linarith only [h]
  have hy : 0 ≤ y := mul_nonneg (by linarith only [hr]) hx.le
  have hP : (1 / 6 : ℝ) ≤ conePricePolynomial y := by
    unfold conePricePolynomial
    nlinarith only [hy,sq_nonneg y]
  have hE := (Real.exp_pos (-y)).le
  have hTX : 0 ≤ (9 / 10) * t * x := by have := ht.1; positivity
  change -(1 / 100) * coneCurvatureUpper y ≤
    -(9 / 10) * t * x * (Real.exp (-y) * (y * (8 / 375 - (47 / 500) * y)))
  by_cases h : (32 / 141 : ℝ) ≤ y
  · have hN : 8 / 375 - (47 / 500) * y ≤ 0 := by linarith only [h]
    have hRight : 0 ≤ -(9 / 10) * t * x * (Real.exp (-y) * (y * (8 / 375 - (47 / 500) * y))) := by
      rw [show -(9 / 10 : ℝ) * t * x = -((9 / 10 : ℝ) * t * x) by ring]
      exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hTX)
        (mul_nonpos_of_nonneg_of_nonpos hE (mul_nonpos_of_nonneg_of_nonpos hy hN))
    exact (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (coneCurvatureUpper_pos hy).le).trans hRight
  · have hY := le_of_not_ge h
    have hxY : x ≤ (20 / 17) * y := by
      change x ≤ (20 / 17) * (r * x)
      nlinarith only [mul_le_mul_of_nonneg_right hr hx.le]
    have hxU : x ≤ (20 / 17) * (32 / 141) := hxY.trans
      (mul_le_mul_of_nonneg_left hY (by norm_num))
    have htX := mul_le_mul_of_nonneg_right ht.2 hx.le
    have hD : y * (8 / 375 - (47 / 500) * y) ≤ (32 / 141) * (8 / 375) := by
      nlinarith only [hY,sq_nonneg y]
    have hM := mul_le_mul (show (9 / 10) * t * x ≤ (9 / 10) * ((20 / 17) * (32 / 141)) by
      linarith only [htX,hxU]) hD (mul_nonneg hy (by linarith only [hY]))
      (by norm_num : (0 : ℝ) ≤ (9 / 10) * ((20 / 17) * (32 / 141)))
    have hCmp : (9 / 10) * t * x * (y * (8 / 375 - (47 / 500) * y)) ≤
        (1 / 100) * conePricePolynomial y := by
      linarith only [hM,hP]
    unfold coneCurvatureUpper
    nlinarith only [mul_le_mul_of_nonneg_right hCmp hE]

private theorem conePriceNormalization_mono {p t x : ℝ} (hp : 1 ≤ p)
    (ht : t ∈ Icc (0 : ℝ) 1) (hx : 0 < x) :
    MonotoneOn (fun g : ℝ => (2 + g) ^ (p + 2) / (1 + g) *
      coneCurvatureUpper (conePriceRadius g t * x)) (Icc 0 (1 / 6)) := by
  let N (g : ℝ) := (2 + g) ^ (p + 2) / (1 + g)
  let Y (g : ℝ) := conePriceRadius g t * x
  let Q (g : ℝ) := coneCurvatureUpper (Y g)
  let c (g : ℝ) := (p + 2) / (2 + g) - 1 / (1 + g)
  let Q' (g : ℝ) := -(9 / 10) * t * x * (Real.exp (-Y g) * (Y g * (8 / 375 - (47 / 500) * Y g)))
  have hD (g : ℝ) (hg : g ∈ Icc (0 : ℝ) (1 / 6)) :
      HasDerivAt (fun v => N v * Q v) (N g * c g * Q g + N g * Q' g) g := by
    have h2 : 0 < 2 + g := by have := hg.1; positivity
    have h1 : 0 < 1 + g := by have := hg.1; positivity
    have h := hasDerivAt_id g
    have hND : HasDerivAt N (N g * c g) g := by
      have hQuot := ((h.const_add 2).rpow_const (p := p + 2) (Or.inl h2.ne')).div (h.const_add 1) h1.ne'
      convert hQuot using 1
      simp only [N,c,id_eq,mul_one,one_mul,Real.rpow_sub_one h2.ne']
      field_simp [h1.ne',h2.ne']
    have hYD : HasDerivAt Y (-(9 / 10) * t * x) g := by
      have hY' := (((h.const_mul (9 / 10 : ℝ)).mul_const t).const_sub 1).mul_const x
      convert hY' using 1
      simp only [id_eq,mul_one]
      ring
    have hQD : HasDerivAt Q (Q' g) g := by
      convert (coneCurvatureUpper_deriv (Y g)).comp g hYD using 1
      unfold Q'
      ring
    exact hND.mul hQD
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · exact fun g hg => (hD g hg).continuousAt.continuousWithinAt
  · exact fun g hg => (hD g (interior_subset hg)).differentiableAt.differentiableWithinAt
  · intro g hg
    have hG : g ∈ Icc (0 : ℝ) (1 / 6) := interior_subset hg
    change 0 ≤ deriv (fun v => N v * Q v) g
    rw [(hD g hG).deriv,mul_assoc,← mul_add]
    have h2 : 0 < 2 + g := by have := hG.1; positivity
    have h1 : 0 < 1 + g := by have := hG.1; positivity
    have hN : 0 ≤ N g := by unfold N; positivity
    have hC : 1 / 100 ≤ c g := by
      have hF : (18 / 13 : ℝ) ≤ (p + 2) / (2 + g) :=
        (le_div_iff₀ h2).mpr (by linarith only [hG.2,hp])
      have hS : 1 / (1 + g) ≤ 1 := (div_le_iff₀ h1).mpr (by linarith only [hG.1])
      unfold c
      linarith only [hF,hS]
    have hQ := coneCurvatureUpper_scale_debit hG ht hx
    have hQ₀ : 0 ≤ Q g := by
      apply (coneCurvatureUpper_pos _).le
      unfold Y conePriceRadius
      have h := mul_le_mul hG.2 ht.2 ht.1 (by norm_num : (0 : ℝ) ≤ 1 / 6)
      exact mul_nonneg (by linarith only [h]) hx.le
    exact mul_nonneg hN (by
      have h := mul_le_mul_of_nonneg_right hC hQ₀
      change -(1 / 100) * Q g ≤ Q' g at hQ
      linarith only [h,hQ])

noncomputable def conePositiveMoment (p g t : ℝ) : ℝ :=
  ∫ x : ℝ in Ioi 0, lineDensity p x * (x * coneCurvatureUpper (conePriceRadius g t * x) *
    ((3553 / 200000) * polyA x + jointPureLambda * Real.exp (-x) * polyA ((1 + g) * x)))

private theorem conePriceRadius_bounds {g t : ℝ} (hg : g ∈ Icc (0 : ℝ) (1 / 6))
    (ht : t ∈ Icc (0 : ℝ) 1) : conePriceRadius g t ∈ Icc (17 / 20) 1 := by
  have h := mul_le_mul hg.2 ht.2 ht.1 (by norm_num : (0 : ℝ) ≤ 1 / 6)
  have h₀ := mul_nonneg hg.1 ht.1
  constructor <;> unfold conePriceRadius <;> linarith only [h,h₀]

theorem conePositiveMoment_integrable {p g t : ℝ} (hp : 0 < p)
    (hg : g ∈ Icc (0 : ℝ) (1 / 6)) (ht : t ∈ Icc (0 : ℝ) 1) :
    IntegrableOn (fun x => lineDensity p x * (x * coneCurvatureUpper (conePriceRadius g t * x) *
      ((3553 / 200000) * polyA x + jointPureLambda * Real.exp (-x) * polyA ((1 + g) * x)))) (Ioi 0) := by
  let r := conePriceRadius g t
  let f (x : ℝ) := lineDensity p x * (x * coneCurvatureUpper (r * x) *
    ((3553 / 200000) * polyA x + jointPureLambda * Real.exp (-x) * polyA ((1 + g) * x)))
  let B (k : ℕ) (x : ℝ) := lineDensity p x * x ^ k * Real.exp (-x * r)
  have hR := conePriceRadius_bounds hg ht
  have hr : 0 < r := (by norm_num : (0 : ℝ) < 17 / 20).trans_le hR.1
  have hI (k : ℕ) : IntegrableOn (B k) (Ioi 0) := (lineDensity_moment hp hr k).1
  have hM : Measurable f := by
    unfold f lineDensity coneCurvatureUpper conePricePolynomial polyA
    fun_prop
  apply (((hI 1).add (hI 2)).add (hI 3)).mono' hM.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx₀ : 0 < x := hx
  have hX : 0 < (1 + g) * x := mul_pos (by have := hg.1; positivity) hx₀
  have hA (v : ℝ) (hv : 0 < v) : polyA v ≤ 1 := by
    unfold polyA
    exact sub_le_self _ (by positivity)
  let K := (3553 / 200000) * polyA x + jointPureLambda * Real.exp (-x) * polyA ((1 + g) * x)
  have hK₀ : 0 ≤ K := by
    unfold K jointPureLambda
    exact add_nonneg (mul_nonneg (by norm_num) (polyA_pos hx₀).le)
      (mul_nonneg (by positivity) (polyA_pos hX).le)
  have hK₁ : K ≤ 1 := by
    have hY := mul_le_mul (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx₀.le)) (hA _ hX)
      (polyA_pos hX).le (by norm_num : (0 : ℝ) ≤ 1)
    unfold K jointPureLambda
    nlinarith only [hY,hA _ hx₀]
  have hrx := mul_pos hr hx₀
  have hRX : r * x ≤ x := mul_le_of_le_one_left hx₀.le hR.2
  have hP : conePricePolynomial (r * x) ≤ 1 + x + x ^ 2 := by
    have hSq := pow_le_pow_left₀ hrx.le hRX 2
    unfold conePricePolynomial
    nlinarith only [hRX,hSq,hx₀,sq_nonneg x]
  have hP₀ : 0 ≤ conePricePolynomial (r * x) := by unfold conePricePolynomial; positivity
  have hρ := (lineDensity_pos hp hx₀).le
  have hEq : f x = (lineDensity p x * x * Real.exp (-x * r)) *
      (conePricePolynomial (r * x) * K) := by
    unfold f K coneCurvatureUpper
    rw [show -(r * x) = -x * r by ring]
    ring
  rw [hEq,Real.norm_of_nonneg (mul_nonneg (by positivity) (mul_nonneg hP₀ hK₀))]
  change _ ≤ B 1 x + B 2 x + B 3 x
  calc
    _ ≤ (lineDensity p x * x * Real.exp (-x * r)) * (1 + x + x ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (mul_le_of_le_one_right hP₀ hK₁).trans hP
    _ = _ := by unfold B; ring

private noncomputable def coneNormalizedPositive (p g t : ℝ) : ℝ :=
  (2 + g) ^ (p + 2) / (1 + g) * conePositiveMoment p g t

theorem coneNormalizedPositive_mono_gap {p t : ℝ} (hp : 1 ≤ p)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    MonotoneOn (fun g => coneNormalizedPositive p g t) (Icc 0 (1 / 6)) := by
  intro g hg G hG hgG
  let N (z : ℝ) := (2 + z) ^ (p + 2) / (1 + z)
  let A (z x : ℝ) := (3553 / 200000) * polyA x +
    jointPureLambda * Real.exp (-x) * polyA ((1 + z) * x)
  let F (z x : ℝ) := lineDensity p x * (x * coneCurvatureUpper (conePriceRadius z t * x) * A z x)
  have hp₀ := zero_lt_one.trans_le hp
  have hN {z : ℝ} (hz : z ∈ Icc (0 : ℝ) (1 / 6)) : 0 ≤ N z := by have := hz.1; unfold N; positivity
  have hI {z : ℝ} (hz : z ∈ Icc (0 : ℝ) (1 / 6)) : IntegrableOn (F z) (Ioi 0) :=
    conePositiveMoment_integrable hp₀ hz ht
  have hEq (z : ℝ) : coneNormalizedPositive p z t = ∫ x : ℝ in Ioi 0, N z * F z x := by
    rw [integral_const_mul]
    rfl
  change coneNormalizedPositive p g t ≤ coneNormalizedPositive p G t
  rw [hEq,hEq]
  apply setIntegral_mono_on ((hI hg).const_mul _) ((hI hG).const_mul _) measurableSet_Ioi
  intro x hx
  have hx₀ : 0 < x := hx
  have hgx : 0 < (1 + g) * x := mul_pos (by have := hg.1; positivity) hx₀
  have hGx : 0 < (1 + G) * x := mul_pos (by have := hG.1; positivity) hx₀
  have hA : A g x ≤ A G x := by
    have h := polyA_monotone_nonneg hgx.le hGx.le
      (mul_le_mul_of_nonneg_right (add_le_add_right hgG 1) hx₀.le)
    unfold A
    exact add_le_add_right (mul_le_mul_of_nonneg_left h
      (show 0 ≤ jointPureLambda * Real.exp (-x) by unfold jointPureLambda; positivity)) _
  have hA₀ : 0 ≤ A g x := by
    unfold A jointPureLambda
    exact add_nonneg (mul_nonneg (by norm_num) (polyA_pos hx₀).le)
      (mul_nonneg (by positivity) (polyA_pos hgx).le)
  have hQ := conePriceNormalization_mono hp ht hx₀ hg hG hgG
  change N g * coneCurvatureUpper (conePriceRadius g t * x) ≤
    N G * coneCurvatureUpper (conePriceRadius G t * x) at hQ
  have hQ₀ : 0 ≤ N G * coneCurvatureUpper (conePriceRadius G t * x) :=
    mul_nonneg (hN hG) (coneCurvatureUpper_pos
      (mul_nonneg ((by norm_num : (0 : ℝ) ≤ 17 / 20).trans (conePriceRadius_bounds hG ht).1) hx₀.le)).le
  have h := mul_le_mul hQ hA hA₀ hQ₀
  unfold F
  have hρ := (lineDensity_pos hp₀ hx₀).le
  nlinarith only [mul_le_mul_of_nonneg_left h (mul_nonneg hρ hx₀.le)]

theorem lineDensity_second_moment {p b : ℝ} (hp : 0 < p) (hb : 0 < b) :
    IntegrableOn (fun x => lineDensity p x * x ^ 2 * Real.exp (-x * b)) (Ioi 0) ∧
      (∫ x in Ioi 0, lineDensity p x * x ^ 2 * Real.exp (-x * b)) =
        p * (p + 1) * b ^ (-(p + 2)) := by
  obtain ⟨hI,hE⟩ := lineDensity_moment hp hb 2
  norm_num only [Nat.cast_ofNat] at hE
  have hΓ : Real.Gamma (p + 2) = p * (p + 1) * Real.Gamma p := by
    rw [show p + 2 = (p + 1) + 1 by ring,Real.Gamma_add_one (by positivity : 0 < p + 1).ne',
      Real.Gamma_add_one hp.ne']
    ring
  exact ⟨hI,by rw [hE,hΓ,mul_div_cancel_right₀ _ (Real.Gamma_pos_of_pos hp).ne']⟩

noncomputable def conePositiveRatio (p g t : ℝ) : ℝ :=
  coneNormalizedPositive p g t / (p * (p + 1))

theorem conePositiveRatio_mono_gap {p t : ℝ} (hp : 1 ≤ p) (ht : t ∈ Icc (0 : ℝ) 1) :
    MonotoneOn (fun g => conePositiveRatio p g t) (Icc 0 (1 / 6)) := by
  intro x hx y hy h
  exact div_le_div_of_nonneg_right (coneNormalizedPositive_mono_gap hp ht hx hy h)
    (by have := zero_lt_one.trans_le hp; positivity)

private noncomputable def coneGammaPower (p r z : ℝ) (k : ℕ) : ℝ :=
  (Real.Gamma (p + k) / Real.Gamma p) * (r + z) ^ (-(p + k))

private noncomputable def coneQMoment (p r z : ℝ) (k : ℕ) : ℝ :=
  coneGammaPower p r z k / 6 + r * coneGammaPower p r z (k + 1) / 6 +
    (47 / 500) * r ^ 2 * coneGammaPower p r z (k + 2)

private theorem coneQMoment_integral {p r z : ℝ} (hp : 0 < p) (hrz : 0 < r + z) (k : ℕ) :
    let f (x : ℝ) := lineDensity p x * x ^ k * Real.exp (-x * z) * coneCurvatureUpper (r * x)
    IntegrableOn f (Ioi 0) ∧ (∫ x in Ioi 0, f x) = coneQMoment p r z k := by
  let F (j : ℕ) (x : ℝ) := lineDensity p x * x ^ j * Real.exp (-x * (r + z))
  let f (x : ℝ) := lineDensity p x * x ^ k * Real.exp (-x * z) * coneCurvatureUpper (r * x)
  have hI (j : ℕ) : IntegrableOn (F j) (Ioi 0) := (lineDensity_moment hp hrz j).1
  have hE (j : ℕ) : (∫ x in Ioi 0, F j x) = coneGammaPower p r z j :=
    (lineDensity_moment hp hrz j).2
  have hEq (x : ℝ) : f x = (1 / 6) * F k x + (r / 6) * F (k + 1) x +
      ((47 / 500) * r ^ 2) * F (k + 2) x := by
    unfold f F coneCurvatureUpper conePricePolynomial
    rw [pow_add,pow_add,pow_one,show -x * (r + z) = -x * z + -(r * x) by ring,Real.exp_add]
    ring
  constructor
  · exact ((((hI k).const_mul _).add ((hI (k + 1)).const_mul _)).add ((hI (k + 2)).const_mul _)).congr
      (Eventually.of_forall fun x => (hEq x).symm)
  · change (∫ x in Ioi 0, f x) = _
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => hEq x),
      integral_add (f := fun x => (1 / 6) * F k x + (r / 6) * F (k + 1) x)
        (((hI k).const_mul _).add ((hI (k + 1)).const_mul _)) ((hI (k + 2)).const_mul _),
      integral_add ((hI k).const_mul _) ((hI (k + 1)).const_mul _),integral_const_mul,integral_const_mul,
      integral_const_mul,hE,hE,hE,coneQMoment]
    ring

private noncomputable def coneQDebit (p r z U : ℝ) : ℝ :=
  coneQMoment p r z 1 - coneQMoment p r (z + U) 1 - U * coneQMoment p r (z + U) 2

private theorem coneQDebit_integral {p r z U : ℝ} (hp : 0 < p) (hrz : 0 < r + z)
    (hU : 0 ≤ U) :
    let f (x : ℝ) := lineDensity p x * x * Real.exp (-x * z) * coneCurvatureUpper (r * x) * polyA (U * x)
    IntegrableOn f (Ioi 0) ∧ (∫ x in Ioi 0, f x) = coneQDebit p r z U := by
  let F (z : ℝ) (k : ℕ) (x : ℝ) := lineDensity p x * x ^ k * Real.exp (-x * z) * coneCurvatureUpper (r * x)
  let f (x : ℝ) := lineDensity p x * x * Real.exp (-x * z) * coneCurvatureUpper (r * x) * polyA (U * x)
  have hR : 0 < r + (z + U) := by linarith only [hrz,hU]
  obtain ⟨hA,hAE⟩ := coneQMoment_integral hp hrz 1
  obtain ⟨hB,hBE⟩ := coneQMoment_integral hp hR 1
  obtain ⟨hC,hCE⟩ := coneQMoment_integral hp hR 2
  change IntegrableOn (F z 1) (Ioi 0) at hA
  change IntegrableOn (F (z + U) 1) (Ioi 0) at hB
  change IntegrableOn (F (z + U) 2) (Ioi 0) at hC
  have hEq (x : ℝ) : f x = F z 1 x - F (z + U) 1 x - U * F (z + U) 2 x := by
    unfold f F polyA
    rw [show -x * (z + U) = -x * z + -(U * x) by ring,Real.exp_add]
    ring
  constructor
  · change IntegrableOn f (Ioi 0)
    exact ((hA.sub hB).sub (hC.const_mul U)).congr (Eventually.of_forall fun x => (hEq x).symm)
  · change (∫ x in Ioi 0, f x) = _
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => hEq x),
      integral_sub (f := fun x => F z 1 x - F (z + U) 1 x) (hA.sub hB) (hC.const_mul _),
      integral_sub hA hB,integral_const_mul]
    change (∫ x in Ioi 0, F z 1 x) - (∫ x in Ioi 0, F (z + U) 1 x) -
      U * (∫ x in Ioi 0, F (z + U) 2 x) = _
    rw [hAE,hBE,hCE,coneQDebit]

private theorem conePositiveMoment_eq {p g t : ℝ} (hp : 0 < p)
    (hg : g ∈ Icc (0 : ℝ) (1 / 6)) (ht : t ∈ Icc (0 : ℝ) 1) :
    conePositiveMoment p g t =
      (3553 / 200000) * coneQDebit p (conePriceRadius g t) 0 1 +
        jointPureLambda * coneQDebit p (conePriceRadius g t) 1 (1 + g) := by
  let r := conePriceRadius g t
  have hr : 0 < r := (by norm_num : (0 : ℝ) < 17 / 20).trans_le (conePriceRadius_bounds hg ht).1
  obtain ⟨hA,hAE⟩ := coneQDebit_integral (z := 0) hp (by linarith only [hr]) (by norm_num : (0 : ℝ) ≤ 1)
  obtain ⟨hB,hBE⟩ := coneQDebit_integral (r := r) (z := 1) hp (by positivity)
    (show 0 ≤ 1 + g by linarith only [hg.1])
  unfold conePositiveMoment
  change (∫ x : ℝ in Ioi 0, lineDensity p x * (x * coneCurvatureUpper (r * x) *
    ((3553 / 200000) * polyA x + jointPureLambda * Real.exp (-x) * polyA ((1 + g) * x)))) = _
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun x =>
    (3553 / 200000 : ℝ) * (lineDensity p x * x * Real.exp (-x * 0) * coneCurvatureUpper (r * x) * polyA (1 * x)) +
      jointPureLambda * (lineDensity p x * x * Real.exp (-x * 1) * coneCurvatureUpper (r * x) * polyA ((1 + g) * x)))
      (fun x _ => by simp only [mul_zero,Real.exp_zero,one_mul,mul_one]; ring),
    integral_add (hA.const_mul _) (hB.const_mul _),integral_const_mul,integral_const_mul,hAE,hBE]

noncomputable def conePositiveIntegral (p g : ℝ) : ℝ :=
  (9 / 10) * ∫ t in (0 : ℝ)..1, t * conePositiveRatio p g t

private theorem coneShiftPower_continuousOn {y q : ℝ} (hy : 0 ≤ y) :
    ContinuousOn (fun r => (r + y) ^ q) (Ioi 0) := by
  intro r hr
  exact (((hasDerivAt_id r).add_const y).rpow_const (p := q)
    (Or.inl (add_pos_of_pos_of_nonneg (show 0 < r from hr) hy).ne')).continuousAt.continuousWithinAt

private theorem coneQMoment_continuousOn {p z : ℝ} (hz : 0 ≤ z) (k : ℕ) :
    ContinuousOn (fun r => coneQMoment p r z k) (Ioi 0) := by
  have hP (j : ℕ) : ContinuousOn (fun r => coneGammaPower p r z j) (Ioi 0) :=
    (coneShiftPower_continuousOn hz).const_mul _
  unfold coneQMoment
  exact (((hP k).div_const 6).add ((continuousOn_id.mul (hP (k + 1))).div_const 6)).add
    (((continuousOn_id.pow 2).const_mul (47 / 500)).mul (hP (k + 2)))

private theorem coneQDebit_continuousOn {p z U : ℝ} (hz : 0 ≤ z) (hU : 0 ≤ U) :
    ContinuousOn (fun r => coneQDebit p r z U) (Ioi 0) := by
  have hQ (z : ℝ) (hz : 0 ≤ z) (k : ℕ) := coneQMoment_continuousOn (p := p) hz k
  unfold coneQDebit
  exact ((hQ z hz 1).sub (hQ (z + U) (add_nonneg hz hU) 1)).sub
    ((hQ (z + U) (add_nonneg hz hU) 2).const_mul U)

theorem conePositiveMoment_continuousOn {p g : ℝ} (hp : 0 < p) (hg : g ∈ Icc (0 : ℝ) (1 / 6)) :
    ContinuousOn (conePositiveMoment p g) (Icc 0 1) := by
  apply ContinuousOn.congr (f := fun t =>
      ((3553 / 200000) * coneQDebit p (conePriceRadius g t) 0 1 +
        jointPureLambda * coneQDebit p (conePriceRadius g t) 1 (1 + g)))
  · have hR : ContinuousOn (conePriceRadius g) (Icc (0 : ℝ) 1) := by unfold conePriceRadius; fun_prop
    have hMap : MapsTo (conePriceRadius g) (Icc (0 : ℝ) 1) (Ioi 0) := by
      intro t ht
      exact (by norm_num : (0 : ℝ) < 17 / 20).trans_le (conePriceRadius_bounds hg ht).1
    have hA := (coneQDebit_continuousOn (p := p) (z := 0) (U := 1) (by norm_num) (by norm_num)).comp hR hMap
    have hB := (coneQDebit_continuousOn (p := p) (z := 1) (U := 1 + g) (by norm_num)
      (by linarith only [hg.1])).comp hR hMap
    exact (hA.const_mul (3553 / 200000)).add (hB.const_mul jointPureLambda)
  · intro t ht
    exact conePositiveMoment_eq hp hg ht

/-- A monomial antiderivative, including the logarithm when the exponent is zero. -/
private noncomputable def coneIntPrimitive (a : ℤ) (y : ℝ) : ℝ :=
  if a = 0 then Real.log y else y ^ a / (a : ℝ)

private theorem coneIntPrimitive_deriv (a : ℤ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (coneIntPrimitive a) (y ^ (a-1)) y := by
  by_cases h : a = 0
  · subst a
    simpa [coneIntPrimitive, one_div] using Real.hasDerivAt_log hy.ne'
  · have hA : (a : ℝ) ≠ 0 := by exact_mod_cast h
    rw [show coneIntPrimitive a = (fun x : ℝ => x^a/(a:ℝ)) by funext x; simp [coneIntPrimitive,h]]
    simpa [hA] using (hasDerivAt_zpow a y (Or.inl hy.ne')).div_const (a : ℝ)

private noncomputable def coneIntEndpointPrimitive (p j k : ℕ) (z y : ℝ) : ℝ :=
  ∑ l ∈ Finset.range (j+1), (j.choose l : ℝ) * (-z)^(j-l) *
    ((1+z)*coneIntPrimitive ((l : ℤ)-p-k+1) y - coneIntPrimitive ((l : ℤ)-p-k+2) y)

private theorem coneIntEndpointPrimitive_deriv (p j k : ℕ) (z y : ℝ) (hy : 0 < y) :
    HasDerivAt (coneIntEndpointPrimitive p j k z) ((1+z-y)*(y-z)^j*y^(-((p : ℝ)+k))) y := by
  have hD (l : ℕ) : HasDerivAt (fun y : ℝ =>
      (j.choose l : ℝ)*(-z)^(j-l)*
        ((1+z)*coneIntPrimitive ((l : ℤ)-p-k+1) y - coneIntPrimitive ((l : ℤ)-p-k+2) y))
      ((j.choose l : ℝ)*(-z)^(j-l)*((1+z-y)*y^(-((p : ℝ)+k))*y^l)) y := by
    have h₁ := (coneIntPrimitive_deriv ((l : ℤ)-p-k+1) hy).const_mul (1+z)
    have h₂ := coneIntPrimitive_deriv ((l : ℤ)-p-k+2) hy
    convert (h₁.sub h₂).const_mul ((j.choose l : ℝ)*(-z)^(j-l)) using 1
    have hL : y ^ (((l : ℤ)-p-k+1)-1) = y^(-((p : ℝ)+k))*y^l := by
      rw [← Real.rpow_natCast,← Real.rpow_add hy,← Real.rpow_intCast]
      congr 1
      push_cast
      ring
    have hR : y ^ (((l : ℤ)-p-k+2)-1) = y^(-((p : ℝ)+k))*y^l*y := by
      rw [← Real.rpow_natCast,← Real.rpow_add hy,← Real.rpow_add_one hy.ne',← Real.rpow_intCast]
      congr 1
      push_cast
      ring
    rw [hL,hR]
    ring
  have h := HasDerivAt.fun_sum (u := Finset.range (j+1)) (fun l _ => hD l)
  convert h using 1
  rw [show y-z = y + -z by ring,add_pow,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  ring

private noncomputable def coneIntEndpointJ (p : ℕ) (j k : ℕ) (z : ℝ) : ℝ :=
  coneIntEndpointPrimitive p j k z (1 + z) - coneIntEndpointPrimitive p j k z (17 / 20 + z)

private theorem coneIntEndpointJ_eq (p : ℕ) (j k : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    (∫ r in (17 / 20 : ℝ)..1, (1 - r) * r ^ j * (r + z) ^ (-((p : ℝ) + k : ℝ))) =
      coneIntEndpointJ p j k z := by
  let f (r : ℝ) := (1 - r) * r ^ j * (r + z) ^ (-((p : ℝ) + k : ℝ))
  let F (r : ℝ) := coneIntEndpointPrimitive p j k z (r + z)
  have hD (r : ℝ) (hr : 0 < r) : HasDerivAt F (f r) r := by
    convert (coneIntEndpointPrimitive_deriv p j k z (r + z) (add_pos_of_pos_of_nonneg hr hz)).comp r
      ((hasDerivAt_id r).add_const z) using 1
    simp only [id_eq,mul_one,add_sub_cancel_right]
    unfold f
    ring
  have hC : ContinuousOn f (Icc (17 / 20 : ℝ) 1) := by
    unfold f
    exact ((by fun_prop : ContinuousOn (fun r : ℝ => (1 - r) * r ^ j) (Icc (17 / 20 : ℝ) 1))).mul
      ((coneShiftPower_continuousOn hz).mono (fun _ hr => (by norm_num : (0 : ℝ) < 17 / 20).trans_le hr.1))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (17 / 20 : ℝ)) (b := 1)
    (fun r hr => hD r (by norm_num at hr; linarith only [hr.1]))
    (hC.intervalIntegrable_of_Icc (by norm_num))
  exact h

private noncomputable def coneIntEndpointMoment (p : ℕ) (z : ℝ) (k : ℕ) : ℝ :=
  (Real.Gamma ((p : ℝ) + k) / Real.Gamma (p : ℝ)) * coneIntEndpointJ p 0 k z / 6 +
    (Real.Gamma ((p : ℝ) + (k + 1 : ℕ)) / Real.Gamma (p : ℝ)) * coneIntEndpointJ p 1 (k + 1) z / 6 +
    (47 / 500) * (Real.Gamma ((p : ℝ) + (k + 2 : ℕ)) / Real.Gamma (p : ℝ)) * coneIntEndpointJ p 2 (k + 2) z

private theorem coneIntEndpointMoment_eq (p : ℕ) {z : ℝ} (hz : 0 ≤ z) (k : ℕ) :
    (∫ r in (17 / 20 : ℝ)..1, (1 - r) * coneQMoment (p : ℝ) r z k) =
      coneIntEndpointMoment p z k := by
  let F (j l : ℕ) (r : ℝ) := (1 - r) * r ^ j * (r + z) ^ (-((p : ℝ) + l : ℝ))
  let Γ (l : ℕ) := Real.Gamma ((p : ℝ) + l) / Real.Gamma (p : ℝ)
  have hI (j l : ℕ) : IntervalIntegrable (F j l) volume (17 / 20 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (17 / 20 : ℝ) ≤ 1)
    unfold F
    exact ((by fun_prop : ContinuousOn (fun r : ℝ => (1 - r) * r ^ j) (Icc (17 / 20 : ℝ) 1))).mul
      ((coneShiftPower_continuousOn hz).mono (fun _ hr => (by norm_num : (0 : ℝ) < 17 / 20).trans_le hr.1))
  have hEq (r : ℝ) : (1 - r) * coneQMoment (p : ℝ) r z k =
      (Γ k / 6) * F 0 k r + (Γ (k + 1) / 6) * F 1 (k + 1) r +
        ((47 / 500) * Γ (k + 2)) * F 2 (k + 2) r := by
    unfold coneQMoment coneGammaPower F Γ
    simp only [pow_zero,pow_one]
    ring
  simp_rw [hEq]
  rw [intervalIntegral.integral_add (((hI 0 k).const_mul _).add ((hI 1 (k + 1)).const_mul _))
      ((hI 2 (k + 2)).const_mul _),intervalIntegral.integral_add ((hI 0 k).const_mul _)
      ((hI 1 (k + 1)).const_mul _),intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have hE (j l : ℕ) : (∫ r in (17 / 20 : ℝ)..1, F j l r) = coneIntEndpointJ p j l z :=
    coneIntEndpointJ_eq p j l hz
  rw [hE,hE,hE]
  unfold coneIntEndpointMoment Γ
  ring

private noncomputable def coneIntEndpointDebit (p : ℕ) (z U : ℝ) : ℝ :=
  coneIntEndpointMoment p z 1 - coneIntEndpointMoment p (z + U) 1 - U * coneIntEndpointMoment p (z + U) 2

private theorem coneIntEndpointDebit_eq (p : ℕ) {z U : ℝ} (hz : 0 ≤ z) (hU : 0 ≤ U) :
    (∫ r in (17 / 20 : ℝ)..1, (1 - r) * coneQDebit (p : ℝ) r z U) =
      coneIntEndpointDebit p z U := by
  let F (z : ℝ) (k : ℕ) (r : ℝ) := (1 - r) * coneQMoment (p : ℝ) r z k
  have hI (z : ℝ) (hz : 0 ≤ z) (k : ℕ) : IntervalIntegrable (F z k) volume (17 / 20 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (17 / 20 : ℝ) ≤ 1)
    unfold F
    exact ((by fun_prop : ContinuousOn (fun r : ℝ => 1 - r) (Icc (17 / 20 : ℝ) 1))).mul
      ((coneQMoment_continuousOn hz k).mono (fun _ hr => (by norm_num : (0 : ℝ) < 17 / 20).trans_le hr.1))
  have hEq (r : ℝ) : (1 - r) * coneQDebit (p : ℝ) r z U =
      F z 1 r - F (z + U) 1 r - U * F (z + U) 2 r := by unfold F coneQDebit; ring
  simp_rw [hEq]
  have hZU := add_nonneg hz hU
  rw [intervalIntegral.integral_sub ((hI z hz 1).sub (hI (z + U) hZU 1)) ((hI (z + U) hZU 2).const_mul _),
    intervalIntegral.integral_sub (hI z hz 1) (hI (z + U) hZU 1),intervalIntegral.integral_const_mul]
  exact congrArg₂ (fun x y : ℝ => x - y) (congrArg₂ (· - ·) (coneIntEndpointMoment_eq p hz 1)
    (coneIntEndpointMoment_eq p (add_nonneg hz hU) 1))
    (congrArg (U * ·) (coneIntEndpointMoment_eq p (add_nonneg hz hU) 2))

private theorem conePositiveIntegral_int_endpoint_eq (p : ℕ) (hp : 0 < p) :
    conePositiveIntegral (p : ℝ) (1 / 6) =
      40 * ((3553 / 200000) * coneIntEndpointDebit p 0 1 + jointPureLambda * coneIntEndpointDebit p 1 (7 / 6)) /
        ((7 / 6) * (p : ℝ) * (p + 1) * (13 / 6 : ℝ) ^ (-((p : ℝ) + 2))) := by
  have hp₀ : 0 < (p : ℝ) := by exact_mod_cast hp
  let Q (r : ℝ) := (3553 / 200000) * coneQDebit (p : ℝ) r 0 1 + jointPureLambda * coneQDebit (p : ℝ) r 1 (7 / 6)
  let F (r : ℝ) := (1 - r) * Q r
  let b : ℝ := 13 / 6
  let k : ℝ := b ^ ((p : ℝ) + 2) / ((7 / 6) * (p : ℝ) * (p + 1))
  have hRad (t : ℝ) : conePriceRadius (1 / 6) t = -(3 / 20) * t + 1 := by unfold conePriceRadius; ring
  have hCmp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      t * conePositiveRatio (p : ℝ) (1 / 6) t = ((20 / 3) * k) * F (-(3 / 20) * t + 1) := by
    unfold conePositiveRatio coneNormalizedPositive
    rw [conePositiveMoment_eq hp₀ (by norm_num) ht,hRad]
    unfold F Q k b
    field_simp [hp₀.ne', show (p:ℝ)+1 ≠ 0 by positivity]
    <;> ring
  unfold conePositiveIntegral
  rw [intervalIntegral.integral_congr (by rw [uIcc_of_le zero_le_one]; exact hCmp),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_mul_add F (by norm_num : -(3 / 20 : ℝ) ≠ 0) 1]
  norm_num only [mul_zero,zero_add,mul_one,show -(3 / 20 : ℝ) + 1 = 17 / 20 by norm_num,smul_eq_mul]
  rw [intervalIntegral.integral_symm (a := (17 / 20 : ℝ)) (b := 1)]
  let A (r : ℝ) := (1 - r) * coneQDebit (p : ℝ) r 0 1
  let B (r : ℝ) := (1 - r) * coneQDebit (p : ℝ) r 1 (7 / 6)
  have hAB (z U : ℝ) (hz : 0 ≤ z) (hU : 0 ≤ U) :
      IntervalIntegrable (fun r => (1 - r) * coneQDebit (p : ℝ) r z U) volume (17 / 20 : ℝ) 1 := by
    have hC := (coneQDebit_continuousOn (p := (p : ℝ)) hz hU).mono
      (fun r (hr : r ∈ Icc (17 / 20 : ℝ) 1) => (by norm_num : (0 : ℝ) < 17 / 20).trans_le hr.1)
    exact ((by fun_prop : ContinuousOn (fun r : ℝ => 1 - r) (Icc (17 / 20 : ℝ) 1)).mul hC).intervalIntegrable_of_Icc (by norm_num)
  have hF : (∫ r in (17 / 20 : ℝ)..1, F r) =
      (3553 / 200000) * coneIntEndpointDebit p 0 1 + jointPureLambda * coneIntEndpointDebit p 1 (7 / 6) := by
    have hE (r : ℝ) : F r = (3553 / 200000) * A r + jointPureLambda * B r := by unfold F Q A B; ring
    simp_rw [hE]
    rw [intervalIntegral.integral_add ((hAB 0 1 (by norm_num) (by norm_num)).const_mul _)
      ((hAB 1 (7 / 6) (by norm_num) (by norm_num)).const_mul _),intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    change _ * (∫ r in (17 / 20 : ℝ)..1, (1 - r) * coneQDebit (p : ℝ) r 0 1) +
      _ * (∫ r in (17 / 20 : ℝ)..1, (1 - r) * coneQDebit (p : ℝ) r 1 (7 / 6)) = _
    rw [coneIntEndpointDebit_eq p (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1),
      coneIntEndpointDebit_eq p (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 7 / 6)]
  rw [hF]
  unfold k b
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 13 / 6)]
  simp only [inv_inv,div_eq_mul_inv,mul_inv_rev]
  ring

private theorem polyA_laplace_average (U x : ℝ) :
    polyA (U*x) = x^2 * ∫ v in (0 : ℝ)..1, U^2*v*Real.exp (-x*(U*v)) := by
  let F (v : ℝ) := polyA (U*x*v)
  have hD (v : ℝ) : HasDerivAt F (x^2*(U^2*v*Real.exp (-x*(U*v)))) v := by
    have h := (hasDerivAt_polyA (U*x*v)).comp v ((hasDerivAt_id v).const_mul (U*x))
    convert h using 1
    simp only [id_eq,mul_one]
    rw [show -(U*x*v) = -x*(U*v) by ring]
    ring
  have hI : Continuous fun v : ℝ => x^2*(U^2*v*Real.exp (-x*(U*v))) := by fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (fun v _ => hD v) (hI.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul] at h
  simpa [F,polyA] using h.symm

private theorem coneQDebit_mellin {p r z U : ℝ} (hp : 0 < p) (hrz : 0 < r+z)
    (hU : 0 ≤ U) :
    coneQDebit p r z U = ∫ v in (0 : ℝ)..1, U^2*v*coneQMoment p r (z+U*v) 3 := by
  let μ := volume.restrict (Ioi (0:ℝ))
  let ν := volume.restrict (Ioc (0:ℝ) 1)
  let D (x : ℝ) := lineDensity p x*x^3*Real.exp (-x*z)*coneCurvatureUpper (r*x)
  let F (s : ℝ × ℝ) := U^2*s.2*(D s.1*Real.exp (-s.1*(U*s.2)))
  have hD : Integrable D μ := (coneQMoment_integral hp hrz 3).1
  have hF : Integrable F (μ.prod ν) := by
    have hM : Measurable F := by unfold F D lineDensity coneCurvatureUpper conePricePolynomial; fun_prop
    apply (hD.norm.mul_prod (integrable_const (μ := ν) (U^2))).mono' hM.aestronglyMeasurable
    have hS : ∀ᵐ s : ℝ × ℝ ∂μ.prod ν, 0 < s.1 ∧ s.2 ∈ Ioc (0:ℝ) 1 :=
      (Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)).and
      (Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc))
    filter_upwards [hS] with s hs
    have hC : U^2*s.2 ≤ U^2 := mul_le_of_le_one_right (sq_nonneg U) hs.2.2
    have hE : Real.exp (-s.1*(U*s.2)) ≤ 1 := Real.exp_le_one_iff.mpr (by
      rw [neg_mul]; exact neg_nonpos.mpr (mul_nonneg hs.1.le (mul_nonneg hU hs.2.1.le)))
    change ‖F s‖ ≤ ‖D s.1‖*U^2
    simp only [F,norm_mul,Real.norm_of_nonneg (mul_nonneg (sq_nonneg U) hs.2.1.le),
      Real.norm_of_nonneg (Real.exp_pos _).le]
    exact (mul_le_mul hC (mul_le_of_le_one_right (norm_nonneg _) hE)
      (by positivity) (sq_nonneg U)).trans_eq (mul_comm _ _)
  have hRow (x : ℝ) (hx : 0 < x) :
      (∫ v, F (x,v) ∂ν) = lineDensity p x*x*Real.exp (-x*z)*coneCurvatureUpper (r*x)*polyA (U*x) := by
    have hEq (v : ℝ) : F (x,v) = D x*(U^2*v*Real.exp (-x*(U*v))) := by unfold F; ring
    simp_rw [hEq]
    rw [integral_const_mul,← intervalIntegral.integral_of_le zero_le_one,polyA_laplace_average]
    unfold D
    ring
  have hCol (v : ℝ) (hv : v ∈ Ioc (0:ℝ) 1) :
      (∫ x, F (x,v) ∂μ) = U^2*v*coneQMoment p r (z+U*v) 3 := by
    have hEq (x : ℝ) : F (x,v) = U^2*v*(lineDensity p x*x^3*Real.exp (-x*(z+U*v))*coneCurvatureUpper (r*x)) := by
      unfold F D
      rw [show -x*(z+U*v) = -x*z + -x*(U*v) by ring,Real.exp_add]
      ring
    simp_rw [hEq]
    rw [integral_const_mul, (coneQMoment_integral hp (show 0 < r+(z+U*v) by
      have h := mul_nonneg hU hv.1.le; linarith only [hrz,h]) 3).2]
  have hRS := (integral_prod F hF).symm.trans (integral_prod_symm F hF)
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => hRow x hx),
      setIntegral_congr_fun measurableSet_Ioc hCol] at hRS
  rw [intervalIntegral.integral_of_le zero_le_one, ← hRS, ← (coneQDebit_integral hp hrz hU).2]

/-- The cubic Gamma ratio and the exponential factor matching the two endpoint bounds. -/
private noncomputable def coneMellinScale (p : ℝ) : ℝ :=
  (p+2)*(p+3)*(p+4)*(158/125 : ℝ)^(p-1)

private noncomputable def coneMellinKernel (b d p : ℝ) (j : Fin 3) : ℝ :=
  Real.exp ((p+2)*Real.log b - (p+3+(j:ℕ))*Real.log d - (p-1)*Real.log (158/125) -
    (if (j:ℕ)<1 then Real.log (p+3) else 0) - (if (j:ℕ)<2 then Real.log (p+4) else 0))

/-- Exponential normalization makes the endpoint bounds equal. Convexity follows
from the affine exponent and the negative logarithms from the Gamma ratios. -/
private theorem coneMellinKernel_convex (b d : ℝ) (j : Fin 3) :
    ConvexOn ℝ (Ici 1) (fun p => coneMellinKernel b d p j) := by
  refine ⟨convex_Ici _,?_⟩
  intro p hp q hq a c ha hc hac
  have hZ : 1 ≤ a*p+c*q := (convex_Ici (1:ℝ)) hp hq ha hc hac
  have hLog (k : ℝ) (hk : 0 ≤ k) :
      a*Real.log (p+k)+c*Real.log (q+k) ≤ Real.log (a*p+c*q+k) := by
    have hp₀ : 0 < p+k := by have : 1 ≤ p := hp; linarith
    have hq₀ : 0 < q+k := by have : 1 ≤ q := hq; linarith
    have h := strictConcaveOn_log_Ioi.concaveOn.2 hp₀ hq₀ ha hc hac
    simp only [smul_eq_mul] at h
    rwa [show a*(p+k)+c*(q+k)=a*p+c*q+k by linear_combination k*hac] at h
  let L (p : ℝ) := (p+2)*Real.log b - (p+3+(j:ℕ))*Real.log d - (p-1)*Real.log (158/125) -
    (if (j:ℕ)<1 then Real.log (p+3) else 0) - (if (j:ℕ)<2 then Real.log (p+4) else 0)
  have hLin : L (a*p+c*q) ≤ a*L p+c*L q := by
    have h₃ := hLog 3 (by norm_num)
    have h₄ := hLog 4 (by norm_num)
    have hB := congrArg (Real.log b * ·) hac
    have hD := congrArg (((3:ℝ)+(j:ℕ))*Real.log d * ·) hac
    have hE := congrArg (Real.log (158/125) * ·) hac
    unfold L
    split_ifs <;> linarith only [h₃,h₄,hB,hD,hE]
  have h := convexOn_exp.2 (mem_univ (L p)) (mem_univ (L q)) ha hc hac
  simp only [smul_eq_mul] at h ⊢
  exact (Real.exp_le_exp.mpr hLin).trans h

private theorem coneMellinKernel_eq {b d p : ℝ} (hb : 0 < b) (hd : 0 < d) (hp : 1 ≤ p) (j : Fin 3) :
    coneMellinKernel b d p j =
      (b^(p+2)/(p*(p+1)*coneMellinScale p)) * coneGammaPower p d 0 (3+j) := by
  have hp₀ := zero_lt_one.trans_le hp
  have hG₀ := Real.Gamma_add_one hp₀.ne'
  have hG₁ := Real.Gamma_add_one (show p+1 ≠ 0 by positivity)
  have hG₂ := Real.Gamma_add_one (show p+2 ≠ 0 by positivity)
  have hG₃ := Real.Gamma_add_one (show p+3 ≠ 0 by positivity)
  have hG₄ := Real.Gamma_add_one (show p+4 ≠ 0 by positivity)
  have hΓ := (Real.Gamma_pos_of_pos hp₀).ne'
  have hRate : 0 < (158/125:ℝ) := by norm_num
  have hRate' := (Real.rpow_pos_of_pos hRate (p-1)).ne'
  have hG₀' : Real.Gamma (p+1) = p*Real.Gamma p := hG₀
  have hG₁' : Real.Gamma (p+2) = (p+1)*Real.Gamma (p+1) := by convert hG₁ using 2; ring
  have hG₂' : Real.Gamma (p+3) = (p+2)*Real.Gamma (p+2) := by convert hG₂ using 2; ring
  have hG₃' : Real.Gamma (p+4) = (p+3)*Real.Gamma (p+3) := by convert hG₃ using 2; ring
  have hG₄' : Real.Gamma (p+5) = (p+4)*Real.Gamma (p+4) := by convert hG₄ using 2; ring
  have hExp (x t : ℝ) (hx : 0 < x) : Real.exp (t*Real.log x) = x^t := by
    rw [Real.rpow_def_of_pos hx,mul_comm]
  fin_cases j <;> norm_num [coneMellinKernel,coneMellinScale,coneGammaPower,Real.exp_sub,add_zero,
      hG₀',hG₁',hG₂',hG₃',hG₄',hExp b _ hb,hExp d _ hd,hExp _ _ hRate] <;>
    (try simp only [Real.exp_log (show 0 < p+3 by positivity),Real.exp_log (show 0 < p+4 by positivity)])
  all_goals
    first | rw [show (-3 + -p : ℝ) = -(p+3) by ring, Real.rpow_neg hd.le]
          | rw [show (-4 + -p : ℝ) = -(p+3+1) by ring, Real.rpow_neg hd.le]
          | rw [show (-5 + -p : ℝ) = -(p+3+2) by ring, Real.rpow_neg hd.le]
    field_simp [hp₀.ne',show p+1 ≠ 0 by positivity,show p+2 ≠ 0 by positivity,
      show p+3 ≠ 0 by positivity,show p+4 ≠ 0 by positivity,hΓ,hRate']
    <;> ring

private noncomputable def coneMellinCoeff (r : ℝ) (j : Fin 3) : ℝ :=
  ![1/6, r/6, (47/500)*r^2] j

private noncomputable def coneMellinNormalizer (b p : ℝ) : ℝ :=
  b^(p+2)/(p*(p+1)*coneMellinScale p)

private theorem coneMellinDebit_convex {b r z U : ℝ} (hb : 0 < b) (hr : 0 < r) (hz : 0 ≤ z) (hU : 0 ≤ U) :
    ConvexOn ℝ (Ici 1) (fun p => coneMellinNormalizer b p * coneQDebit p r z U) := by
  refine ⟨convex_Ici _,?_⟩
  intro p hp q hq a c ha hc hac
  let T (p v : ℝ) := coneMellinNormalizer b p*(U^2*v*coneQMoment p r (z+U*v) 3)
  have hI (p : ℝ) : IntervalIntegrable (T p) volume 0 1 := by
    have hD (j : ℕ) : ContinuousOn (fun v : ℝ => (r+(z+U*v))^(-(p+j))) (Icc 0 1) := by
      apply ContinuousOn.rpow_const (by fun_prop)
      intro v hv
      exact Or.inl (add_pos_of_pos_of_nonneg hr (add_nonneg hz (mul_nonneg hU hv.1))).ne'
    unfold T coneQMoment coneGammaPower
    apply ContinuousOn.intervalIntegrable_of_Icc (μ := volume) zero_le_one
    have h₀ := (continuousOn_const (c := Real.Gamma (p+3)/Real.Gamma p)).mul (hD 3)
    have A := h₀.div_const (6:ℝ)
    have h₁ := ((continuousOn_const (c := r)).mul ((continuousOn_const (c := Real.Gamma (p+4)/Real.Gamma p)).mul (hD 4))).div_const (6:ℝ)
    have h₂ := (continuousOn_const (c := (47/500:ℝ)*r^2)).mul ((continuousOn_const (c := Real.Gamma (p+5)/Real.Gamma p)).mul (hD 5))
    exact continuousOn_const.mul ((by fun_prop : ContinuousOn (fun v : ℝ => U^2*v) _).mul
      ((A.add h₁).add h₂))
  have hEq (p : ℝ) (hp : 1 ≤ p) :
      coneMellinNormalizer b p * coneQDebit p r z U = ∫ v in (0 : ℝ)..1, T p v := by
    rw [coneQDebit_mellin (zero_lt_one.trans_le hp) (add_pos_of_pos_of_nonneg hr hz) hU,
      ← intervalIntegral.integral_const_mul]
  have hpq : 1 ≤ a*p+c*q := (convex_Ici (1:ℝ)) hp hq ha hc hac
  simp only [smul_eq_mul]
  rw [hEq p hp,hEq q hq,hEq _ hpq, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add ((hI p).const_mul a) ((hI q).const_mul c)]
  apply intervalIntegral.integral_mono_on zero_le_one (hI _) (((hI p).const_mul a).add ((hI q).const_mul c))
  intro v hv
  let d := r+(z+U*v)
  have hd : 0 < d := add_pos_of_pos_of_nonneg hr (add_nonneg hz (mul_nonneg hU hv.1))
  have hC (j : Fin 3) : 0 ≤ coneMellinCoeff r j := by fin_cases j <;> norm_num [coneMellinCoeff] <;> positivity
  have hT (p : ℝ) (hp : 1 ≤ p) : T p v = U^2*v * ∑ j : Fin 3, coneMellinCoeff r j*coneMellinKernel b d p j := by
    unfold T
    simp_rw [coneMellinKernel_eq hb hd hp]
    simp [Fin.sum_univ_three,coneMellinCoeff,coneQMoment,coneMellinNormalizer,coneGammaPower,d]
    ring
  rw [hT p hp,hT q hq,hT _ hpq]
  have hSum : (∑ j : Fin 3, coneMellinCoeff r j*coneMellinKernel b d (a*p+c*q) j) ≤
      a*(∑ j : Fin 3, coneMellinCoeff r j*coneMellinKernel b d p j) +
        c*(∑ j : Fin 3, coneMellinCoeff r j*coneMellinKernel b d q j) := by
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    have h := (coneMellinKernel_convex b d j).2 hp hq ha hc hac
    simp only [smul_eq_mul] at h
    linarith only [mul_le_mul_of_nonneg_left h (hC j)]
  linarith only [mul_le_mul_of_nonneg_left hSum (mul_nonneg (sq_nonneg U) hv.1)]

private theorem coneMellinRatio_convex {g t : ℝ} (hg : g ∈ Icc (0:ℝ) (1/6)) (ht : t ∈ Icc (0:ℝ) 1) :
    ConvexOn ℝ (Ici 1) (fun p => conePositiveRatio p g t / coneMellinScale p) := by
  let r := conePriceRadius g t
  let b := 2+g
  let U := 1+g
  have hr : 0 < r := (by norm_num : (0:ℝ) < 17/20).trans_le (conePriceRadius_bounds hg ht).1
  have hb : 0 < b := by unfold b; have := hg.1; positivity
  have hU : 0 < U := by unfold U; have := hg.1; positivity
  have h₁ := coneMellinDebit_convex hb hr (by norm_num : (0:ℝ) ≤ 0) (by norm_num : (0:ℝ) ≤ 1)
  have h₂ := coneMellinDebit_convex hb hr (by norm_num : (0:ℝ) ≤ 1) hU.le
  have h := ((h₁.smul (show (0:ℝ) ≤ 3553/200000 by norm_num)).add
    (h₂.smul (show 0 ≤ jointPureLambda by norm_num [jointPureLambda]))).smul (inv_nonneg.mpr hU.le)
  apply h.congr
  intro p hp
  have hp₀ := zero_lt_one.trans_le (show 1 ≤ p from hp)
  change U⁻¹*((3553/200000)*(b^(p+2)/(p*(p+1)*coneMellinScale p)*coneQDebit p r 0 1) +
    jointPureLambda*(b^(p+2)/(p*(p+1)*coneMellinScale p)*coneQDebit p r 1 U)) =
    b^(p+2)/U * conePositiveMoment p g t / (p*(p+1)) / coneMellinScale p
  have hEq : conePositiveMoment p g t = (3553/200000)*coneQDebit p r 0 1 +
      jointPureLambda*coneQDebit p r 1 U := conePositiveMoment_eq hp₀ hg ht
  rw [hEq]
  have hM : 0 < coneMellinScale p := by unfold coneMellinScale; positivity
  field_simp [hM.ne',hU.ne',hp₀.ne',show p+1 ≠ 0 by positivity]

private theorem coneMellinIntegral_convex {g : ℝ} (hg : g ∈ Icc (0:ℝ) (1/6)) :
    ConvexOn ℝ (Ici 1) (fun p => conePositiveIntegral p g / coneMellinScale p) := by
  refine ⟨convex_Ici _,?_⟩
  intro p hp q hq a c ha hc hac
  let f (p t : ℝ) := (9/10)*t*(conePositiveRatio p g t / coneMellinScale p)
  have hI {p : ℝ} (hp : 1 ≤ p) : IntervalIntegrable (f p) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (μ := volume) zero_le_one
    unfold f conePositiveRatio coneNormalizedPositive
    exact (continuousOn_const.mul continuousOn_id).mul
      ((((conePositiveMoment_continuousOn (zero_lt_one.trans_le hp) hg).const_mul _).div_const _).div_const _)
  have hE (p : ℝ) : conePositiveIntegral p g / coneMellinScale p = ∫ t in (0 : ℝ)..1, f p t := by
    unfold conePositiveIntegral
    rw [← intervalIntegral.integral_const_mul,div_eq_mul_inv,← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr
    intro t _
    unfold f
    ring
  have hpq : 1 ≤ a*p+c*q := (convex_Ici (1:ℝ)) hp hq ha hc hac
  simp only [smul_eq_mul]
  rw [hE,hE,hE,← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add ((hI hp).const_mul a) ((hI hq).const_mul c)]
  apply intervalIntegral.integral_mono_on zero_le_one (hI hpq) (((hI hp).const_mul a).add ((hI hq).const_mul c))
  intro t ht
  have h := (coneMellinRatio_convex hg ht).2 hp hq ha hc hac
  simp only [smul_eq_mul] at h
  have h' := mul_le_mul_of_nonneg_left h (show 0 ≤ (9/10:ℝ)*t by have := ht.1; positivity)
  unfold f
  linarith only [h']

private theorem cone_log_two_terms {x : ℝ} (hx : 0 ≤ x) (hx₁ : x < 1) :
    2*(x+x^3/3) ≤ Real.log ((1+x)/(1-x)) ∧
    Real.log ((1+x)/(1-x)) ≤ 2*(x+x^3/3)+2*x^5/(1-x^2) := by
  have h₁ := Real.sum_range_le_log_div hx hx₁ 2
  have h₂ := (abs_le.mp (Real.sum_range_sub_log_div_le
    (show |x| < 1 by rwa [abs_of_nonneg hx]) 2)).2
  norm_num [Finset.sum_range_succ,abs_of_nonneg hx] at h₁ h₂
  rw [mul_div_assoc]
  constructor <;> linarith only [h₁,h₂]

set_option maxHeartbeats 1400000 in
private theorem conePositiveIntegral_one_exact :
    conePositiveIntegral 1 (1/6) = jointPureLambda *
      (135149360157682577720381251/18418881944938832443965000 +
        (41743/225)*Real.log (190/181) - (1337737921/8010000)*Real.log (40/37) -
        (148312879/8010000)*Real.log (20/17)) := by
  have h := conePositiveIntegral_int_endpoint_eq 1 (by decide)
  norm_num at h
  rw [h]
  rw [Real.log_div (by norm_num : (190:ℝ) ≠ 0) (by norm_num : (181:ℝ) ≠ 0),
    Real.log_div (by norm_num : (40:ℝ) ≠ 0) (by norm_num : (37:ℝ) ≠ 0),
    Real.log_div (by norm_num : (20:ℝ) ≠ 0) (by norm_num : (17:ℝ) ≠ 0)]
  have hLog (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : Real.log (a/b) = Real.log a-Real.log b := Real.log_div ha hb
  have h₁ : Real.log (17/20) = Real.log 17-Real.log 20 := hLog _ _ (by norm_num) (by norm_num)
  have h₂ : Real.log (37/20) = Real.log 37-Real.log 20 := hLog _ _ (by norm_num) (by norm_num)
  have h₃ : Real.log (19/6) = Real.log 190-Real.log 60 := by
    rw [show (19/6:ℝ)=190/60 by norm_num,Real.log_div (by norm_num) (by norm_num)]
  have h₄ : Real.log (181/60) = Real.log 181-Real.log 60 := hLog _ _ (by norm_num) (by norm_num)
  have h₅ : Real.log 2 = Real.log 40-Real.log 20 := by
    rw [← Real.log_div (by norm_num : (40:ℝ) ≠ 0) (by norm_num : (20:ℝ) ≠ 0)]
    norm_num
  norm_num [coneIntEndpointDebit,coneIntEndpointMoment,coneIntEndpointJ,coneIntEndpointPrimitive,
    coneIntPrimitive, jointPureLambda,Finset.sum_range_succ,Nat.choose,Real.Gamma_one,
    Real.Gamma_nat_eq_factorial,Nat.factorial,zpow_neg,h₁,h₂,h₃,h₄,h₅]
  ring

set_option maxHeartbeats 1400000 in
private theorem conePositiveIntegral_two_exact :
    conePositiveIntegral 2 (1/6) = jointPureLambda *
      (28154758322130217276902457123422743/35698839250311983480758423155840000) := by
  have h := conePositiveIntegral_int_endpoint_eq 2 (by decide)
  norm_num at h
  rw [h]
  norm_num [coneIntEndpointDebit,coneIntEndpointMoment,coneIntEndpointJ,coneIntEndpointPrimitive,
    coneIntPrimitive,jointPureLambda,Finset.sum_range_succ,Nat.choose,Real.Gamma_nat_eq_factorial,Nat.factorial,zpow_neg]

theorem conePositiveIntegral_one_lt : conePositiveIntegral 1 (1/6) < jointPureLambda*(5/16) := by
  have h₁ := (cone_log_two_terms (x := 9/371) (by norm_num) (by norm_num)).2
  have h₂ := (cone_log_two_terms (x := 3/77) (by norm_num) (by norm_num)).1
  have h₃ := (cone_log_two_terms (x := 3/37) (by norm_num) (by norm_num)).1
  norm_num at h₁ h₂ h₃
  rw [conePositiveIntegral_one_exact]
  exact mul_lt_mul_of_pos_left (by linarith only [h₁,h₂,h₃]) (by norm_num [jointPureLambda])

theorem conePositiveIntegral_two_lt : conePositiveIntegral 2 (1/6) < jointPureLambda*(79/100) := by
  rw [conePositiveIntegral_two_exact]
  norm_num [jointPureLambda]

private theorem conePositiveIntegral_gap_mono {p : ℝ} (hp : 1 ≤ p) :
    MonotoneOn (conePositiveIntegral p) (Icc 0 (1/6)) := by
  intro g hg G hG h
  have hI {z : ℝ} (hz : z ∈ Icc (0:ℝ) (1/6)) :
      IntervalIntegrable (fun t => t * conePositiveRatio p z t) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (μ := volume) zero_le_one
    unfold conePositiveRatio coneNormalizedPositive
    exact continuousOn_id.mul (((conePositiveMoment_continuousOn (zero_lt_one.trans_le hp) hz).const_mul _).div_const _)
  unfold conePositiveIntegral
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply intervalIntegral.integral_mono_on zero_le_one (hI hg) (hI hG)
  exact fun t ht => mul_le_mul_of_nonneg_left (conePositiveRatio_mono_gap hp ht hg hG h) ht.1

private noncomputable def coneMellinEnvelope (p : ℝ) : ℝ := (5/16)*p*(158/125 : ℝ)^(p-1)

private theorem conePositiveIntegral_mellin_le {p g : ℝ} (hp : 1 ≤ p) (hP : p ≤ 2)
    (hg : g ∈ Icc (0:ℝ) (1/6)) : conePositiveIntegral p g ≤ jointPureLambda*coneMellinEnvelope p := by
  have hP₀ : 0 < p := zero_lt_one.trans_le hp
  have hS : 0 < coneMellinScale p := by unfold coneMellinScale; positivity
  have hConv := (coneMellinIntegral_convex (by norm_num : (1/6:ℝ) ∈ Icc 0 (1/6))).2
    (mem_Ici.mpr (le_refl (1:ℝ))) (show (2:ℝ) ∈ Ici 1 by norm_num)
    (sub_nonneg.mpr hP) (sub_nonneg.mpr hp) (by ring : 2-p+(p-1)=1)
  simp only [smul_eq_mul, mul_one] at hConv
  rw [show 2-p+(p-1)*2=p by ring] at hConv
  have h₁ : conePositiveIntegral 1 (1/6)/coneMellinScale 1 ≤ jointPureLambda/192 := by
    unfold coneMellinScale
    norm_num
    linarith only [conePositiveIntegral_one_lt]
  have h₂ : conePositiveIntegral 2 (1/6)/coneMellinScale 2 ≤ jointPureLambda/192 := by
    unfold coneMellinScale
    norm_num [Real.rpow_one]
    linarith only [conePositiveIntegral_two_lt]
  have hRaw : conePositiveIntegral p (1/6)/coneMellinScale p ≤ jointPureLambda/192 := by
    have h₁' := mul_le_mul_of_nonneg_left h₁ (sub_nonneg.mpr hP)
    have h₂' := mul_le_mul_of_nonneg_left h₂ (sub_nonneg.mpr hp)
    linarith only [hConv,h₁',h₂']
  have hR := (div_le_iff₀ hS).mp hRaw
  have hSpan : (p+2)*(p+3)*(p+4) ≤ 60*p := by
    nlinarith only [mul_nonneg (mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hP))
      (show 0 ≤ p+12 by positivity)]
  have hLam : 0 < jointPureLambda := by norm_num [jointPureLambda]
  have hPay := mul_le_mul_of_nonneg_right hSpan
    (show 0 ≤ jointPureLambda/192 * (158/125:ℝ)^(p-1) by positivity)
  have hMon := conePositiveIntegral_gap_mono hp hg (show (1/6:ℝ) ∈ Icc 0 (1/6) by norm_num) hg.2
  unfold coneMellinScale at hR
  unfold coneMellinEnvelope
  linarith only [hMon,hR,hPay]

private theorem coneMellinEnvelope_convex : ConvexOn ℝ (Ici 1) coneMellinEnvelope := by
  let l := Real.log (158/125)
  let E (p : ℝ) := Real.exp ((p-1)*l)
  let F (p : ℝ) := (5/16)*p*E p
  let G (p : ℝ) := (5/16)*(1+p*l)*E p
  have hl : 0 ≤ l := Real.log_nonneg (by norm_num)
  have hE (p : ℝ) : HasDerivAt E (E p*l) p := by
    simpa [E] using ((((hasDerivAt_id p).sub_const 1).mul_const l).exp)
  have hF (p : ℝ) : HasDerivAt F (G p) p := by
    convert (((hasDerivAt_id p).const_mul (5/16 : ℝ)).mul (hE p)) using 1
    simp only [F,G,id_eq,mul_one,one_mul]
    ring
  have hG (p : ℝ) : HasDerivAt G ((5/16)*(2*l+p*l^2)*E p) p := by
    convert (((((hasDerivAt_id p).mul_const l).const_add 1).const_mul (5/16 : ℝ)).mul (hE p)) using 1
    simp only [G,id_eq,mul_one,one_mul]
    ring
  have h : ConvexOn ℝ (Ici 1) F := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici _)
      (fun p _ => (hF p).continuousAt.continuousWithinAt)
      (fun p _ => (hF p).hasDerivWithinAt) (fun p _ => (hG p).hasDerivWithinAt)
    intro p hp
    have hp' : 0 ≤ p := zero_le_one.trans (interior_subset hp)
    unfold E
    positivity
  apply h.congr
  intro p _
  unfold F E l coneMellinEnvelope
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<158/125),mul_comm (Real.log _)]

private theorem coneMellinReserve {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9/5) :
    coneMellinEnvelope p + (1/2)*(130/147 : ℝ)^(p+2) ≤ 199/200 := by
  let R := (130/147 : ℝ)
  let f (p : ℝ) := R^(p+2)
  let B := coneMellinEnvelope
  let K (p : ℝ) := B p+(1/2)*f p
  have hR : 0 < R := by norm_num [R]
  have hE : ConvexOn ℝ (Ici 1) f := by
    refine ⟨convex_Ici _,?_⟩
    intro p _ q _ a b ha hb hab
    unfold f
    simp_rw [Real.rpow_def_of_pos hR,smul_eq_mul]
    have h := convexOn_exp.2 (mem_univ (Real.log R*(p+2))) (mem_univ (Real.log R*(q+2))) ha hb hab
    have hEq : a * (Real.log R * (p+2)) + b * (Real.log R * (q+2)) = Real.log R*(a*p+b*q+2) := by
      linear_combination (2*Real.log R)*hab
    simpa only [smul_eq_mul,hEq] using h
  have hC : ConvexOn ℝ (Ici 1) K := coneMellinEnvelope_convex.add (hE.smul (by norm_num : (0:ℝ)≤1/2))
  have h₁ : K 1 ≤ 199/200 := by
    unfold K B f R coneMellinEnvelope
    rw [show (1:ℝ)+2 = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hB : B (9/5) < 17/25 := by
    unfold B coneMellinEnvelope
    norm_num
    have hPow : ((158/125:ℝ)^(4/5:ℝ))^5 = (158/125:ℝ)^4 := by
      rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ)≤158/125)]
      norm_num [show (4:ℝ)=(4:ℕ) by norm_num,Real.rpow_natCast]
    have h : (9/16:ℝ)*(158/125:ℝ)^(4/5:ℝ) < 17/25 := by
      apply lt_of_pow_lt_pow_left₀ 5 (by norm_num)
      rw [mul_pow,hPow]
      norm_num
    linarith only [h]
  have hF : f (9/5) < 63/100 := by
    unfold f R
    apply lt_of_pow_lt_pow_left₀ 5 (by norm_num)
    rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ)≤130/147)]
    norm_num [show (19:ℝ)=(19:ℕ) by norm_num,Real.rpow_natCast]
  have hP₁ : K (9/5) ≤ 199/200 := by unfold K; linarith only [hB,hF]
  let t := (5/4)*(p-1)
  have ht : 0 ≤ t := by unfold t; linarith only [hp]
  have ht₁ : t ≤ 1 := by unfold t; linarith only [hP]
  have h := hC.2 (show (1:ℝ) ∈ Ici 1 from mem_Ici.mpr le_rfl) (show (9/5:ℝ) ∈ Ici 1 by norm_num)
    (sub_nonneg.mpr ht₁) ht (sub_add_cancel 1 t)
  simp only [smul_eq_mul, show (1-t)*1+t*(9/5)=p by unfold t; ring] at h
  unfold K f B R at h
  have H₁ := mul_le_mul_of_nonneg_left h₁ (sub_nonneg.mpr ht₁)
  have H₂ := mul_le_mul_of_nonneg_left hP₁ ht
  unfold K f B R at H₁ H₂
  linarith only [h,H₁,H₂]


theorem conePositiveIntegral_price {p g : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hg : g ∈ Icc (0 : ℝ) (1 / 6)) :
    (9 / 10) * (∫ t in (0 : ℝ)..1, t * conePositiveMoment p g t) ≤
      jointPureLambda * (199/200-(1/2)*(130/147:ℝ)^(p+2)) * (1 + g) * (p * (p + 1) * (2 + g) ^ (-(p + 2 : ℝ))) := by
  have hPrice := conePositiveIntegral_mellin_le hp (hP.trans (by norm_num)) hg
  have hRoom : coneMellinEnvelope p ≤ 199/200-(1/2)*(130/147:ℝ)^(p+2) := by
    linarith only [coneMellinReserve hp hP]
  have h := hPrice.trans (mul_le_mul_of_nonneg_left hRoom (by norm_num [jointPureLambda]))
  unfold conePositiveIntegral conePositiveRatio coneNormalizedPositive at h
  have hE (t : ℝ) : t * ((2 + g) ^ (p + 2) / (1 + g) * conePositiveMoment p g t / (p * (p + 1))) =
      ((2 + g) ^ (p + 2) / (1 + g) / (p * (p + 1))) * (t * conePositiveMoment p g t) := by ring
  simp_rw [hE] at h
  rw [intervalIntegral.integral_const_mul] at h
  have hp₀ := zero_lt_one.trans_le hp
  have hB : 0 < 2 + g := by have := hg.1; positivity
  have hU : 0 < 1 + g := by have := hg.1; positivity
  have hK : 0 < (2 + g) ^ (p + 2) / (1 + g) / (p * (p + 1)) := by positivity
  have hN := mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hK.le)
  rw [Real.rpow_neg hB.le]
  have hEq : ((2 + g) ^ (p + 2) / (1 + g) / (p * (p + 1)))⁻¹ =
      (1 + g) * (p * (p + 1) * ((2 + g) ^ (p + 2))⁻¹) := by
    field_simp [hU.ne',(Real.rpow_pos_of_pos hB _).ne',hp₀.ne',(by positivity : 0 < p + 1).ne']
  have hLHS : (9 / 10) * (((2 + g) ^ (p + 2) / (1 + g) / (p * (p + 1))) *
      (∫ t in (0 : ℝ)..1, t * conePositiveMoment p g t)) *
      ((2 + g) ^ (p + 2) / (1 + g) / (p * (p + 1)))⁻¹ =
      (9 / 10) * ∫ t in (0 : ℝ)..1, t * conePositiveMoment p g t := by
    field_simp [hK.ne']
  rw [hLHS] at hN
  rw [hEq] at hN
  exact hN.trans_eq (by ring)

end ACS12.GammaMeasure

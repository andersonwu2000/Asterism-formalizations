import ACS12.GammaStrip
import ACS12.Anchored

/-! The positive image law and the actual finite circle kernel. -/

namespace ACS12.GammaMeasure

open MeasureTheory Set
open CenteredCircle.AllN (exponential_samples_hasSum periodic_angle_sin_pos)

noncomputable def imagePotential (p L t : ℝ) : ℝ :=
  ∫ s : ℝ in Ioi 0, imageDensity p L s * Real.exp (-s * t)

theorem imageDensity_eq_spectral (p : ℝ) {L : ℝ} (hL : 0 < L) (s : ℝ) :
    imageDensity p L s =
      (Real.pi / L) ^ (p - 1) * gammaDensity p (L * s / (2 * Real.pi)) *
        Real.sinh (L * s / 2) := by
  have hpi : Real.pi ^ (p - 2) * Real.pi = Real.pi ^ (p - 1) := by
    calc
      _ = Real.pi ^ (p - 2) * Real.pi ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add Real.pi_pos]; congr 1; ring
  rw [imageDensity, gammaDensity, Real.div_rpow Real.pi_pos.le hL.le, ← hpi,
    div_eq_mul_inv (Real.pi ^ (p - 2) * Real.pi),
    ← Real.rpow_neg hL.le, show -(p - 1) = 1 - p by ring]
  field_simp [Real.pi_ne_zero]

theorem continuous_imageDensity {p L : ℝ} (hp : 0 < p) (hL : 0 < L) :
    Continuous (imageDensity p L) := by
  rw [show imageDensity p L = fun s =>
      (Real.pi / L) ^ (p - 1) * gammaDensity p (L * s / (2 * Real.pi)) *
        Real.sinh (L * s / 2) from funext (imageDensity_eq_spectral p hL)]
  exact ((continuous_const.mul ((continuous_gammaDensity hp).comp (by fun_prop))).mul
    (by fun_prop))

private theorem sinh_mul_image_ratio {L s : ℝ} (hL : 0 < L) (hs : 0 < s) (t : ℝ) :
    Real.sinh (L * s / 2) *
        ((Real.exp (-s * t) + Real.exp (-s * (L - t))) / (1 - Real.exp (-s * L))) =
      Real.cosh (s * (L / 2 - t)) := by
  let a := L * s / 2
  let b := s * (L / 2 - t)
  have ha : 0 < a := by dsimp [a]; positivity
  have h₁ : Real.exp (-s * t) = Real.exp (-a) * Real.exp b := by
    rw [← Real.exp_add]
    congr 1
    dsimp [a, b]
    ring
  have h₂ : Real.exp (-s * (L - t)) = Real.exp (-a) * Real.exp (-b) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [a, b]
    ring
  have h₃ : 1 - Real.exp (-s * L) = 2 * Real.exp (-a) * Real.sinh a := by
    rw [Real.sinh_eq]
    have h : Real.exp (-a) * Real.exp a = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc
      _ = Real.exp (-a) * Real.exp a - Real.exp (-a) * Real.exp (-a) := by
        rw [h, ← Real.exp_add]
        congr 2
        dsimp [a]
        ring
      _ = _ := by ring
  change Real.sinh a * _ = Real.cosh b
  rw [h₁, h₂, ← mul_add, h₃, Real.cosh_eq]
  field_simp [(Real.sinh_pos_iff.mpr ha).ne', (Real.exp_pos (-a)).ne']

noncomputable def imageRowIntegrand (p L t s : ℝ) : ℝ :=
  imageDensity p L s *
    ((Real.exp (-s * t) + Real.exp (-s * (L - t))) / (1 - Real.exp (-s * L)))

private theorem imageRowIntegrand_eq (p : ℝ) {L s : ℝ} (hL : 0 < L) (hs : 0 < s) (t : ℝ) :
    imageRowIntegrand p L t s =
      (Real.pi / L) ^ (p - 1) * gammaDensity p (L * s / (2 * Real.pi)) *
        Real.cosh (s * (L / 2 - t)) := by
  rw [imageRowIntegrand, imageDensity_eq_spectral p hL, mul_assoc,
    sinh_mul_image_ratio hL hs]

theorem imageRowIntegral {p L t : ℝ} (hp : 0 < p) (hL : 0 < L)
    (ht : 0 < t) (htL : t < L) :
    (∫ s : ℝ in Ioi 0, imageRowIntegrand p L t s) = circlePower p L t := by
  let a := L / (2 * Real.pi)
  let y := Real.pi - 2 * Real.pi * t / L
  let B := (Real.pi / L) ^ (p - 1) / 2
  let f (u : ℝ) := 2 * gammaDensity p u * Real.cosh (u * y)
  have ha : 0 < a := by dsimp [a]; positivity
  have hy : |y| < Real.pi := by
    apply abs_lt.mpr
    have h : 0 < 2 * Real.pi * t / L := by positivity
    have h' : 2 * Real.pi * t / L < 2 * Real.pi := by
      apply (div_lt_iff₀ hL).mpr
      gcongr
    constructor <;> dsimp [y] <;> linarith
  have hc : Real.cos (y / 2) = Real.sin (Real.pi * t / L) := by
    rw [show y / 2 = Real.pi / 2 - Real.pi * t / L by dsimp [y]; ring,
      Real.cos_pi_div_two_sub]
  have hB : B * a⁻¹ = (Real.pi / L) ^ p := by
    dsimp [B, a]
    rw [show (L / (2 * Real.pi))⁻¹ = 2 * (Real.pi / L) by
      field_simp [hL.ne', Real.pi_ne_zero]]
    rw [show (Real.pi / L) ^ (p - 1) / 2 * (2 * (Real.pi / L)) =
      (Real.pi / L) ^ (p - 1) * (Real.pi / L) by ring]
    calc
      _ = (Real.pi / L) ^ (p - 1) * (Real.pi / L) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add (by positivity), sub_add_cancel]
  calc
    _ = ∫ s : ℝ in Ioi 0, B * f (a * s) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      rw [imageRowIntegrand_eq p hL hs]
      dsimp [B, f]
      rw [show a * s = L * s / (2 * Real.pi) by dsimp [a]; ring,
        show L * s / (2 * Real.pi) * y = s * (L / 2 - t) by
          dsimp [y]; field_simp [hL.ne', Real.pi_ne_zero]]
      ring
    _ = B * (∫ s : ℝ in Ioi 0, f (a * s)) :=
      integral_const_mul B _
    _ = _ := by
      rw [integral_comp_mul_left_Ioi f 0 ha, mul_zero, smul_eq_mul, ← mul_assoc, hB]
      change (Real.pi / L) ^ p * (∫ u : ℝ in Ioi 0,
        2 * gammaDensity p u * Real.cosh (u * y)) = _
      rw [gammaDensity_cosh_moment hp hy, hc, Real.rpow_neg
        (periodic_angle_sin_pos hL ht htL).le, ← div_eq_mul_inv, circlePower]

theorem imageRowIntegrable {p L t : ℝ} (hp : 0 < p) (hL : 0 < L)
    (ht : 0 < t) (htL : t < L) :
    IntegrableOn (imageRowIntegrand p L t) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [imageRowIntegral hp hL ht htL, circlePower]
  exact (div_pos (Real.rpow_pos_of_pos (div_pos Real.pi_pos hL) _)
    (Real.rpow_pos_of_pos (periodic_angle_sin_pos hL ht htL) _)).ne'

private theorem abs_image_nonneg {L t : ℝ} (hL : 0 < L) (ht : 0 < t) (j : ℕ) :
    |t + ((j : ℤ) : ℝ) * L| = t + (j : ℝ) * L := by
  rw [Int.cast_natCast, abs_of_pos (by positivity)]

private theorem abs_image_neg {L t : ℝ} (hL : 0 < L) (htL : t < L) (j : ℕ) :
    |t + ((-(j + 1) : ℤ) : ℝ) * L| = L - t + (j : ℝ) * L := by
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  push_cast
  rw [abs_of_neg (by nlinarith)]
  ring

private theorem imageDensity_samples_hasSum {p L t s : ℝ} (hL : 0 < L) (hs : 0 < s)
    (ht : 0 < t) (htL : t < L) :
    HasSum (fun j : ℤ => imageDensity p L s * Real.exp (-s * |t + (j : ℝ) * L|))
      (imageRowIntegrand p L t s) := by
  let f (j : ℤ) := imageDensity p L s * Real.exp (-s * |t + (j : ℝ) * L|)
  let q := (1 - Real.exp (-s * L))⁻¹
  have hpos : HasSum (fun j : ℕ => f (j : ℤ))
      (imageDensity p L s * (Real.exp (-s * t) * q)) := by
    simpa only [f, abs_image_nonneg hL ht, q] using (exponential_samples_hasSum s t L hs hL).mul_left
      (imageDensity p L s)
  have hneg : HasSum (fun j : ℕ => f (-(j + 1) : ℤ))
      (imageDensity p L s * (Real.exp (-s * (L - t)) * q)) := by
    simpa only [f, abs_image_neg hL htL, q] using (exponential_samples_hasSum s (L - t) L hs hL).mul_left
      (imageDensity p L s)
  change HasSum f (imageRowIntegrand p L t s)
  rw [show imageRowIntegrand p L t s =
      imageDensity p L s * (Real.exp (-s * t) * q) +
        imageDensity p L s * (Real.exp (-s * (L - t)) * q) by
    unfold imageRowIntegrand
    dsimp [q]
    rw [div_eq_mul_inv]
    ring]
  exact hpos.of_nat_of_neg_add_one hneg

/-- Periodizing the actual Gamma Laplace kernel gives the physical radial
power on the interior of a period. -/
theorem imagePotential_periodization {p L t : ℝ} (hp : 0 < p) (hL : 0 < L)
    (ht : 0 < t) (htL : t < L) :
    HasSum (fun j : ℤ => imagePotential p L |t + (j : ℝ) * L|) (circlePower p L t) := by
  let f (j : ℤ) (s : ℝ) := imageDensity p L s * Real.exp (-s * |t + (j : ℝ) * L|)
  have hpoint : ∀ᵐ s : ℝ ∂volume.restrict (Ioi 0),
      HasSum (fun j : ℤ => f j s) (imageRowIntegrand p L t s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact imageDensity_samples_hasSum hL hs ht htL
  rw [← imageRowIntegral hp hL ht htL]
  change HasSum (fun j : ℤ => ∫ s : ℝ in Ioi 0, f j s)
    (∫ s : ℝ in Ioi 0, imageRowIntegrand p L t s)
  refine hasSum_integral_of_dominated_convergence f (fun j => ?_) (fun j => ?_)
    (hpoint.mono fun _ hs => hs.summable) ?_ hpoint
  · have hc : Continuous (f j) := (continuous_imageDensity hp hL).mul (by fun_prop)
    exact hc.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact le_of_eq (Real.norm_of_nonneg (mul_nonneg (imageDensity_pos hp hL hs).le
      (Real.exp_pos _).le))
  · refine (imageRowIntegrable hp hL ht htL).congr ?_
    exact hpoint.mono fun _ hs => hs.tsum_eq.symm

theorem imagePotential_integrable {p L t : ℝ} (hp : 0 < p) (hL : 0 < L) (ht : 0 < t) :
    IntegrableOn (fun s : ℝ => imageDensity p L s * Real.exp (-s * t)) (Ioi 0) := by
  let d := min t (L / 2)
  have hd : 0 < d := lt_min ht (by positivity)
  have hdL : d < L := (min_le_right _ _).trans_lt (by linarith)
  refine (imageRowIntegrable hp hL hd hdL).mono'
    (((continuous_imageDensity hp hL).mul (by fun_prop)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  change 0 < s at hs
  have hw := (imageDensity_pos hp hL hs).le
  have hden : 0 < 1 - Real.exp (-s * L) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))
  have hdt : d ≤ t := min_le_left _ _
  rw [Real.norm_of_nonneg (mul_nonneg hw (Real.exp_pos _).le), imageRowIntegrand]
  apply mul_le_mul_of_nonneg_left _ hw
  calc
    _ ≤ Real.exp (-s * d) := Real.exp_le_exp.mpr (by nlinarith)
    _ ≤ _ := by
      apply (le_div_iff₀ hden).mpr
      calc
        _ ≤ Real.exp (-s * d) * 1 :=
          mul_le_mul_of_nonneg_left (sub_le_self _ (Real.exp_pos _).le) (Real.exp_pos _).le
        _ ≤ _ := by rw [mul_one]; exact le_add_of_nonneg_right (Real.exp_pos _).le

theorem imagePotential_pos {p L t : ℝ} (hp : 0 < p) (hL : 0 < L) (ht : 0 < t) :
    0 < imagePotential p L t := by
  letI : NeZero (volume.restrict (Ioi (0 : ℝ))) :=
    ⟨CenteredCircle.AllN.positiveHalfLine_ne_zero⟩
  have h := CenteredCircle.AllN.integral_strict_of_ae_lt (volume.restrict (Ioi (0 : ℝ)))
    (integrable_zero ℝ ℝ _) (imagePotential_integrable hp hL ht) ?_
  · simpa only [imagePotential, integral_zero] using h
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_pos (imageDensity_pos hp hL hs) (Real.exp_pos _)

theorem imagePotential_antitoneOn {p L : ℝ} (hp : 0 < p) (hL : 0 < L) :
    AntitoneOn (imagePotential p L) (Ioi 0) := by
  intro x hx y hy hxy
  apply integral_mono_ae (imagePotential_integrable hp hL hy)
    (imagePotential_integrable hp hL hx)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
    change 0 < s at hs
    nlinarith)) (imageDensity_pos hp hL hs).le

theorem imagePotential_self_summable {p L : ℝ} (hp : 0 < p) (hL : 0 < L) :
    Summable (fun j : ℕ => imagePotential p L ((j + 1) * L)) := by
  have hd : 0 < L / 2 := by positivity
  have hdL : L / 2 < L := by linarith
  have h := (imagePotential_periodization hp hL hd hdL).summable
  have h' := (summable_int_iff_summable_nat_and_neg.mp h).1
  have hmid (j : ℕ) : 0 < L / 2 + (j : ℝ) * L := by positivity
  have hsum : Summable (fun j : ℕ => imagePotential p L (L / 2 + (j : ℝ) * L)) := by
    simpa only [Int.cast_natCast, abs_of_pos (hmid _)] using h'
  have ht (j : ℕ) : 0 < ((j : ℝ) + 1) * L := by positivity
  refine Summable.of_nonneg_of_le (fun j => (imagePotential_pos hp hL (ht j)).le) ?_ hsum
  intro j
  exact imagePotential_antitoneOn hp hL (hmid j) (ht j) (by nlinarith)

noncomputable def imageSelf (p L : ℝ) : ℝ :=
  2 * ∑' j : ℕ, imagePotential p L ((j + 1) * L)

theorem imageSelf_pos {p L : ℝ} (hp : 0 < p) (hL : 0 < L) : 0 < imageSelf p L := by
  have hn (j : ℕ) : 0 ≤ imagePotential p L ((j + 1) * L) :=
    (imagePotential_pos hp hL (by positivity)).le
  have h := (imagePotential_self_summable hp hL).le_tsum 0 (fun j _ => hn j)
  simp only [Nat.cast_zero, zero_add, one_mul] at h
  exact mul_pos (by norm_num) ((imagePotential_pos hp hL hL).trans_le h)

theorem imagePotential_pair {p L t : ℝ} (hp : 0 < p) (hL : 0 < L)
    (ht : 0 < t) (htL : t < L) :
    CenteredCircle.AllN.imageTail (imagePotential p L) L t +
      CenteredCircle.AllN.imageTail (imagePotential p L) L (L - t) = circlePower p L t := by
  let f (j : ℤ) := imagePotential p L |t + (j : ℝ) * L|
  have h : HasSum f (circlePower p L t) := imagePotential_periodization hp hL ht htL
  have hi : Function.Injective (fun j : ℕ => (-(j + 1) : ℤ)) := by
    intro i j hij
    dsimp at hij
    omega
  have h₁ : Summable (fun j : ℕ => f (j : ℤ)) := h.summable.comp_injective Nat.cast_injective
  have h₂ : Summable (fun j : ℕ => f (-(j + 1) : ℤ)) := h.summable.comp_injective hi
  calc
    _ = (∑' j : ℕ, f (j : ℤ)) + ∑' j : ℕ, f (-(j + 1) : ℤ) := by
      simp only [CenteredCircle.AllN.imageTail, f, abs_image_nonneg hL ht, abs_image_neg hL htL]
    _ = ∑' j : ℤ, f j := (tsum_of_nat_of_neg_add_one h₁ h₂).symm
    _ = _ := h.tsum_eq

theorem imagePotential_samples_summable {p L t : ℝ} (hp : 0 < p) (hL : 0 < L) (ht : 0 < t) :
    Summable (fun j : ℕ => imagePotential p L (t + (j : ℝ) * L)) := by
  let d := min t (L / 2)
  have hd : 0 < d := lt_min ht (by positivity)
  have hdL : d < L := (min_le_right _ _).trans_lt (by linarith)
  have h := (imagePotential_periodization hp hL hd hdL).summable
  have hs : Summable (fun j : ℕ => imagePotential p L (d + (j : ℝ) * L)) := by
    have hn := (summable_int_iff_summable_nat_and_neg.mp h).1
    simpa only [abs_image_nonneg hL hd] using hn
  have hdt : d ≤ t := min_le_left _ _
  have ht' (j : ℕ) : 0 < t + (j : ℝ) * L := by positivity
  have hd' (j : ℕ) : 0 < d + (j : ℝ) * L := by positivity
  exact Summable.of_nonneg_of_le (fun j => (imagePotential_pos hp hL (ht' j)).le)
    (fun j => imagePotential_antitoneOn hp hL (hd' j) (ht' j)
      (by linarith)) hs

/-- A nonnegative Laplace density can be summed over a positive image
spacing once its geometric majorant is integrable. -/
theorem hasSum_laplace_samples (g : ℝ → ℝ) (hg : Measurable g)
    (hg₀ : ∀ s > 0, 0 ≤ g s) {t L : ℝ} (hL : 0 < L)
    (hi : IntegrableOn (fun s : ℝ => g s *
      (Real.exp (-s * t) / (1 - Real.exp (-s * L)))) (Ioi 0)) :
    HasSum (fun j : ℕ => ∫ s : ℝ in Ioi 0, g s * Real.exp (-s * (t + (j : ℝ) * L)))
      (∫ s : ℝ in Ioi 0, g s * (Real.exp (-s * t) / (1 - Real.exp (-s * L)))) := by
  let f (j : ℕ) (s : ℝ) := g s * Real.exp (-s * (t + (j : ℝ) * L))
  let G (s : ℝ) := g s * (Real.exp (-s * t) / (1 - Real.exp (-s * L)))
  have hpoint : ∀ᵐ s : ℝ ∂volume.restrict (Ioi 0), HasSum (fun j => f j s) (G s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    simpa only [f, G, div_eq_mul_inv] using (exponential_samples_hasSum s t L hs hL).mul_left (g s)
  change HasSum (fun j => ∫ s : ℝ in Ioi 0, f j s) (∫ s : ℝ in Ioi 0, G s)
  refine hasSum_integral_of_dominated_convergence f (fun j => ?_) (fun j => ?_)
    (hpoint.mono fun _ hs => hs.summable) ?_ hpoint
  · exact (hg.mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact le_of_eq (Real.norm_of_nonneg (mul_nonneg (hg₀ s hs) (Real.exp_pos _).le))
  · exact hi.congr (hpoint.mono fun _ hs => hs.tsum_eq.symm)

end ACS12.GammaMeasure

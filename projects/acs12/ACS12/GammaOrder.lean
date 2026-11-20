import ACS12.GammaPeriodization
import ACS12.GammaUnitReflection

/-! The Gamma image law divided by its spectral variable is decreasing
through exponent two. The literal endpoint has a linear image density. -/

namespace ACS12.GammaMeasure

open Set Filter
open scoped Topology BigOperators

theorem norm_gammaArgument_add (q t : ℝ) (j : ℕ) :
    ‖gammaArgument q t + (j : ℂ)‖ ^ 2 = (q + (j : ℝ)) ^ 2 + t ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [gammaArgument, Complex.mul_re, Complex.mul_im]
  ring

/-- At the literal pressure endpoint the exact image law is linear. -/
theorem imageDensity_two {L s : ℝ} (hL : 0 < L) (hs : 0 < s) :
    imageDensity 2 L s = s := by
  have hΓ : Real.Gamma 2 = 1 := by norm_num
  have ht : 0 < L * s / (2 * Real.pi) := by positivity
  rw [imageDensity_eq_spectral 2 hL, gammaDensity]
  simp only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, hΓ, mul_one]
  rw [show ((2 / 2 : ℝ) : ℂ) + ((L * s / (2 * Real.pi) : ℝ) : ℂ) * Complex.I =
    gammaArgument 1 (L * s / (2 * Real.pi)) by norm_num [gammaArgument],
    gammaUnit_norm_sq ht,
    show Real.pi * (L * s / (2 * Real.pi)) = L * s / 2 by field_simp [Real.pi_ne_zero]]
  field_simp [hL.ne', Real.pi_ne_zero, (Real.sinh_pos_iff.mpr (by positivity : 0 < L * s / 2)).ne']

theorem norm_GammaSeq {q : ℝ} (hq : 0 < q) (t : ℝ) (n : ℕ) :
    ‖Complex.GammaSeq (gammaArgument q t) n‖ =
      ((n : ℝ) ^ q * (n.factorial : ℝ)) /
        ∏ j ∈ Finset.range (n + 1), ‖gammaArgument q t + (j : ℂ)‖ := by
  rw [Complex.GammaSeq, norm_div, norm_mul, norm_prod, ← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg n) (by simpa using hq.ne'),
    gammaArgument_re, Complex.norm_natCast]

private theorem gammaSeq_norm_ratio {q : ℝ} (hq : 0 < q) (t : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖Complex.GammaSeq (gammaArgument q t) n‖ / ‖Complex.GammaSeq (gammaArgument 1 t) n‖ =
      ((n : ℝ) ^ q / (n : ℝ)) *
        ∏ j ∈ Finset.range (n + 1), ‖gammaArgument 1 t + (j : ℂ)‖ /
          ‖gammaArgument q t + (j : ℂ)‖ := by
  have hpos (q : ℝ) (hq : 0 < q) (j : ℕ) : 0 < ‖gammaArgument q t + (j : ℂ)‖ := by
    apply norm_pos_iff.mpr
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have hp (q : ℝ) (hq : 0 < q) :
      0 < ∏ j ∈ Finset.range (n + 1), ‖gammaArgument q t + (j : ℂ)‖ :=
    Finset.prod_pos fun j _ => hpos q hq j
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [norm_GammaSeq hq, norm_GammaSeq zero_lt_one, Real.rpow_one, Finset.prod_div_distrib]
  field_simp [hf, hn', (hp q hq).ne', (hp 1 zero_lt_one).ne']

private theorem norm_gamma_factor_decreases {q x y : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hx : 0 ≤ x) (hxy : x ≤ y) (j : ℕ) :
    ‖gammaArgument 1 y + (j : ℂ)‖ / ‖gammaArgument q y + (j : ℂ)‖ ≤
      ‖gammaArgument 1 x + (j : ℂ)‖ / ‖gammaArgument q x + (j : ℂ)‖ := by
  have hqj : 0 < q + (j : ℝ) := by positivity
  have h1j : 0 < 1 + (j : ℝ) := by positivity
  have hyy : x ^ 2 ≤ y ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (by linarith : 0 ≤ y + x)]
  have hqq : (q + (j : ℝ)) ^ 2 ≤ (1 + (j : ℝ)) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq1) (by linarith : 0 ≤ 1 + (j : ℝ) + (q + (j : ℝ)))]
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  simp only [div_pow, norm_gammaArgument_add]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hqq) (sub_nonneg.mpr hyy)]

private theorem gamma_ratio_antitone {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    AntitoneOn (fun t : ℝ => ‖Complex.Gamma (gammaArgument q t)‖ /
      ‖Complex.Gamma (gammaArgument 1 t)‖) (Ici 0) := by
  have hlim (t : ℝ) :
      Tendsto (fun n => ‖Complex.GammaSeq (gammaArgument q t) n‖ /
        ‖Complex.GammaSeq (gammaArgument 1 t) n‖) atTop
          (𝓝 (‖Complex.Gamma (gammaArgument q t)‖ / ‖Complex.Gamma (gammaArgument 1 t)‖)) :=
    (Complex.GammaSeq_tendsto_Gamma _).norm.div (Complex.GammaSeq_tendsto_Gamma _).norm
      (norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by simp)))
  intro x hx y _ hxy
  apply le_of_tendsto_of_tendsto (hlim y) (hlim x)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  rw [gammaSeq_norm_ratio hq y (by omega), gammaSeq_norm_ratio hq x (by omega)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.prod_le_prod (fun j _ => by positivity)
    (fun j _ => norm_gamma_factor_decreases hq hq1 hx hxy j)

theorem imageDensity_div_eq_ratio {p L s : ℝ} (hp : 0 < p) (hL : 0 < L) (hs : 0 < s) :
    imageDensity p L s / s =
      ((Real.pi / L) ^ (p - 1) * (2 : ℝ) ^ (p - 1) /
        (Real.Gamma p * (Real.pi / L) * 2)) *
      (‖Complex.Gamma (gammaArgument (p / 2) (L * s / (2 * Real.pi)))‖ /
        ‖Complex.Gamma (gammaArgument 1 (L * s / (2 * Real.pi)))‖) ^ 2 := by
  let t := L * s / (2 * Real.pi)
  have hΓ : Real.Gamma 2 = 1 := by norm_num
  have hg : ‖Complex.Gamma (gammaArgument 1 t)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by simp))
  calc
    _ = imageDensity p L s / imageDensity 2 L s := by rw [imageDensity_two hL hs]
    _ = _ := by
      rw [imageDensity_eq_spectral p hL, imageDensity_eq_spectral 2 hL]
      simp only [gammaDensity, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
        hΓ, mul_one, show (2 : ℝ) / 2 = 1 by norm_num]
      change ((Real.pi / L) ^ (p - 1) *
          ((2 : ℝ) ^ (p - 1) * ‖Complex.Gamma (gammaArgument (p / 2) t)‖ ^ 2 /
            (Real.pi * Real.Gamma p)) * Real.sinh (L * s / 2)) /
          ((Real.pi / L) * (2 * ‖Complex.Gamma (gammaArgument 1 t)‖ ^ 2 / Real.pi) *
            Real.sinh (L * s / 2)) =
        ((Real.pi / L) ^ (p - 1) * (2 : ℝ) ^ (p - 1) /
          (Real.Gamma p * (Real.pi / L) * 2)) *
          (‖Complex.Gamma (gammaArgument (p / 2) t)‖ /
            ‖Complex.Gamma (gammaArgument 1 t)‖) ^ 2
      rw [div_pow]
      field_simp [Real.pi_ne_zero, hL.ne', (Real.Gamma_pos_of_pos hp).ne', hg,
        (Real.sinh_pos_iff.mpr (by positivity : 0 < L * s / 2)).ne'] <;> ring

/-- The exact density divided by the Laplace variable is antitone up to and
including the literal pressure endpoint. -/
theorem imageDensity_div_antitone {p L : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2) (hL : 0 < L) :
    AntitoneOn (fun s => imageDensity p L s / s) (Ioi 0) := by
  intro x hx y hy hxy
  change imageDensity p L y / y ≤ imageDensity p L x / x
  rw [imageDensity_div_eq_ratio hp hL hy, imageDensity_div_eq_ratio hp hL hx]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply pow_le_pow_left₀ (by positivity) _ 2
  exact gamma_ratio_antitone (by positivity : 0 < p / 2) (by linarith)
    (by change 0 ≤ L * x / (2 * Real.pi); exact div_nonneg (mul_nonneg hL.le hx.le) (by positivity))
    (by change 0 ≤ L * y / (2 * Real.pi); exact div_nonneg (mul_nonneg hL.le hy.le) (by positivity))
    (by gcongr)

theorem imageDensity_linear_bound {p L : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2) (hL : 0 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s > 0, imageDensity p L s ≤ C * s := by
  let A := (Real.pi / L) ^ (p - 1) * (2 : ℝ) ^ (p - 1) /
    (Real.Gamma p * (Real.pi / L) * 2)
  let C := A * (‖Complex.Gamma (gammaArgument (p / 2) 0)‖ /
    ‖Complex.Gamma (gammaArgument 1 0)‖) ^ 2
  refine ⟨C, by dsimp [C, A]; positivity, fun s hs => (div_le_iff₀ hs).mp ?_⟩
  rw [imageDensity_div_eq_ratio hp hL hs]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply pow_le_pow_left₀ (by positivity) _ 2
  have ht : 0 ≤ L * s / (2 * Real.pi) := by positivity
  exact gamma_ratio_antitone (by positivity : 0 < p / 2) (by linarith) (by simp) ht ht

end ACS12.GammaMeasure

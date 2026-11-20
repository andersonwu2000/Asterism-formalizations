import ACS12.PowerSine
import ACS12.DeficitProfile

/-! The complete positive binomial Gamma sum, derived before any spectral interchange. -/
namespace ACS12.GammaMeasure

open MeasureTheory Set Filter
open GammaDeficit (gamma_exp_integral integrable_gamma_exp sinhProfile)

theorem gammaBinomial_hasSum {p x : ℝ} (hp : 0 < p) (hx : 0 ≤ x) (hx₁ : x < 1) :
    HasSum (fun j : ℕ => Real.Gamma (p + j) * x ^ j / (j.factorial : ℝ))
      (Real.Gamma p * (1 - x) ^ (-p)) := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  let F (j : ℕ) (s : ℝ) := (s ^ (p - 1) * Real.exp (-s)) * ((x * s) ^ j / (j.factorial : ℝ))
  let G (s : ℝ) := s ^ (p - 1) * Real.exp (-(1 - x) * s)
  have hG : Integrable G μ := integrable_gamma_exp hp (sub_pos.mpr hx₁)
  have hSeries (s : ℝ) (hs : 0 < s) : HasSum (fun j => F j s) (G s) := by
    have h := (NormedSpace.expSeries_div_hasSum_exp (x * s)).mul_left (s ^ (p - 1) * Real.exp (-s))
    rw [← Real.exp_eq_exp_ℝ] at h
    dsimp only [F,G]
    rw [mul_assoc,← Real.exp_add] at h
    convert h using 2 <;> ring
  have hAE : ∀ᵐ s ∂μ, HasSum (fun j => F j s) (G s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact hSeries s hs
  have h := hasSum_integral_of_dominated_convergence F
    (fun j => (by unfold F; fun_prop : Measurable (F j)).aestronglyMeasurable)
    (fun j => by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs₀ : 0 < s := hs
      exact le_of_eq (Real.norm_of_nonneg (by dsimp only [F]; positivity)))
    (hAE.mono fun _ h => h.summable)
    (hG.congr (hAE.mono fun _ h => h.tsum_eq.symm)) hAE
  have hTerm (j : ℕ) : (∫ s : ℝ, F j s ∂μ) = Real.Gamma (p + j) * x ^ j / (j.factorial : ℝ) := by
    have hE (s : ℝ) (hs : 0 < s) : F j s = (x ^ j / (j.factorial : ℝ)) *
        (s ^ (p + (j : ℝ) - 1) * Real.exp (-s * 1)) := by
      dsimp only [F]
      rw [mul_pow,mul_one,show p + (j : ℝ) - 1 = (p - 1) + j by ring,Real.rpow_add hs,Real.rpow_natCast]
      ring
    change (∫ s : ℝ in Ioi 0, F j s) = _
    rw [setIntegral_congr_fun measurableSet_Ioi (fun s hs => hE s hs),integral_const_mul,
      show (fun s : ℝ => s ^ (p + (j : ℝ) - 1) * Real.exp (-s * 1)) =
        (fun s : ℝ => s ^ (p + (j : ℝ) - 1) * Real.exp (-1 * s)) by funext s; congr 2; ring,
      gamma_exp_integral (by positivity : 0 < p + (j : ℝ)) zero_lt_one,Real.one_rpow,mul_one]
    ring
  have hGE : (∫ s : ℝ, G s ∂μ) = Real.Gamma p * (1 - x) ^ (-p) :=
    gamma_exp_integral hp (sub_pos.mpr hx₁)
  simp_rw [hTerm,hGE] at h
  exact h

theorem gammaHyperbolic_hasSum {p v : ℝ} (hp : 0 < p) (hv : 0 < v) :
    HasSum (fun j : ℕ => Real.Gamma (p + j) * Real.exp (-v * (p / 2 + j)) / (j.factorial : ℝ))
      (Real.Gamma p * sinhProfile p v) := by
  have h := (gammaBinomial_hasSum hp (Real.exp_pos (-v)).le
    (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hv))).mul_left (Real.exp (-v * (p / 2)))
  have hE (j : ℕ) : Real.exp (-v * (p / 2)) * (Real.Gamma (p + j) * Real.exp (-v) ^ j / (j.factorial : ℝ)) =
      Real.Gamma (p + j) * Real.exp (-v * (p / 2 + j)) / (j.factorial : ℝ) := by
    rw [← Real.exp_nat_mul]
    calc
      _ = Real.Gamma (p + j) * (Real.exp (-v * (p / 2)) * Real.exp ((j : ℝ) * -v)) / (j.factorial : ℝ) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 3; ring
  have hS : 2 * Real.sinh (v / 2) = Real.exp (v / 2) * (1 - Real.exp (-v)) := by
    rw [Real.sinh_eq,mul_sub,mul_one,← Real.exp_add,show v / 2 + -v = -(v / 2) by ring]
    ring
  have hR : Real.exp (-v * (p / 2)) * (Real.Gamma p * (1 - Real.exp (-v)) ^ (-p)) =
      Real.Gamma p * sinhProfile p v := by
    rw [sinhProfile,hS,Real.mul_rpow (Real.exp_pos _).le
      (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hv))).le,← Real.exp_mul]
    rw [show (v / 2) * (-p) = -v * (p / 2) by ring]
    ring
  simp_rw [hE,hR] at h
  exact h

end ACS12.GammaMeasure

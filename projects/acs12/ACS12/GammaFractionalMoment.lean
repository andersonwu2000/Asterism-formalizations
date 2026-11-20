import ACS12.GammaFractionalDeficit
import ACS12.DeficitProfile
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! The actual Gamma product's fractional moment and its ordinary full deficit integral. -/
namespace ACS12.GammaMixture

open MeasureTheory Set Filter
open GammaDeficit (deficitProfile sinhProfile)

theorem gammaTotal_fractional_eq_profile {p : ℝ} (hp : 2 < p) (hp₄ : p < 4) :
    let h := (p - 2) / 2
    IntegrableOn (fun t => t * deficitProfile p t) (Ioi 0) ∧
      (∫ ω : ℕ → ℝ, gammaTotal ω ^ h ∂gammaProduct p) =
        (2 * h / Real.Gamma (1 - h)) * ∫ t : ℝ in Ioi 0, t * deficitProfile p t := by
  let h := (p - 2) / 2
  have hp₀ : 0 < p := by linarith only [hp]
  have hh : 0 < h := by dsimp only [h]; linarith only [hp]
  have hh₁ : h < 1 := by dsimp only [h]; linarith only [hp₄]
  letI : IsProbabilityMeasure (gammaProduct p) := gammaProduct_probability hp₀
  let K (s : ℝ) := s ^ (-h - 1) * (1 - ∫ ω, Real.exp (-s * gammaTotal ω) ∂gammaProduct p)
  have hNonneg : ∀ᵐ ω ∂gammaProduct p, 0 ≤ gammaTotal ω :=
    Eventually.of_forall fun ω => ENNReal.toReal_nonneg
  obtain ⟨hKI,hK⟩ := fractionalMoment_eq_laplace (μ := gammaProduct p)
    measurable_gammaTotal (integrable_gammaTotal hp₀) hNonneg hh hh₁
  change IntegrableOn K (Ioi 0) at hKI
  change (∫ ω, gammaTotal ω ^ h ∂gammaProduct p) =
    (h / Real.Gamma (1 - h)) * ∫ s : ℝ in Ioi 0, K s at hK
  let f (t : ℝ) := t ^ (2 : ℕ)
  have hImg : f '' Ioi (0 : ℝ) = Ioi 0 := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact mem_Ioi.mpr (sq_pos_of_pos ht)
    · intro hx
      exact ⟨Real.sqrt x,mem_Ioi.mpr (Real.sqrt_pos.2 hx),Real.sq_sqrt (show 0 < x from hx).le⟩
  have hD (t : ℝ) : HasDerivAt f (2 * t) t := by
    simpa only [Nat.cast_ofNat,show (2 : ℕ) - 1 = 1 by decide,pow_one] using hasDerivAt_pow 2 t
  have hInj : (Ioi (0 : ℝ)).InjOn f := by
    intro x hx y hy he
    change x ^ 2 = y ^ 2 at he
    have hx₀ : 0 < x := hx
    have hy₀ : 0 < y := hy
    exact (sq_eq_sq₀ hx₀.le hy₀.le).mp he
  have hPoint (t : ℝ) (ht : 0 < t) : |2 * t| • K (f t) = 2 * (t * deficitProfile p t) := by
    have hSin : 0 < 2 * Real.sinh (t / 2) := mul_pos (by norm_num)
      (Real.sinh_pos_iff.mpr (by positivity))
    have hE : t ^ (-p) * (t / (2 * Real.sinh (t / 2))) ^ p = sinhProfile p t := by
      rw [sinhProfile,Real.div_rpow ht.le hSin.le,Real.rpow_neg ht.le,Real.rpow_neg hSin.le]
      field_simp [(Real.rpow_pos_of_pos ht p).ne',(Real.rpow_pos_of_pos hSin p).ne']
    have hR : (t ^ 2) ^ (-h - 1) = t ^ (-p) := by
      rw [← Real.rpow_two,← Real.rpow_mul ht.le]
      congr 1
      dsimp only [h]
      ring
    dsimp only [K,f,smul_eq_mul]
    rw [gammaTotal_laplace hp₀ ht,abs_of_pos (by positivity : 0 < 2 * t),hR]
    unfold deficitProfile
    rw [← hE]
    ring
  have hEq := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun t _ => (hD t).hasDerivWithinAt) hInj K
  have hI := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun t _ => (hD t).hasDerivWithinAt) hInj K
  rw [hImg] at hEq hI
  have hFI := hI.mp hKI
  have hI' : IntegrableOn (fun t => 2 * (t * deficitProfile p t)) (Ioi 0) := by
    apply hFI.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hPoint t ht
  have hEq' : (∫ s : ℝ in Ioi 0, K s) = 2 * ∫ t : ℝ in Ioi 0, t * deficitProfile p t := by
    rw [hEq,setIntegral_congr_fun measurableSet_Ioi (fun t ht => hPoint t ht),integral_const_mul]
  refine ⟨?_,?_⟩
  · have hJ := hI'.const_mul (1 / 2)
    exact hJ.congr (Eventually.of_forall fun _ => by ring)
  · rw [hK,hEq']
    ring

end ACS12.GammaMixture

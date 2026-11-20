import ACS12.GammaProductAnalytic
import CenteredCircle.IntegralProductComparison
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! A single exponential tilt supplies a uniform complex neighborhood of the Gamma Laplace law. -/
namespace ACS12.GammaMixture
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
set_option maxHeartbeats 1200000

theorem gammaLaplace_exponential_tilt {a t δ : ℝ} (ha : 0 < a) (ht : 0 ≤ t)
    (hδ : 0 ≤ δ) (hRate : δ < gammaRate 0) :
    (∫ ω, Real.exp (-t*gammaTotal ω)*(Real.exp (δ*gammaTotal ω)-1) ∂gammaProduct a) ≤
      (mgf gammaTotal (gammaProduct a) (-t))*(mgf gammaTotal (gammaProduct a) δ-1) := by
  letI := gammaProduct_probability ha
  let f (ω : ℕ → ℝ) := Real.exp (δ*gammaTotal ω)-1
  let g (ω : ℕ → ℝ) := Real.exp (-t*gammaTotal ω)
  have hE := gammaTotal_integrableExpSet ha hRate
  have hG := gammaTotal_integrableExpSet ha (show -t < gammaRate 0 by linarith only [ht,gammaRate_pos 0])
  have hF : Integrable f (gammaProduct a) := hE.sub (integrable_const 1)
  have hFG : Integrable (fun ω => f ω*g ω) (gammaProduct a) := by
    have h := (gammaTotal_integrableExpSet ha (show δ-t < gammaRate 0 by linarith only [ht,hRate])).sub hG
    apply h.congr
    exact Eventually.of_forall fun ω => by
      dsimp [f,g]
      rw [show (δ-t)*gammaTotal ω=δ*gammaTotal ω+(-t*gammaTotal ω) by ring,Real.exp_add]
      ring
  have hCov := CenteredCircle.AllN.integral_product_comparison hF hG hFG (integrable_const (1:ℝ)) (show
      ∀ᵐ x ∂gammaProduct a, ∀ᵐ y ∂gammaProduct a,
        0 ≤ f x*g y+f y*g x-(f x*g x)*1-(f y*g y)*1 from by
    exact Eventually.of_forall fun x => Eventually.of_forall fun y => by
      have hPair : 0 ≤ (f x-f y)*(g y-g x) := by
        rcases le_total (gammaTotal x) (gammaTotal y) with hxy | hyx
        · have hFxy : f x ≤ f y := sub_le_sub_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hxy hδ)) 1
          have hGyx : g y ≤ g x := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hxy (neg_nonpos.mpr ht))
          exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hFxy) (sub_nonpos.mpr hGyx)
        · have hFyx : f y ≤ f x := sub_le_sub_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hyx hδ)) 1
          have hGxy : g x ≤ g y := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hyx (neg_nonpos.mpr ht))
          exact mul_nonneg (sub_nonneg.mpr hFyx) (sub_nonneg.mpr hGxy)
      nlinarith only [hPair])
  simp only [integral_const,probReal_univ,smul_eq_mul,mul_one] at hCov
  have hFI : (∫ ω, f ω ∂gammaProduct a) = mgf gammaTotal (gammaProduct a) δ-1 := by
    rw [integral_sub hE (integrable_const 1)]
    simp only [mgf,integral_const,probReal_univ,smul_eq_mul,mul_one]
  rw [hFI] at hCov
  change (∫ ω, g ω*f ω ∂gammaProduct a) ≤ _
  simpa only [f,g,mul_comm] using hCov

theorem gammaLaplace_small_exponential_moment :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/2 ∧ δ < gammaRate 0 ∧
      mgf gammaTotal (gammaProduct 1) δ < 3/2 := by
  letI := gammaProduct_probability zero_lt_one
  have hCC := (gammaTotal_complexMGF_analytic zero_lt_one (z:=0)
    (show (0:ℝ)<gammaRate 0 from gammaRate_pos 0)).continuousAt
  have hCComplex : ContinuousAt (fun x : ℝ => complexMGF gammaTotal (gammaProduct 1) (x:ℂ)) 0 :=
    ContinuousAt.comp (g:=complexMGF gammaTotal (gammaProduct 1)) (f:=fun x : ℝ => (x:ℂ))
      hCC Complex.continuous_ofReal.continuousAt
  have hC : ContinuousAt (fun x : ℝ => (complexMGF gammaTotal (gammaProduct 1) (x:ℂ)).re) 0 :=
    Complex.continuous_re.continuousAt.comp hCComplex
  have hEq : (fun x : ℝ => (complexMGF gammaTotal (gammaProduct 1) (x:ℂ)).re) =
      mgf gammaTotal (gammaProduct 1) := by
    funext x
    rw [complexMGF_ofReal]
    rfl
  rw [hEq] at hC
  have h0 : mgf gammaTotal (gammaProduct 1) 0 = 1 := mgf_zero
  have hEvent : ∀ᶠ x : ℝ in 𝓝 0, mgf gammaTotal (gammaProduct 1) x < 3/2 := by
    exact hC.eventually (eventually_lt_nhds (by rw [h0]; norm_num : mgf gammaTotal (gammaProduct 1) 0 < 3/2))
  obtain ⟨ε,hε,hBall⟩ := Metric.mem_nhds_iff.mp hEvent
  let δ := min (ε/2) (min (gammaRate 0/2) (1/2))
  have hδ : 0 < δ := lt_min (half_pos hε) (lt_min (half_pos (gammaRate_pos 0)) (by norm_num))
  have hδε : δ < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hδR : δ < gammaRate 0 :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self (gammaRate_pos 0))
  refine ⟨δ,hδ,(min_le_right _ _).trans (min_le_right _ _),hδR,?_⟩
  exact hBall (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hδ] using hδε)

end ACS12.GammaMixture

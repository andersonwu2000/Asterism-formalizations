import ACS12.GammaLaplaceTilt
import ACS12.MellinPhiBounds

/-! Uniform complex shifts of the Gamma Laplace transform, paid by its original positive tilt. -/
namespace ACS12.NativeCells
open MeasureTheory ProbabilityTheory Set Filter GammaMixture
set_option maxHeartbeats 1500000

private theorem exp_sub_one_norm_price (x : ℂ) :
    ‖Complex.exp x-1‖ ≤ Real.exp ‖x‖-1 := by
  simpa only [Finset.sum_range_one,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one] using
    Complex.norm_exp_sub_sum_le_exp_norm_sub_sum x 1

theorem gammaLaplace_complex_shift_bound {t δ : ℝ} {h : ℂ} (ht : 0 < t)
    (hδ : 0 ≤ δ) (hRate : δ < gammaRate 0) (hh : ‖h‖ ≤ δ) :
    ‖gammaLaplaceGerm 1 ((t:ℂ)+h)-gammaLaplaceGerm 1 (t:ℂ)‖ ≤
      mellinPhi t*(mgf gammaTotal (gammaProduct 1) δ-1) := by
  let μ := gammaProduct 1
  letI : IsProbabilityMeasure μ := gammaProduct_probability zero_lt_one
  let X := gammaTotal
  let D (ω : ℕ → ℝ) : ℂ := (Real.exp (-t*X ω):ℂ)*(Complex.exp (-h*(X ω:ℂ))-1)
  let B (ω : ℕ → ℝ) : ℝ := Real.exp (-t*X ω)
  let G (ω : ℕ → ℝ) : ℝ := B ω*(Real.exp (δ*X ω)-1)
  have hE := gammaTotal_integrableExpSet zero_lt_one hRate
  have hB : Integrable B μ := gammaTotal_integrableExpSet zero_lt_one
    (show -t < gammaRate 0 by linarith only [ht,gammaRate_pos 0])
  have hGI : Integrable G μ := by
    have h := (gammaTotal_integrableExpSet zero_lt_one
      (show δ-t < gammaRate 0 by linarith only [ht,hRate])).sub hB
    apply h.congr
    exact Eventually.of_forall fun ω => by
      dsimp [G,B,X]
      rw [show (δ-t)*gammaTotal ω=(-t*gammaTotal ω)+(δ*gammaTotal ω) by ring,Real.exp_add]
      ring
  have hPoint (ω : ℕ → ℝ) : ‖D ω‖ ≤ G ω := by
    have hX : 0 ≤ X ω := ENNReal.toReal_nonneg
    have hArg : ‖-h*(X ω:ℂ)‖ ≤ δ*X ω := by
      rw [norm_mul,norm_neg,Complex.norm_real,Real.norm_of_nonneg hX]
      exact mul_le_mul_of_nonneg_right hh hX
    have hExp := (exp_sub_one_norm_price (-h*(X ω:ℂ))).trans
      (sub_le_sub_right (Real.exp_le_exp.mpr hArg) 1)
    dsimp only [D,G]
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left hExp (Real.exp_pos _).le
  have hDM : Measurable D := by
    have hX := measurable_gammaTotal
    dsimp [D,X]
    fun_prop
  have hDI : Integrable D μ := hGI.mono' hDM.aestronglyMeasurable
    (Eventually.of_forall hPoint)
  have hBC : Integrable (fun ω => (B ω:ℂ)) μ := hB.ofReal
  have hShift (ω : ℕ → ℝ) : Complex.exp (-((t:ℂ)+h)*(X ω:ℂ)) = D ω+(B ω:ℂ) := by
    dsimp [D,B]
    rw [show -((t:ℂ)+h)*(X ω:ℂ)=((-t*X ω:ℝ):ℂ)+(-h*(X ω:ℂ)) by push_cast; ring,
      Complex.exp_add,←Complex.ofReal_exp]
    ring
  have hShiftI : Integrable (fun ω => Complex.exp (-((t:ℂ)+h)*(X ω:ℂ))) μ :=
    (hDI.add hBC).congr (Eventually.of_forall fun ω => (hShift ω).symm)
  have hDifference : gammaLaplaceGerm 1 ((t:ℂ)+h)-gammaLaplaceGerm 1 (t:ℂ) = ∫ ω, D ω ∂μ := by
    unfold gammaLaplaceGerm complexMGF
    change (∫ ω, Complex.exp (-((t:ℂ)+h)*(X ω:ℂ)) ∂μ)-
      (∫ ω, Complex.exp (-(t:ℂ)*(X ω:ℂ)) ∂μ) = _
    have hBase (ω : ℕ → ℝ) : Complex.exp (-(t:ℂ)*(X ω:ℂ)) = (B ω:ℂ) := by
      dsimp [B]
      rw [show -(t:ℂ)*(X ω:ℂ)=((-t*X ω:ℝ):ℂ) by push_cast; ring,←Complex.ofReal_exp]
    simp_rw [hBase]
    rw [←integral_sub hShiftI hBC]
    apply integral_congr_ae
    exact Eventually.of_forall fun ω => by dsimp only; rw [hShift]; ring
  have hNorm : ‖∫ ω, D ω ∂μ‖ ≤ ∫ ω, G ω ∂μ :=
    (norm_integral_le_integral_norm _).trans (integral_mono_ae hDI.norm hGI (Eventually.of_forall hPoint))
  have hCov := gammaLaplace_exponential_tilt (a:=1) zero_lt_one ht.le hδ hRate
  have hPhi : mgf gammaTotal μ (-t) = mellinPhi t := by
    apply Complex.ofReal_injective
    have h := gammaLaplaceGerm_one_real ht
    unfold gammaLaplaceGerm at h
    rw [←Complex.ofReal_neg,complexMGF_ofReal] at h
    exact h
  dsimp [μ] at hPhi
  rw [hPhi] at hCov
  rw [hDifference]
  exact hNorm.trans (by simpa only [G,B,X,μ] using hCov)

end ACS12.NativeCells

import ACS12.GammaLaplaceComplexShift
import Mathlib.Analysis.Complex.Liouville

/-! One uniform disc controls every differentiated carrier on the complete positive ray. -/
namespace ACS12.NativeCells
open MeasureTheory ProbabilityTheory Set Filter GammaMixture Metric
set_option maxHeartbeats 1500000

noncomputable def gammaLaplaceRatio (t : ℝ) (w : ℂ) : ℂ :=
  gammaLaplaceGerm 1 w/(mellinPhi t:ℂ)

theorem gammaLaplace_uniform_ratio_disc :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/2 ∧ δ < gammaRate 0 ∧
      ∀ t : ℝ, 0 < t → ∀ w : ℂ, dist w (t:ℂ) ≤ δ →
        ‖gammaLaplaceRatio t w-1‖ ≤ 1/2 := by
  obtain ⟨δ,hδ,hδ₂,hRate,hM⟩ := gammaLaplace_small_exponential_moment
  refine ⟨δ,hδ,hδ₂,hRate,?_⟩
  intro t ht w hw
  have hPhi := mellinPhi_pos ht
  have hG := gammaLaplaceGerm_one_real ht
  have hBound := gammaLaplace_complex_shift_bound (h:=w-(t:ℂ)) ht hδ.le hRate
    (by simpa only [dist_eq_norm] using hw)
  rw [show (t:ℂ)+(w-(t:ℂ)) = w by ring] at hBound
  have hN : ‖gammaLaplaceGerm 1 w-gammaLaplaceGerm 1 (t:ℂ)‖ ≤ mellinPhi t/2 := by
    have h := mul_le_mul_of_nonneg_left (show mgf gammaTotal (gammaProduct 1) δ-1 ≤ (1/2:ℝ) by linarith only [hM]) hPhi.le
    exact hBound.trans (by linarith only [h])
  have hId : gammaLaplaceRatio t w-1 =
      (gammaLaplaceGerm 1 w-gammaLaplaceGerm 1 (t:ℂ))/(mellinPhi t:ℂ) := by
    rw [hG]
    unfold gammaLaplaceRatio
    field_simp [hPhi.ne']
    <;> ring
  rw [hId,norm_div,Complex.norm_real,Real.norm_of_nonneg hPhi.le]
  exact (div_le_iff₀ hPhi).mpr (by linarith only [hN])

theorem gammaLaplaceRatio_re_pos {t : ℝ} {w : ℂ}
    (h : ‖gammaLaplaceRatio t w-1‖ ≤ (1/2:ℝ)) : 0 < (gammaLaplaceRatio t w).re := by
  have hRe := (Complex.abs_re_le_norm (gammaLaplaceRatio t w-1)).trans h
  simp only [Complex.sub_re,Complex.one_re] at hRe
  have hLow := (abs_le.mp hRe).1
  linarith only [hLow]

theorem gammaLaplaceRatio_log_bound {t : ℝ} {w : ℂ}
    (h : ‖gammaLaplaceRatio t w-1‖ ≤ (1/2:ℝ)) : ‖Complex.log (gammaLaplaceRatio t w)‖ ≤ 1 := by
  have hLog := Complex.norm_log_one_add_half_le_self h
  rw [add_sub_cancel] at hLog
  linarith only [hLog,h]

theorem jointPhiLog_ratio {t : ℝ} {w : ℂ} (ht : 0 < t)
    (h : ‖gammaLaplaceRatio t w-1‖ ≤ (1/2:ℝ)) :
    jointPhiLog w = (Real.log (mellinPhi t):ℂ)+Complex.log (gammaLaplaceRatio t w) := by
  have hPhi := mellinPhi_pos ht
  have hR : gammaLaplaceRatio t w ≠ 0 := by
    intro hz
    have hPos := gammaLaplaceRatio_re_pos h
    rw [hz,Complex.zero_re] at hPos
    exact (lt_irrefl (0:ℝ)) hPos
  unfold jointPhiLog
  have hId : gammaLaplaceGerm 1 w = (mellinPhi t:ℂ)*gammaLaplaceRatio t w := by
    unfold gammaLaplaceRatio
    field_simp [hPhi.ne']
  rw [hId,Complex.log_ofReal_mul hPhi hR]

theorem jointLaplaceCarrier_disc_bound {α w : ℂ} {z t ε M A : ℝ}
    (ht : 0 < t) (hα : ε ≤ α.re)
    (hε : 0 < ε) (hM : ‖α‖ ≤ M) (hA : 0 ≤ A)
    (hNoise : ‖complexMGF boseNoise boseNoiseMeasure (-(z:ℂ)*w)‖ ≤ A)
    (hRatio : ‖gammaLaplaceRatio t w-1‖ ≤ (1/2:ℝ)) :
    ‖jointLaplaceCarrier α z w‖ ≤ A*Real.exp M*(mellinPhi t)^ε := by
  letI := boseNoise_probability
  have hPhi := mellinPhi_pos ht
  have hLog := gammaLaplaceRatio_log_bound hRatio
  have hExpNorm : ‖Complex.exp (α*Complex.log (gammaLaplaceRatio t w))‖ ≤ Real.exp M := by
    have hRe : (α*Complex.log (gammaLaplaceRatio t w)).re ≤ M := by
      calc
        _ ≤ ‖α*Complex.log (gammaLaplaceRatio t w)‖ := Complex.re_le_norm _
        _ = ‖α‖*‖Complex.log (gammaLaplaceRatio t w)‖ := norm_mul _ _
        _ ≤ M*1 := mul_le_mul hM hLog (norm_nonneg _) ((norm_nonneg α).trans hM)
        _ = M := mul_one M
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr hRe
  unfold jointLaplaceCarrier
  rw [jointPhiLog_ratio ht hRatio,mul_add,Complex.exp_add,norm_mul,norm_mul]
  have hReal : ‖Complex.exp (α*(Real.log (mellinPhi t):ℂ))‖ = (mellinPhi t)^α.re := by
    rw [Complex.norm_exp,Real.rpow_def_of_pos hPhi]
    congr 1
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    ring
  rw [hReal]
  have hPow := Real.rpow_le_rpow_of_exponent_ge hPhi (mellinPhi_le_one ht) hα
  have h := mul_le_mul (mul_le_mul hPow hExpNorm (norm_nonneg _) (Real.rpow_nonneg hPhi.le _))
    hNoise (norm_nonneg _) (by positivity : 0 ≤ (mellinPhi t)^ε*Real.exp M)
  simpa only [mul_one,one_mul,mul_assoc,mul_left_comm,mul_comm] using h

end ACS12.NativeCells

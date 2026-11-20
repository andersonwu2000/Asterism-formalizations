import ACS12.JointLaplaceDerivativeAnalytic

/-! A uniform positive-law disc gives all derivative orders the same complete tail. -/
namespace ACS12.NativeCells
open MeasureTheory ProbabilityTheory Set Filter GammaMixture Metric
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem jointLaplaceDerivative_uniform_bound {z ε M : ℝ} (hz : 0 ≤ z) (hε : 0 < ε) (k : ℕ) :
    ∃ C > 0, ∀ α : ℂ, ε ≤ α.re → ‖α‖ ≤ M → ∀ t : ℝ, 0 < t →
      ‖iteratedDeriv k (jointLaplaceCarrier α z) (t:ℂ)‖ ≤ C*(mellinPhi t)^ε := by
  obtain ⟨R,hR,hR₂,hRRate,hRatio⟩ := gammaLaplace_uniform_ratio_disc
  have hRatePos := gammaRate_pos 0
  let δ := min R (gammaRate 0/(2*(z+1)))
  have hδ : 0 < δ := lt_min hR (by positivity)
  have hδR : δ ≤ R := min_le_left _ _
  have hδRate : δ < gammaRate 0 := hδR.trans_lt hRRate
  have hδCap : δ*(2*(z+1)) ≤ gammaRate 0 :=
    (le_div_iff₀ (by positivity : 0 < 2*(z+1))).mp (min_le_right _ _)
  let c := z*δ
  have hc₀ : 0 ≤ c := mul_nonneg hz hδ.le
  have hc : c < gammaRate 0 := by dsimp [c]; nlinarith only [hδCap,hδ,gammaRate_pos 0]
  let A := mgf boseNoise boseNoiseMeasure c
  letI := boseNoise_probability
  have hAE : Integrable (fun s => Real.exp (c*boseNoise s)) boseNoiseMeasure := boseNoise_integrableExpSet hc
  have hA : 0 < A := mgf_pos hAE
  let C := (k.factorial:ℝ)*(A*Real.exp M)/δ^k
  have hFact : (0:ℝ) < k.factorial := Nat.cast_pos.mpr (Nat.factorial_pos k)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro α hα hM t ht
  have hDisc (w : ℂ) (hw : w ∈ closedBall (t:ℂ) δ) :
      -w.re < gammaRate 0 ∧ (-(z:ℂ)*w).re ≤ c ∧
        ‖gammaLaplaceRatio t w-1‖ ≤ (1/2:ℝ) := by
    have hDist := mem_closedBall.mp hw
    have hRe := (Complex.abs_re_le_norm (w-(t:ℂ))).trans
      (show ‖w-(t:ℂ)‖ ≤ δ by simpa only [dist_eq_norm] using hDist)
    simp only [Complex.sub_re,Complex.ofReal_re] at hRe
    have hLow : -δ ≤ w.re := by have h := (abs_le.mp hRe).1; linarith only [h,ht]
    refine ⟨by linarith only [hLow,hδRate],?_,hRatio t ht w (hDist.trans hδR)⟩
    have h := mul_le_mul_of_nonneg_left hLow hz
    dsimp [c]
    simp only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.ofReal_re,
      Complex.ofReal_im,neg_zero,zero_mul,sub_zero]
    linarith only [h]
  have hNoise (w : ℂ) (hw : w ∈ closedBall (t:ℂ) δ) :
      ‖complexMGF boseNoise boseNoiseMeasure (-(z:ℂ)*w)‖ ≤ A := by
    have h := norm_complexMGF_le_mgf (X:=boseNoise) (μ:=boseNoiseMeasure) (z:=-(z:ℂ)*w)
    apply h.trans
    unfold mgf
    have hBound := integral_mono_of_nonneg (μ:=boseNoiseMeasure)
      (Eventually.of_forall fun _ => (Real.exp_pos _).le) hAE
      (boseNoise_ae_pos.mono fun s hs => Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (hDisc w hw).2.1 hs.le))
    exact hBound
  have hAnalytic (w : ℂ) (hw : w ∈ closedBall (t:ℂ) δ) :
      AnalyticAt ℂ (jointLaplaceCarrier α z) w := by
    have hD := hDisc w hw
    have hG : 0 < (gammaLaplaceGerm 1 w).re := by
      have hRatioPos := gammaLaplaceRatio_re_pos hD.2.2
      have hPhi := mellinPhi_pos ht
      have hId : gammaLaplaceGerm 1 w = (mellinPhi t:ℂ)*gammaLaplaceRatio t w := by
        unfold gammaLaplaceRatio
        field_simp [hPhi.ne']
      rw [hId]
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
      exact mul_pos hPhi hRatioPos
    have hJ := jointLaplaceCarrier_joint_analytic (α:=α) hD.1 (hD.2.1.trans_lt hc)
      (Complex.mem_slitPlane_iff.mpr (Or.inl hG))
    exact hJ.comp_of_eq' (by fun_prop : AnalyticAt ℂ (fun x : ℂ => (α,x)) w) rfl
  have hOn : DifferentiableOn ℂ (jointLaplaceCarrier α z) (closedBall (t:ℂ) δ) :=
    fun w hw => (hAnalytic w hw).differentiableAt.differentiableWithinAt
  have hBound (w : ℂ) (hw : w ∈ sphere (t:ℂ) δ) :
      ‖jointLaplaceCarrier α z w‖ ≤ A*Real.exp M*(mellinPhi t)^ε := by
    have hwC : w ∈ closedBall (t:ℂ) δ := sphere_subset_closedBall hw
    exact jointLaplaceCarrier_disc_bound ht hα hε hM hA.le (hNoise w hwC) (hDisc w hwC).2.2
  have hK := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hδ
    ((hOn.mono closure_ball_subset_closedBall).diffContOnCl) hBound
  convert hK using 1
  dsimp [C]
  ring

end ACS12.NativeCells

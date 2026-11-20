import ACS12.PressureUnit
import ACS12.GammaLowSource

/-! Original incident rays and their complete A/B integrals. -/
namespace ACS12.Pressure

open Set Filter MeasureTheory CenteredCircle.AllN
open GammaMeasure (imageDensity imageDensity_pos continuous_imageDensity imageMoment
  imageMomentWeight imageSlopeTail_integrable hasSum_laplace_samples imageA imageB
  imageTail_moment_zero_a imageTail_moment_zero_b)

theorem leftDistance_eq_forward {n : ℕ} (S : AnchoredCircleSource (Fin n)) (i : Fin n) :
    S.leftDistance i = S.forwardDistance i S.root := by
  by_cases hi : i = S.root
  · simp [hi,AnchoredCircleSource.leftDistance,S.coordinate_root]
  · have h : S.coordinate S.root < S.coordinate i := by
      rw [S.coordinate_root]
      exact S.coordinate_pos_of_ne_root hi
    rw [S.forwardDistance_eq_wrap h,S.coordinate_root,AnchoredCircleSource.leftDistance]
    ring

theorem rayWeight_nonneg {n : ℕ} {L s : ℝ} (hL : 0 < L) (hs : 0 < s)
    {m : Fin n → ℝ} (hm : ∀ i, 0 ≤ m i) (d : Fin n → ℝ) :
    0 ≤ rayWeight L m d s := by
  unfold rayWeight
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (hm i) (div_nonneg (Real.exp_pos _).le (periodicDen_pos hL hs).le)

theorem leftRay_root_le_bose {n : ℕ} (S : AnchoredCircleSource (Fin n)) (hcap : S.HasCircularMassCaps)
    {s : ℝ} (hs : 0 < s) : leftRay S S.root s ≤ pressureBose 1 s := by
  let K (t : ℝ) := Real.exp (-s * t)
  have hK : QuadratureData K 1 := ⟨fun _ _ => (Real.exp_pos _).le,
    fun t u _ hu => (exponential_samples_hasSum s t u hs hu).summable,
    fun t _ => (strictMonoOn_samplingHead_exponential s t hs).monotoneOn,
    fun t _ => (strictAntiOn_samplingTail_exponential s t hs).antitoneOn,
    by
      intro t ht u hu h
      exact (strictAntiOn_samplingTail_exponential s 0 hs).antitoneOn
        (mem_Ioi.mpr (zero_lt_one.trans_le (mem_Ici.mp ht)))
        (mem_Ioi.mpr (zero_lt_one.trans_le (mem_Ici.mp hu))) h⟩
  have h := S.leftExterior_quadrature hK hcap
  have hE : S.leftExterior K = leftRay S S.root s := by
    unfold AnchoredCircleSource.leftExterior leftRay rayWeight
    apply Finset.sum_congr rfl
    intro i _
    dsimp only
    rw [← leftDistance_eq_forward]
    exact congrArg (S.mass i * ·) (exponential_samples_hasSum s (S.leftDistance i) S.period hs S.period_pos).tsum_eq
  rw [hE,samplingTail_exponential_zero hs zero_lt_one,← pressureBose_eq zero_lt_one hs] at h
  exact h

private theorem densityPolynomial_le_s {s : ℝ} (hs : 0 < s) (kind : CircleKernelKind) :
    densityPolynomial kind s ≤ s := by
  have hb : polyB s < s := by
    unfold polyB
    linarith only [Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hs)]
  cases kind
  · exact ((polyA_lt_polyB hs).trans hb).le
  · exact hb.le

theorem ray_moment_integral {n : ℕ} {p L : ℝ} (hp : 0 < p) (hL : 0 < L)
    (kind : CircleKernelKind) (m d : Fin n → ℝ) (hd : ∀ i, 0 < d i) :
    IntegrableOn (fun s => imageDensity p L s * densityPolynomial kind s * rayWeight L m d s) (Ioi 0) ∧
    (∫ s : ℝ in Ioi 0, imageDensity p L s * densityPolynomial kind s * rayWeight L m d s) =
      ∑ i, m i * imageTail (imageMoment p L kind 0) L (d i) := by
  let g (s : ℝ) := imageDensity p L s * densityPolynomial kind s
  let v (i : Fin n) (s : ℝ) := g s * (Real.exp (-s * d i) / periodicDen L s)
  have hg : Measurable g := ((continuous_imageDensity hp hL).mul (continuous_densityPolynomial kind)).measurable
  have hG (s : ℝ) (hs : 0 < s) : 0 ≤ g s :=
    mul_nonneg (imageDensity_pos hp hL hs).le (densityPolynomial_pos kind hs).le
  have hV (i : Fin n) : IntegrableOn (v i) (Ioi 0) := by
    have hm : Measurable (v i) := by
      unfold v
      refine hg.mul ?_
      unfold periodicDen
      fun_prop
    apply (imageSlopeTail_integrable hp hL (hd i)).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0 < s := hs
    have hExp := div_pos (Real.exp_pos (-s * d i)) (periodicDen_pos hL hs₀)
    have hV₀ : 0 ≤ v i s := mul_nonneg (hG s hs₀) hExp.le
    rw [Real.norm_of_nonneg hV₀]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (densityPolynomial_le_s hs₀ kind) (imageDensity_pos hp hL hs₀).le) hExp.le
  have hE (s : ℝ) : g s * rayWeight L m d s = ∑ i, m i * v i s := by
    rw [rayWeight,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    unfold v
    ring
  constructor
  · exact (integrable_finsetSum Finset.univ (fun i _ => (hV i).const_mul (m i))).congr
      (Eventually.of_forall fun s => (hE s).symm)
  · change (∫ s : ℝ in Ioi 0, g s * rayWeight L m d s) = _
    rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => hE s),
      integral_finsetSum _ (fun i _ => (hV i).const_mul (m i))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul]
    have h := (hasSum_laplace_samples g hg hG hL (hV i)).tsum_eq
    apply congrArg (m i * ·)
    simpa only [v,periodicDen,imageTail,imageMoment,imageMomentWeight,pow_zero,one_mul,g] using h.symm

theorem leftRay_root_moment_integral {n : ℕ} {p : ℝ} (hp : 0 < p)
    (S : AnchoredCircleSource (Fin n)) (kind : CircleKernelKind) :
    let K := match kind with
      | .a => imageA p S.period
      | .b => imageB p S.period
    IntegrableOn (fun s => imageDensity p S.period s * densityPolynomial kind s * leftRay S S.root s) (Ioi 0) ∧
    (∫ s : ℝ in Ioi 0, imageDensity p S.period s * densityPolynomial kind s * leftRay S S.root s) =
      S.leftExterior K := by
  have h := ray_moment_integral hp S.period_pos kind S.mass S.leftDistance S.leftDistance_pos
  have hD : S.leftDistance = fun i => S.forwardDistance i S.root := funext (leftDistance_eq_forward S)
  rw [← show rayWeight S.period S.mass S.leftDistance = leftRay S S.root by unfold leftRay; rw [hD]]
  refine ⟨h.1,h.2.trans ?_⟩
  cases kind
  · exact Finset.sum_congr rfl fun i _ =>
      congrArg (S.mass i * ·) (imageTail_moment_zero_a hp S.period_pos (S.leftDistance_pos i))
  · exact Finset.sum_congr rfl fun i _ =>
      congrArg (S.mass i * ·) (imageTail_moment_zero_b hp S.period_pos (S.leftDistance_pos i))

end ACS12.Pressure

import ACS12.JointConePrice
import ACS12.JointGapIncrement
import ACS12.JointMomentScaling

/-! The coupled increment of both source residuals on the whole pure-law cone. -/
namespace ACS12.GammaMeasure

open Set MeasureTheory Filter CenteredCircle.AllN
open GammaDeficit (lineDensity)

private noncomputable def coneGapIntegrand (g e x : ℝ) : ℝ :=
  jointCanonicalMu * ((1 + x) * Real.exp (-x) +
      polyA x * ∫ t in (0 : ℝ)..1, BoseShape.C ((1 - e * t) * x)) -
    jointPureLambda * Real.exp (-x) * polyA ((1 + g) * x) *
      (1 - ∫ t in (0 : ℝ)..1, BoseShape.C ((1 - e * t) * x))

private theorem scaledExpTail_secant_average {x e : ℝ} (hx : 0 < x) (he : 0 ≤ e) (he₁ : e < 1) :
    scaledExpTail x (1 - e) - scaledExpTail x 1 =
      e * ∫ t in (0 : ℝ)..1, BoseShape.C ((1 - e * t) * x) := by
  let F (t : ℝ) := scaledExpTail x (1 - e * t)
  let f (t : ℝ) := BoseShape.C ((1 - e * t) * x)
  have hPos {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 0 < 1 - e * t := by
    linarith only [he₁,mul_le_of_le_one_right he ht.2]
  have hD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt F (e * f t) t := by
    have h := ((hasDerivAt_id t).const_mul e).const_sub 1
    convert (scaledExpTail_derivative hx (hPos ht)).comp t h using 1
    unfold f
    simp only [id_eq,mul_one]
    rw [mul_comm x]
    ring
  have hC : ContinuousOn f (Icc (0 : ℝ) 1) := by
    intro t ht
    have h := (((hasDerivAt_id t).const_mul e).const_sub 1).mul_const x
    exact ((BoseShape.C_deriv (mul_pos (hPos ht) hx)).comp t h).continuousAt.continuousWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (fun t ht => hD t (by rw [uIcc_of_le zero_le_one] at ht; exact ht))
    ((hC.intervalIntegrable_of_Icc zero_le_one).const_mul e)
  rw [intervalIntegral.integral_const_mul] at h
  unfold F at h
  simpa only [mul_one,mul_zero,sub_zero] using h.symm

private theorem coneGap_at_zero {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    IntegrableOn (fun x => lineDensity p x * coneGapIntegrand 0 0 x) (Ioi 0) ∧
      (∫ x in Ioi 0, lineDensity p x * coneGapIntegrand 0 0 x) = jointPureMismatch p := by
  have hp₂ := hP.trans (by norm_num : (9 / 5 : ℝ) ≤ 2)
  obtain ⟨hA,hAE⟩ := jointGapD_moment hp hp₂
  obtain ⟨hB,hBE⟩ := jointGapB_moment hp hp₂
  let A (s : ℝ) := lineDensity p s * (1 - polyA s * (1 - BoseShape.C s))
  let B (s : ℝ) := lineDensity p s * Real.exp (-s) * polyA s * (1 - BoseShape.C s)
  change IntegrableOn A (Ioi 0) at hA
  change IntegrableOn B (Ioi 0) at hB
  have hEq (x : ℝ) : lineDensity p x * coneGapIntegrand 0 0 x =
      jointCanonicalMu * A x - jointPureLambda * B x := by
    unfold coneGapIntegrand A B polyA
    simp only [zero_mul,sub_zero,one_mul,add_zero,intervalIntegral.integral_const,sub_zero,smul_eq_mul]
    ring
  constructor
  · exact ((hA.const_mul _).sub (hB.const_mul _)).congr (Eventually.of_forall fun x => (hEq x).symm)
  · rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => hEq x),
      integral_sub (hA.const_mul _) (hB.const_mul _),integral_const_mul,integral_const_mul,
      hAE,hBE,jointPureMismatch]

private theorem coneGap_monotone_secant {g e E x : ℝ} (hg : 0 ≤ g) (he : 0 ≤ e) (heE : e ≤ E)
    (hE : E < 1) (hx : 0 < x) :
    coneGapIntegrand g e x ≤ coneGapIntegrand g E x := by
  let f (e t : ℝ) := BoseShape.C ((1 - e * t) * x)
  have hC {e : ℝ} (he₀ : 0 ≤ e) (he₁ : e < 1) : ContinuousOn (f e) (Icc (0 : ℝ) 1) := by
    intro t ht
    have hPos : 0 < (1 - e * t) * x := mul_pos (by linarith only [he₁,mul_le_of_le_one_right he₀ ht.2]) hx
    have h := (((hasDerivAt_id t).const_mul e).const_sub 1).mul_const x
    exact ((BoseShape.C_deriv hPos).comp t h).continuousAt.continuousWithinAt
  have hInt := intervalIntegral.integral_mono_on zero_le_one
    ((hC he (heE.trans_lt hE)).intervalIntegrable_of_Icc (μ := volume) zero_le_one)
    ((hC (he.trans heE) hE).intervalIntegrable_of_Icc (μ := volume) zero_le_one) (fun t ht => by
      have hPos (e' : ℝ) (he' : e' ≤ E) : 0 < (1 - e' * t) * x := by
        have h := (mul_le_mul_of_nonneg_right he' ht.1).trans (mul_le_of_le_one_right (he.trans heE) ht.2)
        exact mul_pos (by linarith only [h,hE]) hx
      exact BoseShape.C_antitone (hPos E le_rfl) (hPos e heE)
        (mul_le_mul_of_nonneg_right (sub_le_sub_left (mul_le_mul_of_nonneg_right heE ht.1) 1) hx.le))
  have hμ : 0 ≤ jointCanonicalMu := by linarith only [jointCanonicalMu_bounds.1]
  have hA := (polyA_pos hx).le
  have hB := (polyA_pos (mul_pos (by positivity : 0 < 1 + g) hx)).le
  have h₁ := mul_le_mul_of_nonneg_left hInt (show 0 ≤ jointCanonicalMu * polyA x by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hInt
    (show 0 ≤ jointPureLambda * Real.exp (-x) * polyA ((1 + g) * x) by unfold jointPureLambda; positivity)
  unfold coneGapIntegrand
  change _ ≤ _ at h₁ h₂
  linarith only [h₁,h₂]

private theorem coneGap_integral_eq {p L u m r : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) (hL : 0 < L)
    (hu : 0 < u) (hm : 0 < m) (hr : 0 < r) (hR : r < m) :
    let g := (u - m) / m
    let e := (m - r) / m
    IntegrableOn (fun x => lineDensity p x * coneGapIntegrand g e x) (Ioi 0) ∧
      jointPureValue p L u m r jointCanonicalMu - jointPureValue p L u m m jointCanonicalMu =
        (m - r) * m ^ (-p) * (∫ x in Ioi 0, lineDensity p x * coneGapIntegrand g e x) := by
  let g := (u - m) / m
  let e := (m - r) / m
  let d := m - r
  have hd : 0 < d := sub_pos.mpr hR
  have he : 0 ≤ e := (div_pos hd hm).le
  have he₁ : e < 1 := (div_lt_one hm).mpr (by linarith only [hr])
  have hE : 1 - e = r / m := by unfold e; field_simp [hm.ne']; ring
  have hUE : 1 + g = u / m := by unfold g; field_simp [hm.ne']; ring
  have hQ (s : ℝ) (hs : 0 < s) :
      scaledExpTail s r - scaledExpTail s m = d *
        (∫ t in (0 : ℝ)..1, BoseShape.C ((1 - e * t) * (m * s))) := by
    have hR := scaledExpTail_secant_average (mul_pos hm hs) he he₁
    have hS (v : ℝ) : m * scaledExpTail (m * s) (v / m) = scaledExpTail s v := by
      unfold scaledExpTail
      rw [show m * s * (v / m) = s * v by field_simp [hm.ne']]
      rw [← mul_div_assoc,mul_div_cancel₀ _ hm.ne']
    rw [hE] at hR
    have h₁ : m * scaledExpTail (m * s) 1 = scaledExpTail s m := by
      simpa only [div_self hm.ne'] using hS m
    have h := congrArg (m * ·) hR
    dsimp only at h
    rw [mul_sub,hS r,h₁] at h
    have hde : m * e = d := by unfold d e; field_simp [hm.ne']
    rw [← mul_assoc,hde] at h
    exact h
  have hPoint (s : ℝ) (hs : 0 < s) : jointGapRaw u m r jointCanonicalMu s = d * coneGapIntegrand g e (m * s) := by
    unfold jointGapRaw coneGapIntegrand adjacentBoseGap
    rw [show m - r + scaledExpTail s m - scaledExpTail s r =
      (m - r) - (scaledExpTail s r - scaledExpTail s m) by ring,hQ s hs,hUE,show u / m * (m * s) = u * s by field_simp [hm.ne'],
      show -(m * s) = -s * m by ring,show 1 + m * s = 1 + s * m by ring]
    unfold polyA at *
    rw [show -(m * s) = -s * m by ring]
    unfold d
    ring
  obtain ⟨hI,hIE⟩ := jointPure_gap_eq_integral (mu := jointCanonicalMu) hp (hP.trans (by norm_num)) hL hu hm hr
  have hScaled : IntegrableOn (fun s => lineDensity p s * coneGapIntegrand g e (m * s)) (Ioi 0) := by
    apply (hI.const_mul d⁻¹).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    change d⁻¹ * (lineDensity p s * jointGapRaw u m r jointCanonicalMu s) = _
    rw [hPoint s hs]
    field_simp [hd.ne']
  have hUnscaled : IntegrableOn (fun s => lineDensity p s * coneGapIntegrand g e s) (Ioi 0) := by
    apply (pureIntegral_integrable_scale (inv_pos.mpr hm) hScaled).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s _
    rw [← mul_assoc,mul_inv_cancel₀ hm.ne',one_mul]
  refine ⟨hUnscaled,?_⟩
  rw [hIE,setIntegral_congr_fun measurableSet_Ioi (g := fun s =>
    d * (lineDensity p s * coneGapIntegrand g e (m * s))) (fun s hs => by rw [hPoint s hs]; ring),
    integral_const_mul,pureIntegral_scale hm]
  exact (mul_assoc _ _ _).symm

private noncomputable def coneGapLine (g t x : ℝ) : ℝ :=
  jointCanonicalMu * ((1 + x) * Real.exp (-x) + polyA x * BoseShape.C (conePriceRadius g t * x)) -
    jointPureLambda * Real.exp (-x) * polyA ((1 + g) * x) * (1 - BoseShape.C (conePriceRadius g t * x))

private noncomputable def coneGapLineDerivative (g t x : ℝ) : ℝ :=
  ((9 / 10) * t * x) * (-BoseShape.C₁ (conePriceRadius g t * x)) *
    (jointCanonicalMu * polyA x + jointPureLambda * Real.exp (-x) * polyA ((1 + g) * x)) -
      jointPureLambda * (1 + g) * x ^ 2 * Real.exp (-x * (2 + g)) *
        (1 - BoseShape.C (conePriceRadius g t * x))

private theorem coneGapLine_deriv {g t x : ℝ} (hg : g ∈ Icc (0 : ℝ) (1 / 6))
    (ht : t ∈ Icc (0 : ℝ) 1) (hx : 0 < x) :
    HasDerivAt (fun v => coneGapLine v t x) (coneGapLineDerivative g t x) g := by
  let C (v : ℝ) := BoseShape.C (conePriceRadius v t * x)
  let A (v : ℝ) := polyA ((1 + v) * x)
  have hRadius : 0 < conePriceRadius g t := by
    have h := mul_le_mul hg.2 ht.2 ht.1 (by norm_num : (0 : ℝ) ≤ 1 / 6)
    unfold conePriceRadius
    linarith only [h]
  have hArg : HasDerivAt (fun v => conePriceRadius v t * x) (-(9 / 10) * t * x) g := by
    have h := ((((hasDerivAt_id g).const_mul (9 / 10 : ℝ)).mul_const t).const_sub 1).mul_const x
    convert h using 1
    simp only [mul_one]
    ring
  have hC := (BoseShape.C_deriv (mul_pos hRadius hx)).comp g hArg
  have hA := (hasDerivAt_polyA ((1 + g) * x)).comp g (((hasDerivAt_id g).const_add 1).mul_const x)
  have h := (((hC.const_mul (polyA x)).const_add ((1 + x) * Real.exp (-x))).const_mul jointCanonicalMu).sub
    ((hA.mul (hC.const_sub 1)).const_mul (jointPureLambda * Real.exp (-x)))
  convert h using 1
  · funext v
    unfold coneGapLine
    simp only [Pi.sub_apply,Pi.mul_apply,Function.comp_apply,id_eq]
    ring
  simp only [coneGapLineDerivative,Function.comp_apply,id_eq,mul_one,one_mul]
  rw [show -x * (2 + g) = -x + -((1 + g) * x) by ring,Real.exp_add]
  ring

private noncomputable def coneGapMajorant (g t x : ℝ) : ℝ :=
  (9 / 10) * t * (x * coneCurvatureUpper (conePriceRadius g t * x) *
    ((3553 / 200000) * polyA x + jointPureLambda * Real.exp (-x) * polyA ((1 + g) * x))) -
      jointPureLambda * (1 + g) * x ^ 2 * Real.exp (-x * (2 + g)) *
        (1 - BoseShape.C ((1 - (9 / 10) * g) * x))

private theorem coneGapLineDerivative_le {g t x : ℝ} (hg : g ∈ Icc (0 : ℝ) (1 / 6))
    (ht : t ∈ Icc (0 : ℝ) 1) (hx : 0 < x) :
    coneGapLineDerivative g t x ≤ coneGapMajorant g t x := by
  let r := conePriceRadius g t
  let R := 1 - (9 / 10) * g
  have hR : 0 < R := by unfold R; linarith only [hg.2]
  have hRr : R ≤ r := by
    have h := mul_le_of_le_one_right hg.1 ht.2
    unfold R r conePriceRadius
    linarith only [h]
  have hr := hR.trans_le hRr
  have hUpper := boseCurvature_cone_le (mul_pos hr hx)
  change -BoseShape.C₁ (r * x) ≤ coneCurvatureUpper (r * x) at hUpper
  have hA := (polyA_pos hx).le
  have hB := (polyA_pos (mul_pos (by have := hg.1; positivity : 0 < 1 + g) hx)).le
  have hμ : 0 ≤ jointCanonicalMu := by linarith only [jointCanonicalMu_bounds.1]
  have hLambda : 0 ≤ jointPureLambda := by norm_num [jointPureLambda]
  have hK : 0 ≤ jointCanonicalMu * polyA x + jointPureLambda * Real.exp (-x) * polyA ((1 + g) * x) := by positivity
  have hμU : jointCanonicalMu ≤ 3553 / 200000 := by linarith only [jointCanonicalMu_bounds.2]
  have hV := add_le_add_left (mul_le_mul_of_nonneg_right hμU hA)
    (jointPureLambda * Real.exp (-x) * polyA ((1 + g) * x))
  have hQ := mul_le_mul hUpper hV hK (coneCurvatureUpper_pos (mul_pos hr hx).le).le
  have hPos := mul_le_mul_of_nonneg_left hQ
    (show 0 ≤ (9 / 10 : ℝ) * t * x by have := ht.1; positivity)
  have hNeg := mul_le_mul_of_nonneg_left (BoseShape.C_antitone (mul_pos hR hx) (mul_pos hr hx)
    (mul_le_mul_of_nonneg_right hRr hx.le))
    (show 0 ≤ jointPureLambda * (1 + g) * x ^ 2 * Real.exp (-x * (2 + g)) by have := hg.1; positivity)
  unfold coneGapLineDerivative coneGapMajorant
  change _ ≤ _ at hPos hNeg
  linarith only [hPos,hNeg]

private theorem coneGapLine_average {g x : ℝ} (hg : g ∈ Icc (0 : ℝ) (1 / 6)) (hx : 0 < x) :
    (∫ t in (0 : ℝ)..1, coneGapLine g t x) = coneGapIntegrand g ((9 / 10) * g) x := by
  let C (t : ℝ) := BoseShape.C (conePriceRadius g t * x)
  have hC : ContinuousOn C (Icc (0 : ℝ) 1) := by
    intro t ht
    have hR : 0 < conePriceRadius g t := by
      have h := mul_le_mul hg.2 ht.2 ht.1 (by norm_num : (0 : ℝ) ≤ 1 / 6)
      unfold conePriceRadius
      linarith only [h]
    have h := ((((hasDerivAt_id t).const_mul ((9 / 10) * g)).const_sub 1).mul_const x)
    exact ((BoseShape.C_deriv (mul_pos hR hx)).comp t h).continuousAt.continuousWithinAt
  let A := jointCanonicalMu * ((1 + x) * Real.exp (-x)) -
    jointPureLambda * Real.exp (-x) * polyA ((1 + g) * x)
  let B := jointCanonicalMu * polyA x + jointPureLambda * Real.exp (-x) * polyA ((1 + g) * x)
  have hEq (t : ℝ) : coneGapLine g t x = A + B * C t := by unfold coneGapLine A B C; ring
  simp_rw [hEq]
  rw [intervalIntegral.integral_add intervalIntegrable_const ((hC.intervalIntegrable_of_Icc zero_le_one).const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const]
  simp only [sub_zero,smul_eq_mul,one_mul]
  change A + B * (∫ t in (0 : ℝ)..1, C t) = _
  unfold A B C conePriceRadius coneGapIntegrand
  ring

private theorem coneGapMajorant_integral_le {p g : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hg : g ∈ Icc (0 : ℝ) (1 / 6)) :
    let μ := volume.restrict (Ioi (0 : ℝ))
    let ν := volume.restrict (Ioc (0 : ℝ) 1)
    let F (z : ℝ × ℝ) := lineDensity p z.1 * coneGapMajorant g z.2 z.1
    Integrable F (μ.prod ν) ∧
      (∫ z, F z ∂(μ.prod ν)) ≤
        -jointPureLambda * (p * (p + 1) * (13 / 6 : ℝ) ^ (-(p + 2 : ℝ))) * (288479 / 1588261500) := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  let ν := volume.restrict (Ioc (0 : ℝ) 1)
  let f (z : ℝ × ℝ) := lineDensity p z.1 * coneGapMajorant g z.2 z.1
  let r := 1 - (9 / 10) * g
  let U := 1 + g
  let b := 2 + g
  let M := p * (p + 1) * b ^ (-(p + 2 : ℝ))
  let K (x : ℝ) := lineDensity p x * x ^ 2 * Real.exp (-x * b)
  let S (x : ℝ) := K x * BoseShape.C (r * x)
  let G (z : ℝ × ℝ) := lineDensity p z.1 * (z.1 * coneCurvatureUpper (conePriceRadius g z.2 * z.1) *
    ((3553 / 200000) * polyA z.1 + jointPureLambda * Real.exp (-z.1) * polyA (U * z.1)))
  have hp₀ := zero_lt_one.trans_le hp
  have hU : 1 ≤ U := by unfold U; linarith only [hg.1]
  have hb : 0 < b := by unfold b; have := hg.1; positivity
  have hbU : b ≤ 13 / 6 := by unfold b; linarith only [hg.2]
  have hr : 17 / 20 ≤ r := by unfold r; linarith only [hg.2]
  have hLambda : 0 < jointPureLambda := by norm_num [jointPureLambda]
  have hMem : ∀ᵐ z ∂(μ.prod ν), z.1 ∈ Ioi (0 : ℝ) ∧ z.2 ∈ Ioc (0 : ℝ) 1 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioi.prod measurableSet_Ioc)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact ⟨hx,ht⟩
  have hGI : Integrable G (μ.prod ν) := by
    let D (x : ℝ) := lineDensity p x * (x + x ^ 2 + x ^ 3) * Real.exp (-x * (17 / 20))
    have hD : Integrable D μ := by
      have h (k : ℕ) := (lineDensity_moment hp₀ (by norm_num : (0 : ℝ) < 17 / 20) k).1
      apply (((h 1).add (h 2)).add (h 3)).congr
      exact Eventually.of_forall fun x => by simp only [Pi.add_apply,pow_one,D]; ring
    have hDom : Integrable (fun z : ℝ × ℝ => D z.1 * 1) (μ.prod ν) :=
      hD.mul_prod (integrable_const (μ := ν) (1 : ℝ))
    have hGM : Measurable G := by unfold G lineDensity coneCurvatureUpper conePricePolynomial conePriceRadius polyA; fun_prop
    apply hDom.mono' hGM.aestronglyMeasurable
    filter_upwards [hMem] with z hz
    have hx : 0 < z.1 := hz.1
    have ht : z.2 ∈ Icc (0 : ℝ) 1 := ⟨hz.2.1.le,hz.2.2⟩
    let v := conePriceRadius g z.2
    have hv : v ∈ Icc (17 / 20 : ℝ) 1 := by
      have h := mul_le_mul hg.2 ht.2 ht.1 (by norm_num : (0 : ℝ) ≤ 1 / 6)
      have h' := mul_nonneg hg.1 ht.1
      constructor <;> unfold v conePriceRadius <;> linarith only [h,h']
    have hvx : 0 < v * z.1 := mul_pos ((by norm_num : (0 : ℝ) < 17 / 20).trans_le hv.1) hx
    have hUx := mul_pos (zero_lt_one.trans_le hU) hx
    have hA (x : ℝ) (hx : 0 < x) : polyA x ≤ 1 := by unfold polyA; exact sub_le_self _ (by positivity)
    let B := (3553 / 200000) * polyA z.1 + jointPureLambda * Real.exp (-z.1) * polyA (U * z.1)
    have hB₀ : 0 ≤ B := by
      unfold B
      exact add_nonneg (mul_nonneg (by norm_num) (polyA_pos hx).le)
        (mul_nonneg (by positivity) (polyA_pos hUx).le)
    have hB₁ : B ≤ 1 := by
      have h := mul_le_mul (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx.le)) (hA _ hUx)
        (polyA_pos hUx).le (by norm_num : (0 : ℝ) ≤ 1)
      unfold B jointPureLambda
      linarith only [h,hA _ hx]
    have hP' : conePricePolynomial (v * z.1) ≤ 1 + z.1 + z.1 ^ 2 := by
      have h := mul_le_of_le_one_left hx.le hv.2
      unfold conePricePolynomial
      nlinarith only [h,pow_le_pow_left₀ hvx.le h 2,hx,sq_nonneg z.1]
    have hP₀ : 0 ≤ conePricePolynomial (v * z.1) := by unfold conePricePolynomial; positivity
    have hE := Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hv.1 hx.le))
    have hρ := (lineDensity_pos hp₀ hx).le
    change ‖lineDensity p z.1 * (z.1 * coneCurvatureUpper (v * z.1) * B)‖ ≤ D z.1 * 1
    unfold coneCurvatureUpper
    rw [Real.norm_of_nonneg (by positivity),mul_one]
    have h := mul_le_mul hE ((mul_le_of_le_one_right hP₀ hB₁).trans hP')
      (mul_nonneg hP₀ hB₀) (Real.exp_pos _).le
    rw [show -(17 / 20 * z.1) = -z.1 * (17 / 20) by ring] at h
    unfold D
    linarith only [mul_le_mul_of_nonneg_left h (mul_nonneg hρ hx.le)]
  have hG₁ : Integrable (fun z : ℝ × ℝ => ((9 / 10) * z.2) * G z) (μ.prod ν) := by
    apply hGI.norm.mono' ((by
      unfold G lineDensity coneCurvatureUpper conePricePolynomial conePriceRadius polyA
      fun_prop : Measurable (fun z : ℝ × ℝ => ((9 / 10) * z.2) * G z)).aestronglyMeasurable)
    filter_upwards [hMem] with z hz
    rw [norm_mul,Real.norm_of_nonneg (mul_nonneg (by norm_num) hz.2.1.le)]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith only [hz.2.2])
  obtain ⟨hK,hKE⟩ := lineDensity_second_moment hp₀ hb
  change Integrable K μ at hK
  change (∫ x, K x ∂μ) = M at hKE
  have hr₀ := (by norm_num : (0 : ℝ) < 17 / 20).trans_le hr
  have hS : Integrable S μ := by
    have hM : Measurable S := by unfold S K lineDensity BoseShape.C; fun_prop
    apply hK.mono' hM.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx₀ : 0 < x := hx
    have hK₀ : 0 ≤ K x := by unfold K; have := lineDensity_pos hp₀ hx₀; positivity
    unfold S
    rw [Real.norm_of_nonneg (mul_nonneg hK₀ (BoseShape.C_pos (mul_pos hr₀ hx₀)).le)]
    exact mul_le_of_le_one_right hK₀ ((boseC_lt_half (mul_pos hr₀ hx₀)).le.trans (by norm_num))
  let N (x : ℝ) := jointPureLambda * U * (K x - S x)
  have hN : Integrable N μ := (hK.sub hS).const_mul _
  have hN' : Integrable (fun z : ℝ × ℝ => N z.1) (μ.prod ν) := by
    simpa only [mul_one] using hN.mul_prod (integrable_const (μ := ν) (1 : ℝ))
  have hE (z : ℝ × ℝ) : f z = (9 / 10) * z.2 * G z - N z.1 := by
    unfold f coneGapMajorant G N S K r U b
    ring
  have hI : Integrable f (μ.prod ν) := (hG₁.sub hN').congr (Eventually.of_forall fun z => (hE z).symm)
  refine ⟨hI,?_⟩
  rw [integral_congr_ae (Eventually.of_forall hE),integral_sub hG₁ hN']
  have hGE : (∫ z, (9 / 10) * z.2 * G z ∂(μ.prod ν)) =
      (9 / 10) * ∫ t in (0 : ℝ)..1, t * conePositiveMoment p g t := by
    rw [integral_prod_symm _ hG₁,intervalIntegral.integral_of_le zero_le_one,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [integral_const_mul]
    change (9 / 10 : ℝ) * t * conePositiveMoment p g t = (9 / 10) * (t * conePositiveMoment p g t)
    ring
  have hNE : (∫ z, N z.1 ∂(μ.prod ν)) = jointPureLambda * U * (M - ∫ x, S x ∂μ) := by
    rw [integral_prod_symm _ hN']
    change (∫ _ : ℝ, (∫ x, N x ∂μ) ∂ν) = _
    rw [integral_const,Measure.real]
    have hν : ν Set.univ = 1 := by simp [ν,Measure.restrict_apply,Real.volume_Ioc]
    rw [hν,ENNReal.toReal_one,one_smul]
    unfold N
    rw [integral_const_mul,integral_sub hK hS,hKE]
  rw [hGE,hNE]
  have hPos := conePositiveIntegral_price hp hP hg
  change _ ≤ jointPureLambda * (199/200-(1/2)*(130/147:ℝ)^(p+2)) * U * M at hPos
  have hNeg := jointCone_negative_part_le hp hb hbU hr
  change (∫ x, S x ∂μ) ≤ (1 / 2) * (130 / 147 : ℝ) ^ (p+2) * M at hNeg
  have hMul := mul_le_mul_of_nonneg_left hNeg (mul_nonneg hLambda.le (zero_le_one.trans hU))
  have hM : 0 ≤ M := by unfold M; positivity
  have hScale : (13 / 6 : ℝ) ^ (-(p + 2 : ℝ)) ≤ b ^ (-(p + 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hb hbU (neg_nonpos.mpr (by positivity : 0 ≤ p + 2))
  have hScale' := mul_le_mul_of_nonneg_left hScale (show 0 ≤ p * (p + 1) by positivity)
  have hU' := mul_le_mul_of_nonneg_right hU hM
  have hB := mul_le_mul_of_nonneg_left (hScale'.trans (by simpa only [one_mul,M] using hU'))
    (show 0 ≤ jointPureLambda * (288479 / 1588261500) by positivity)
  have hRoom := mul_le_mul_of_nonneg_right
    (by norm_num : (288479/1588261500:ℝ) ≤ 1/200)
    (mul_nonneg (mul_nonneg hLambda.le (zero_le_one.trans hU)) hM)
  nlinarith only [hPos,hMul,hB,hRoom]

private theorem coneGapLine_majorized {g t x : ℝ} (hg : g ∈ Icc (0 : ℝ) (1 / 6))
    (ht : t ∈ Icc (0 : ℝ) 1) (hx : 0 < x) :
    coneGapLine g t x - coneGapLine 0 t x ≤ ∫ v in (0 : ℝ)..g, coneGapMajorant v t x := by
  have hSub {v : ℝ} (hv : v ∈ Icc (0 : ℝ) g) : v ∈ Icc (0 : ℝ) (1 / 6) :=
    ⟨hv.1,hv.2.trans hg.2⟩
  have hRadius {v : ℝ} (hv : v ∈ Icc (0 : ℝ) g) : 0 < conePriceRadius v t * x := by
    have h := mul_le_mul (hSub hv).2 ht.2 ht.1 (by norm_num : (0 : ℝ) ≤ 1 / 6)
    unfold conePriceRadius
    exact mul_pos (by linarith only [h]) hx
  have hR₁ {v : ℝ} (hv : v ∈ Icc (0 : ℝ) g) : 0 < (1 - (9 / 10) * v) * x :=
    mul_pos (by linarith only [(hSub hv).2]) hx
  have hC (f : ℝ → ℝ) (hf : Differentiable ℝ f) (hP : ∀ v ∈ Icc (0 : ℝ) g, 0 < f v) :
      ContinuousOn (fun v => BoseShape.C (f v)) (Icc (0 : ℝ) g) :=
    fun v hv => ((BoseShape.C_deriv (hP v hv)).continuousAt.comp (hf v).continuousAt).continuousWithinAt
  have hC₁ (f : ℝ → ℝ) (hf : Differentiable ℝ f) (hP : ∀ v ∈ Icc (0 : ℝ) g, 0 < f v) :
      ContinuousOn (fun v => BoseShape.C₁ (f v)) (Icc (0 : ℝ) g) :=
    fun v hv => ((BoseShape.C₁_deriv (hP v hv)).continuousAt.comp (hf v).continuousAt).continuousWithinAt
  have hDiff : Differentiable ℝ (fun v => conePriceRadius v t * x) := by unfold conePriceRadius; fun_prop
  have hD : ContinuousOn (fun v => coneGapLineDerivative v t x) (Icc 0 g) := by
    unfold coneGapLineDerivative
    refine ContinuousOn.sub (ContinuousOn.mul (ContinuousOn.mul continuousOn_const
      (hC₁ _ hDiff (fun _ hv => hRadius hv)).neg) (by unfold polyA; fun_prop)) ?_
    exact ContinuousOn.mul (by fun_prop) (continuousOn_const.sub (hC _ hDiff (fun _ hv => hRadius hv)))
  have hM : ContinuousOn (fun v => coneGapMajorant v t x) (Icc 0 g) := by
    unfold coneGapMajorant
    exact ContinuousOn.sub (by unfold coneCurvatureUpper conePricePolynomial conePriceRadius polyA; fun_prop)
      (ContinuousOn.mul (by fun_prop)
        (continuousOn_const.sub (hC _ (by fun_prop) (fun _ hv => hR₁ hv))))
  have hDI := hD.intervalIntegrable_of_Icc (μ := volume) hg.1
  have hMI := hM.intervalIntegrable_of_Icc (μ := volume) hg.1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := g)
    (fun v hv => coneGapLine_deriv (hSub (by rwa [uIcc_of_le hg.1] at hv)) ht hx) hDI
  rw [← hFTC]
  exact intervalIntegral.integral_mono_on hg.1 hDI hMI fun v hv => coneGapLineDerivative_le (hSub hv) ht hx

private theorem coneGapIncrement_integral_le {p g : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hg : g ∈ Icc (0 : ℝ) (1 / 6)) :
    let κ := jointPureLambda * (p * (p + 1) * (13 / 6 : ℝ) ^ (-(p + 2 : ℝ))) * (288479 / 1588261500)
    IntegrableOn (fun x => lineDensity p x * coneGapIntegrand g ((9 / 10) * g) x) (Ioi 0) ∧
      (∫ x in Ioi 0, lineDensity p x * coneGapIntegrand g ((9 / 10) * g) x) ≤ jointPureMismatch p - κ * g := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  let ν := volume.restrict (Ioc (0 : ℝ) 1)
  let τ := volume.restrict (Ioc (0 : ℝ) g)
  let κ := jointPureLambda * (p * (p + 1) * (13 / 6 : ℝ) ^ (-(p + 2 : ℝ))) * (288479 / 1588261500)
  let F (v : ℝ) (z : ℝ × ℝ) := lineDensity p z.1 * coneGapMajorant v z.2 z.1
  let R (v : ℝ) (z : ℝ × ℝ) := lineDensity p z.1 * coneGapLine v z.2 z.1
  have hp₀ := zero_lt_one.trans_le hp
  have h0 : (0 : ℝ) ∈ Icc 0 (1 / 6) := by norm_num
  have hMem : ∀ᵐ z ∂(μ.prod ν), z.1 ∈ Ioi (0 : ℝ) ∧ z.2 ∈ Ioc (0 : ℝ) 1 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioi.prod measurableSet_Ioc)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact ⟨hx,ht⟩
  have hR (v : ℝ) (hv : v ∈ Icc (0 : ℝ) (1 / 6)) : Integrable (R v) (μ.prod ν) := by
    let D (x : ℝ) := lineDensity p x * ((1 + x) * Real.exp (-x) + Real.exp (-x * (17 / 60)) + Real.exp (-x))
    have hD : Integrable D μ := by
      have h₁ := (lineDensity_moment hp₀ (by norm_num : (0 : ℝ) < 1) 0).1
      have h₂ := (lineDensity_moment hp₀ (by norm_num : (0 : ℝ) < 1) 1).1
      have h₃ := (lineDensity_moment hp₀ (by norm_num : (0 : ℝ) < 17 / 60) 0).1
      apply (((h₁.const_mul 2).add h₂).add h₃).congr
      exact Eventually.of_forall fun x => by simp only [Pi.add_apply,pow_zero,pow_one,mul_one,D]; ring
    have hDom : Integrable (fun z : ℝ × ℝ => D z.1 * 1) (μ.prod ν) :=
      hD.mul_prod (integrable_const (μ := ν) (1 : ℝ))
    have hM : Measurable (R v) := by unfold R coneGapLine lineDensity BoseShape.C conePriceRadius polyA; fun_prop
    apply hDom.mono' hM.aestronglyMeasurable
    filter_upwards [hMem] with z hz
    let x := z.1
    let t := z.2
    let r := conePriceRadius v t
    have hx : 0 < x := hz.1
    have ht : t ∈ Icc (0 : ℝ) 1 := ⟨hz.2.1.le,hz.2.2⟩
    have hr : 17 / 20 ≤ r := by
      have h := mul_le_mul hv.2 ht.2 ht.1 (by norm_num : (0 : ℝ) ≤ 1 / 6)
      unfold r conePriceRadius
      linarith only [h]
    have hrx : 0 < r * x := mul_pos ((by norm_num : (0 : ℝ) < 17 / 20).trans_le hr) hx
    have hA₀ (y : ℝ) (hy : 0 < y) := (polyA_pos hy).le
    have hA₁ (y : ℝ) (hy : 0 < y) : polyA y ≤ 1 := by unfold polyA; exact sub_le_self _ (by positivity)
    have hy : 0 < (1 + v) * x := mul_pos (by have := hv.1; positivity) hx
    have hC := (BoseShape.C_pos hrx).le
    have hC₁ := (boseC_lt_half hrx).le.trans (by norm_num : (1 / 2 : ℝ) ≤ 1)
    have hC' : BoseShape.C (r * x) ≤ Real.exp (-x * (17 / 60)) := by
      have h := Real.exp_le_exp.mpr (show -(r * x) / 3 ≤ -x * (17 / 60) by
        nlinarith only [mul_le_mul_of_nonneg_right hr hx.le])
      have hE := Real.exp_pos (-x * (17 / 60))
      linarith only [boseC_exp_upper hrx,h,hE]
    have hμ₀ : 0 ≤ jointCanonicalMu := by linarith only [jointCanonicalMu_bounds.1]
    have hμ₁ : jointCanonicalMu ≤ 1 := by linarith only [jointCanonicalMu_bounds.2]
    have hLambda₀ : 0 ≤ jointPureLambda := by norm_num [jointPureLambda]
    have hLambda₁ : jointPureLambda ≤ 1 := by norm_num [jointPureLambda]
    let A := jointCanonicalMu * ((1 + x) * Real.exp (-x) + polyA x * BoseShape.C (r * x))
    let B := jointPureLambda * Real.exp (-x) * polyA ((1 + v) * x) * (1 - BoseShape.C (r * x))
    have hAx := hA₀ x hx
    have hAy := hA₀ _ hy
    have hA : 0 ≤ A := by unfold A; positivity
    have hB : 0 ≤ B := by
      unfold B
      exact mul_nonneg (mul_nonneg (mul_nonneg hLambda₀ (Real.exp_pos _).le) hAy) (sub_nonneg.mpr hC₁)
    have hAU : A ≤ (1 + x) * Real.exp (-x) + Real.exp (-x * (17 / 60)) := by
      unfold A
      exact (mul_le_of_le_one_left (by positivity) hμ₁).trans (add_le_add_right
        ((mul_le_of_le_one_left hC (hA₁ x hx)).trans hC') _)
    have hBU : B ≤ Real.exp (-x) := by
      unfold B
      exact (mul_le_of_le_one_right (by positivity) (sub_le_self _ hC)).trans
        ((mul_le_of_le_one_right (by positivity) (hA₁ _ hy)).trans (mul_le_of_le_one_left (Real.exp_pos _).le hLambda₁))
    have hρ := (lineDensity_pos hp₀ hx).le
    change ‖lineDensity p x * (A - B)‖ ≤ D x * 1
    rw [norm_mul,Real.norm_of_nonneg hρ,mul_one]
    have hAB : ‖A - B‖ ≤ A + B := by
      simpa only [Real.norm_eq_abs,abs_of_nonneg hA,abs_of_nonneg hB] using norm_sub_le A B
    exact mul_le_mul_of_nonneg_left (hAB.trans (add_le_add hAU hBU)) hρ
  let G (a : (ℝ × ℝ) × ℝ) := F a.2 a.1
  have hG : Integrable G ((μ.prod ν).prod τ) := by
    let B (x : ℝ) := 2 * lineDensity p x * (x + x ^ 2 + x ^ 3) * Real.exp (-x * (17 / 20))
    have hB : Integrable B μ := by
      have h (k : ℕ) := (lineDensity_moment hp₀ (by norm_num : (0 : ℝ) < 17 / 20) k).1
      apply ((((h 1).add (h 2)).add (h 3)).const_mul 2).congr
      exact Eventually.of_forall fun x => by simp only [Pi.add_apply,pow_one,B]; ring
    have hB' : Integrable (fun z : ℝ × ℝ => B z.1) (μ.prod ν) := by
      simpa only [mul_one] using hB.mul_prod (integrable_const (μ := ν) (1 : ℝ))
    have hDom : Integrable (fun a : (ℝ × ℝ) × ℝ => B a.1.1 * 1) ((μ.prod ν).prod τ) :=
      hB'.mul_prod (integrable_const (μ := τ) (1 : ℝ))
    have hM : Measurable G := by unfold G F coneGapMajorant coneCurvatureUpper conePricePolynomial conePriceRadius lineDensity polyA BoseShape.C; fun_prop
    apply hDom.mono' hM.aestronglyMeasurable
    have hMem' : ∀ᵐ a ∂((μ.prod ν).prod τ), (a.1.1 ∈ Ioi (0 : ℝ) ∧ a.1.2 ∈ Ioc (0 : ℝ) 1) ∧ a.2 ∈ Ioc (0 : ℝ) g := by
      apply (Measure.ae_prod_iff_ae_ae ((measurableSet_Ioi.prod measurableSet_Ioc).prod measurableSet_Ioc)).mpr
      filter_upwards [hMem] with z hz
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      exact ⟨hz,hv⟩
    filter_upwards [hMem'] with a ha
    let x := a.1.1
    let t := a.1.2
    let v := a.2
    let r := conePriceRadius v t
    have hx : 0 < x := ha.1.1
    have hv : v ∈ Icc (0 : ℝ) (1 / 6) := ⟨ha.2.1.le,ha.2.2.trans hg.2⟩
    have ht : t ∈ Icc (0 : ℝ) 1 := ⟨ha.1.2.1.le,ha.1.2.2⟩
    have hr : r ∈ Icc (17 / 20 : ℝ) 1 := by
      have h := mul_le_mul hv.2 ht.2 ht.1 (by norm_num : (0 : ℝ) ≤ 1 / 6)
      have h' := mul_nonneg hv.1 ht.1
      constructor <;> unfold r conePriceRadius <;> linarith only [h,h']
    have hrx : 0 < r * x := mul_pos ((by norm_num : (0 : ℝ) < 17 / 20).trans_le hr.1) hx
    have hA (y : ℝ) (hy : 0 < y) : 0 ≤ polyA y ∧ polyA y ≤ 1 :=
      ⟨(polyA_pos hy).le,by unfold polyA; exact sub_le_self _ (by positivity)⟩
    have hU : 0 < 1 + v := by have := hv.1; positivity
    let P := (3553 / 200000) * polyA x + jointPureLambda * Real.exp (-x) * polyA ((1 + v) * x)
    have hLambda₀ : 0 ≤ jointPureLambda := by norm_num [jointPureLambda]
    have hP₀ : 0 ≤ P := by
      unfold P
      exact add_nonneg (mul_nonneg (by norm_num) (hA _ hx).1)
        (mul_nonneg (by positivity) (hA _ (mul_pos hU hx)).1)
    have hP₁ : P ≤ 1 := by
      have h := mul_le_mul (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx.le)) (hA _ (mul_pos hU hx)).2
        (hA _ (mul_pos hU hx)).1 (by norm_num : (0 : ℝ) ≤ 1)
      unfold P jointPureLambda
      linarith only [h,(hA _ hx).2]
    have hQ₀ : 0 ≤ conePricePolynomial (r * x) := by unfold conePricePolynomial; positivity
    have hQ₁ : conePricePolynomial (r * x) ≤ 1 + x + x ^ 2 := by
      have h := mul_le_of_le_one_left hx.le hr.2
      unfold conePricePolynomial
      nlinarith only [h,pow_le_pow_left₀ hrx.le h 2,hx,sq_nonneg x]
    have hC₀ : 0 < (1 - (9 / 10) * v) * x := mul_pos (by linarith only [hv.2]) hx
    have hC := (BoseShape.C_pos hC₀).le
    have hC₁ : BoseShape.C ((1 - (9 / 10) * v) * x) ≤ 1 := (boseC_lt_half hC₀).le.trans (by norm_num)
    have hρ := (lineDensity_pos hp₀ hx).le
    let A := (9 / 10) * t * (x * coneCurvatureUpper (r * x) * P)
    let D := jointPureLambda * (1 + v) * x ^ 2 * Real.exp (-x * (2 + v)) *
      (1 - BoseShape.C ((1 - (9 / 10) * v) * x))
    have hA₀ : 0 ≤ A := by unfold A; have := ht.1; have := (coneCurvatureUpper_pos hrx.le).le; positivity
    have hD₀ : 0 ≤ D := by unfold D; have := sub_nonneg.mpr hC₁; positivity
    have hA₁ : A ≤ x * (1 + x + x ^ 2) * Real.exp (-x * (17 / 20)) := by
      have hE := Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hr.1 hx.le))
      have h := mul_le_mul hE ((mul_le_of_le_one_right hQ₀ hP₁).trans hQ₁)
        (mul_nonneg hQ₀ hP₀) (Real.exp_pos _).le
      unfold A coneCurvatureUpper
      have hMul := mul_le_mul_of_nonneg_left h hx.le
      have ht₀ := ht.1
      have ht₁ : (9 / 10) * t ≤ 1 := by linarith only [ht.2]
      have hA := mul_le_of_le_one_left (show 0 ≤ x * (Real.exp (-(r * x)) * conePricePolynomial (r * x)) * P by positivity) ht₁
      rw [show -(17 / 20 * x) = -x * (17 / 20) by ring] at hMul
      linarith only [hMul,hA]
    have hD₁ : D ≤ x ^ 2 * Real.exp (-x * (17 / 20)) := by
      have hE := Real.exp_le_exp.mpr (show -x * (2 + v) ≤ -x * (17 / 20) by
        nlinarith only [mul_nonneg hx.le hv.1,hx])
      have hL : jointPureLambda * (1 + v) ≤ 1 := by unfold jointPureLambda; linarith only [hv.2]
      unfold D
      have hB := mul_le_of_le_one_right
        (show 0 ≤ jointPureLambda * (1 + v) * x ^ 2 * Real.exp (-x * (2 + v)) by positivity)
        (sub_le_self 1 hC)
      have hC := mul_le_of_le_one_left (show 0 ≤ x ^ 2 * Real.exp (-x * (2 + v)) by positivity) hL
      linarith only [hB,hC,mul_le_mul_of_nonneg_left hE (sq_nonneg x)]
    change ‖lineDensity p x * (A - D)‖ ≤ B x * 1
    rw [norm_mul,Real.norm_of_nonneg hρ,mul_one]
    have hAD : ‖A - D‖ ≤ A + D := by
      simpa only [Real.norm_eq_abs,abs_of_nonneg hA₀,abs_of_nonneg hD₀] using norm_sub_le A D
    have h := mul_le_mul_of_nonneg_left (hAD.trans (add_le_add hA₁ hD₁)) hρ
    have hB := mul_nonneg (mul_nonneg hρ (add_nonneg hx.le (pow_nonneg hx.le 3))) (Real.exp_pos (-x * (17 / 20))).le
    unfold B
    linarith only [h,hB]
  have hCmp : (∫ z, R g z ∂(μ.prod ν)) - (∫ z, R 0 z ∂(μ.prod ν)) ≤
      ∫ a, G a ∂((μ.prod ν).prod τ) := by
    rw [← integral_sub (hR g hg) (hR 0 h0),integral_prod G hG]
    apply integral_mono_ae ((hR g hg).sub (hR 0 h0)) hG.integral_prod_left
    filter_upwards [hMem] with z hz
    have h := coneGapLine_majorized hg (show z.2 ∈ Icc (0 : ℝ) 1 from ⟨hz.2.1.le,hz.2.2⟩) hz.1
    have hρ := (lineDensity_pos hp₀ hz.1).le
    rw [intervalIntegral.integral_of_le hg.1] at h
    change R g z - R 0 z ≤ ∫ v, F v z ∂τ
    unfold F R
    rw [integral_const_mul]
    linarith only [mul_le_mul_of_nonneg_left h hρ]
  have hInt (v : ℝ) (hv : v ∈ Icc (0 : ℝ) (1 / 6)) :
      Integrable (fun x => lineDensity p x * coneGapIntegrand v ((9 / 10) * v) x) μ ∧
      (∫ z, R v z ∂(μ.prod ν)) = ∫ x, lineDensity p x * coneGapIntegrand v ((9 / 10) * v) x ∂μ := by
    have hEq : ∀ᵐ x ∂μ, (∫ t, R v (x,t) ∂ν) = lineDensity p x * coneGapIntegrand v ((9 / 10) * v) x := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have h := coneGapLine_average hv hx
      rw [intervalIntegral.integral_of_le zero_le_one] at h
      change (∫ t, lineDensity p x * coneGapLine v t x ∂ν) = _
      rw [integral_const_mul,h]
    exact ⟨(hR v hv).integral_prod_left.congr hEq, (integral_prod _ (hR v hv)).trans (integral_congr_ae hEq)⟩
  have h0E := (coneGap_at_zero hp hP).2
  have h0I := (hInt 0 h0).2
  rw [mul_zero,h0E] at h0I
  rw [(hInt g hg).2,h0I,integral_prod_symm G hG] at hCmp
  have hBound : (∫ v, (∫ z, G (z,v) ∂(μ.prod ν)) ∂τ) ≤ -κ * g := by
    have hν : τ Set.univ = ENNReal.ofReal g := by simp [τ,Measure.restrict_apply,Real.volume_Ioc]
    have hConst : (∫ v : ℝ, -κ ∂τ) = -κ * g := by
      rw [integral_const,Measure.real,hν,ENNReal.toReal_ofReal hg.1,smul_eq_mul,mul_comm]
    rw [← hConst]
    apply integral_mono_ae hG.integral_prod_right (integrable_const _)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact (coneGapMajorant_integral_le hp hP ⟨hv.1.le,hv.2.trans hg.2⟩).2.trans_eq (by unfold κ; ring)
  refine ⟨(hInt g hg).1,?_⟩
  change (∫ x, lineDensity p x * coneGapIntegrand g ((9 / 10) * g) x ∂μ) ≤ jointPureMismatch p - κ * g
  linarith only [hCmp,hBound]

theorem jointPure_wholeCone_increment {p L u m r : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) (hL : 0 < L)
    (huL : 7 / 8 ≤ u) (hu₁ : u ≤ 1) (hmL : 2 * u - 1 ≤ m) (hmU : m ≤ u)
    (hd : 0 ≤ m - r) (hdU : m - r ≤ (9 / 10) * (u - m)) :
    let κ := jointPureLambda * (p * (p + 1) * (13 / 6 : ℝ) ^ (-(p + 2 : ℝ))) * (288479 / 1588261500)
    jointPureValue p L u m r jointCanonicalMu - jointPureValue p L u m m jointCanonicalMu ≤
      (m - r) * m ^ (-p) * (jointPureMismatch p - κ * ((u - m) / m)) := by
  let d := m - r
  let g := (u - m) / m
  let e := d / m
  have hu : 0 < u := by linarith only [huL]
  have hm : 0 < m := by linarith only [huL,hmL]
  have hG : g ∈ Icc (0 : ℝ) (1 / 6) := by
    refine ⟨div_nonneg (sub_nonneg.mpr hmU) hm.le,(div_le_iff₀ hm).mpr ?_⟩
    linarith only [huL,hmL]
  have he : 0 ≤ e := div_nonneg hd hm.le
  have heU : e ≤ (9 / 10) * g := by unfold e g; rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right hdU hm.le
  rcases hd.eq_or_lt with h | h
  · have hEq := sub_eq_zero.mp h.symm
    simp [hEq]
  have hr : 0 < r := by linarith only [hdU,hmL,huL]
  obtain ⟨hI,hE⟩ := coneGap_integral_eq hp hP hL hu hm hr (sub_pos.mp h)
  obtain ⟨hGInt,hPrice⟩ := coneGapIncrement_integral_le hp hP hG
  have he₁ : (9 / 10) * g < 1 := by linarith only [hG.2]
  have hCmp := setIntegral_mono_on hI hGInt measurableSet_Ioi fun x hx => mul_le_mul_of_nonneg_left
    (coneGap_monotone_secant hG.1 he heU he₁ hx) (lineDensity_pos (zero_lt_one.trans_le hp) hx).le
  rw [hE]
  exact mul_le_mul_of_nonneg_left (hCmp.trans hPrice) (mul_nonneg hd (Real.rpow_nonneg hm.le _))

end ACS12.GammaMeasure

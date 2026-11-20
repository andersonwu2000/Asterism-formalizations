import ACS12.NativeBoseRow
import ACS12.JointMomentScaling
import ACS12.PressureCothConvex

/-! The complete original Bose row in its canonical image scale. -/
namespace ACS12.Pressure

open Set Filter MeasureTheory CenteredCircle.AllN
open GammaDeficit (lineDensity signedDensity)
open GammaMeasure (continuous_imageDensity imageDensity_eq_spectral imageDensity_pos
  imageSelf imageSelf_eq_tail imageTail_integral signedDensity_pos signedDensity_total
  pureIntegral_integrable_scale pureIntegral_scale powerTail boseMoment_integrable boseMoment_integral)
open NativeCells (boseRow analyticRow boseRow_sub_self)

noncomputable def pressureLogCountRow (p v : ℝ) : ℝ :=
  Real.exp (-p * v) * analyticRow p (Real.exp v)

theorem canonical_boseRow_eq {p N : ℝ} (hp : 0 < p) (hN : 0 < N) :
    boseRow p N = (2 / Real.pi ^ p) *
      ∫ s : ℝ in Ioi 0, GammaMeasure.imageDensity p 1 s * rowBoseBeta (s / N) := by
  let c := 2 * Real.pi
  let G (s : ℝ) := GammaMeasure.imageDensity p 1 s * rowBoseBeta (s / N)
  have hc : 0 < c := mul_pos (by norm_num) Real.pi_pos
  have hI := integral_comp_mul_right_Ioi G 0 hc
  rw [zero_mul,smul_eq_mul] at hI
  have hGI : (∫ s : ℝ in Ioi 0, G s) = c * ∫ s : ℝ in Ioi 0, G (s * c) := by
    rw [hI,← mul_assoc,mul_inv_cancel₀ hc.ne',one_mul]
  have hB : boseRow p N = ∫ s : ℝ in Ioi 0, (2 / Real.pi ^ p) * (c * G (s * c)) := by
    unfold boseRow
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    have hS : 0 < s := hs
    have hArg : (1 : ℝ) * (s * c) / (2 * Real.pi) = s := by
      unfold c
      rw [one_mul,mul_div_cancel_right₀ _ hc.ne']
    have hArg' : 1 * (s * c) / 2 = Real.pi * s := by dsimp only [c]; ring
    have hX : s * c / N = 2 * Real.pi * s / N := by dsimp only [c]; ring
    dsimp only [G]
    rw [imageDensity_eq_spectral p zero_lt_one,hArg,hArg',div_one,hX,
      Real.rpow_sub_one Real.pi_ne_zero,rowBoseBeta]
    field_simp [(Real.rpow_pos_of_pos Real.pi_pos p).ne',Real.pi_ne_zero]
    dsimp only [c]
    ring
  change boseRow p N = (2 / Real.pi ^ p) * ∫ s : ℝ in Ioi 0, G s
  rw [hB,integral_const_mul,integral_const_mul,← hGI]

private theorem pureBose_integral {p N : ℝ} (hp : 1 < p) (hN : 0 < N) :
    let f (s : ℝ) := lineDensity p s * rowBoseBeta (s / N)
    IntegrableOn f (Ioi 0) ∧ (∫ s : ℝ in Ioi 0, f s) = N ^ p * powerTail p 1 := by
  let Γ := Real.Gamma p
  let f (s : ℝ) := lineDensity p s * rowBoseBeta s
  let G (s : ℝ) := s ^ (p - 1) * (Real.exp (-s * 1) / (1 - Real.exp (-s)))
  have hp₀ := zero_lt_one.trans hp
  have hΓ : 0 < Γ := Real.Gamma_pos_of_pos hp₀
  have hGI : IntegrableOn G (Ioi 0) := by
    simpa only [G,Nat.cast_one] using boseMoment_integrable (sub_pos.mpr hp) (m := 1) (by decide)
  have hGE : (∫ s : ℝ in Ioi 0, G s) = Γ * powerTail p 1 := by
    simpa only [G,Γ,Nat.cast_one,sub_add_cancel] using
      boseMoment_integral (sub_pos.mpr hp) (m := 1) (by decide)
  have hF (s : ℝ) (hs : 0 < s) : f s = Γ⁻¹ * G s := by
    unfold f G lineDensity Γ
    rw [rowBoseBeta_eq_decay hs,mul_one,div_eq_mul_inv]
    ring
  have hI : IntegrableOn f (Ioi 0) := by
    apply (hGI.const_mul Γ⁻¹).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hF s hs).symm
  have hE : (∫ s : ℝ in Ioi 0, f s) = powerTail p 1 := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun s hs => hF s hs),integral_const_mul,hGE,
      ← mul_assoc,inv_mul_cancel₀ hΓ.ne',one_mul]
  have hN' := inv_pos.mpr hN
  have hJ := pureIntegral_integrable_scale (f := rowBoseBeta) hN' hI
  have hJE := pureIntegral_scale (p := p) hN' rowBoseBeta
  rw [show (N⁻¹) ^ (-p) = N ^ p by rw [Real.inv_rpow hN.le,Real.rpow_neg hN.le,inv_inv]] at hJE
  change _ = N ^ p * (∫ s : ℝ in Ioi 0, f s) at hJE
  rw [hE] at hJE
  simpa only [div_eq_mul_inv,mul_comm _ N⁻¹] using And.intro hJ hJE

private theorem canonicalBose_parts {p N : ℝ} (hp : 1 < p) (hp₂ : p < 2) (hN : 0 < N) :
    let T (s : ℝ) := rowBoseBeta (s / N)
    IntegrableOn (fun s => GammaMeasure.imageDensity p 1 s * T s) (Ioi 0) ∧
      IntegrableOn (fun s => signedDensity p 1 s * T s) (Ioi 0) := by
  let T (s : ℝ) := rowBoseBeta (s / N)
  let w := GammaMeasure.imageDensity p 1
  let e := signedDensity p 1
  let ρ := lineDensity p
  have hρ : IntegrableOn (fun s => ρ s * T s) (Ioi 0) := (pureBose_integral hp hN).1
  have hp₀ := zero_lt_one.trans hp
  have hMT : Measurable T := by unfold T rowBoseBeta; fun_prop
  have hMw : Measurable w := (continuous_imageDensity hp₀ zero_lt_one).measurable
  have hMρ : Measurable ρ := by unfold ρ lineDensity; fun_prop
  have hP (s : ℝ) (hs : 0 < s) : 0 ≤ T s := div_nonneg zero_le_one (expTail_den_pos (div_pos hs hN)).le
  have hA (s : ℝ) (hs : 0 < s) : 0 ≤ w s ∧ 0 ≤ e s ∧ w s ≤ ρ s ∧ e s ≤ ρ s := by
    have hw := (imageDensity_pos hp₀ zero_lt_one hs).le
    have he := (signedDensity_pos hp.le hp₂ zero_lt_one hs).le
    have hE : e s = ρ s - w s := rfl
    exact ⟨hw,he,by linarith only [hE,he],by linarith only [hE,hw]⟩
  constructor
  · apply hρ.mono' (hMw.mul hMT).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    obtain ⟨hw,_,hU,_⟩ := hA s hs
    rw [Real.norm_of_nonneg (mul_nonneg hw (hP s hs))]
    exact mul_le_mul_of_nonneg_right hU (hP s hs)
  · apply hρ.mono' ((hMρ.sub hMw).mul hMT).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    obtain ⟨_,he,_,hU⟩ := hA s hs
    change ‖e s * T s‖ ≤ ρ s * T s
    rw [Real.norm_of_nonneg (mul_nonneg he (hP s hs))]
    exact mul_le_mul_of_nonneg_right hU (hP s hs)

theorem actualRow_calibrated {p v : ℝ} (hp : 1 < p) (hp₂ : p < 2) (hv : 0 < v) :
    let G (s : ℝ) := signedDensity p 1 s * calibratedBose p s v
    IntegrableOn G (Ioi 0) ∧ pressureLogCountRow p v =
      (2 / Real.pi ^ p) * (powerTail p 1 - ∫ s : ℝ in Ioi 0, G s) := by
  let N := Real.exp v
  let T (s : ℝ) := rowBoseBeta (s / N)
  let w := GammaMeasure.imageDensity p 1
  let e := signedDensity p 1
  let G (s : ℝ) := e s * calibratedBose p s v
  have hp₀ := zero_lt_one.trans hp
  have hN : 1 < N := Real.one_lt_exp_iff.mpr hv
  have hN₀ : 0 < N := zero_lt_one.trans hN
  have hY : ∀ s : ℝ, s * Real.exp (-v) = s / N := by simp only [N,Real.exp_neg,div_eq_mul_inv,implies_true]
  obtain ⟨hW,hE⟩ := canonicalBose_parts hp hp₂ hN₀
  obtain ⟨he,heE⟩ := signedDensity_total hp.le hp₂ (L := 1) zero_lt_one
  have hG (s : ℝ) : G s = Real.exp (-p * v) * (e s * T s + (1 / 2) * e s) := by
    dsimp only [G,calibratedBose,T]
    rw [hY]
    ring
  have hA : IntegrableOn (fun s => e s * T s + (1 / 2) * e s) (Ioi 0) := hE.add (he.const_mul _)
  refine ⟨(hA.const_mul _).congr (Eventually.of_forall fun s => (hG s).symm),?_⟩
  have hSelf : boseRow p 1 = (imageSelf p 1) / Real.pi ^ p := by
    rw [canonical_boseRow_eq hp₀ zero_lt_one,imageSelf_eq_tail,imageTail_integral hp₀ zero_lt_one zero_lt_one]
    have hI : (∫ s : ℝ in Ioi 0, GammaMeasure.imageDensity p 1 s * rowBoseBeta (s / 1)) =
        ∫ s : ℝ in Ioi 0, GammaMeasure.imageTailIntegrand p 1 1 s := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      dsimp only
      rw [div_one,rowBoseBeta_eq_decay hs]
      simp only [GammaMeasure.imageTailIntegrand,mul_one]
    rw [hI]
    ring
  have hComp : (∫ s : ℝ in Ioi 0, w s * T s) =
      N ^ p * powerTail p 1 - ∫ s : ℝ in Ioi 0, e s * T s := by
    have hEq (s : ℝ) : w s * T s + e s * T s = lineDensity p s * T s := by
      unfold e w signedDensity
      ring
    have hI := setIntegral_congr_fun (μ := volume) (measurableSet_Ioi (a := (0 : ℝ))) (fun s _ => hEq s)
    rw [integral_add hW hE] at hI
    change _ = ∫ s : ℝ in Ioi 0, lineDensity p s * rowBoseBeta (s / N) at hI
    rw [(pureBose_integral hp hN₀).2] at hI
    linarith only [hI]
  have hPow : Real.exp (-p * v) * N ^ p = 1 := by
    have hNExp : N ^ p = Real.exp (p * v) := by
      dsimp only [N]
      rw [← Real.exp_mul]
      congr 1
      ring
    rw [hNExp,← Real.exp_add]
    simp only [neg_mul,neg_add_cancel,Real.exp_zero]
  change Real.exp (-p * v) * analyticRow p N = (2 / Real.pi ^ p) * (powerTail p 1 - ∫ s : ℝ in Ioi 0, G s)
  rw [← boseRow_sub_self hp₀ hN,canonical_boseRow_eq hp₀ hN₀,hSelf]
  change _ * ((2 / Real.pi ^ p) * (∫ s : ℝ in Ioi 0, w s * T s) - _) = _
  rw [hComp,setIntegral_congr_fun measurableSet_Ioi (fun s _ => hG s),integral_const_mul,
    integral_add hE (he.const_mul _),integral_const_mul,heE]
  linear_combination (2 / Real.pi ^ p) * powerTail p 1 * hPow

end ACS12.Pressure

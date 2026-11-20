import ACS12.DeficitProfile
import ACS12.GammaMixture

/-! The positive Gaussian mixture for the signed deficit profile. -/

namespace ACS12.GammaDeficit

open MeasureTheory Set Filter
open scoped ENNReal
open ACS12.GammaMixture (gammaProduct gammaProduct_probability gammaTotal
  measurable_gammaTotal gammaTotal_laplace)

private theorem integral_exp_toTime {t v : ℝ} (ht : 0 < t) (hv : 0 ≤ v) :
    (∫ q : ℝ in Ioo 0 v, Real.exp (-(t ^ 2) * q)) =
      (1 - Real.exp (-(t ^ 2) * v)) / t ^ 2 := by
  have hc : -(t ^ 2) ≠ 0 := neg_ne_zero.mpr (pow_ne_zero _ ht.ne')
  have hd (q : ℝ) : HasDerivAt (fun q => Real.exp (-(t ^ 2) * q) / (-(t ^ 2)))
      (Real.exp (-(t ^ 2) * q)) q := by
    convert (((hasDerivAt_id q).const_mul (-(t ^ 2))).exp).div_const (-(t ^ 2)) using 1
    dsimp
    field_simp [hc]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hv]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun q _ => hd q)
    (by apply Continuous.intervalIntegrable; fun_prop : IntervalIntegrable
      (fun q : ℝ => Real.exp (-(t ^ 2) * q)) volume 0 v)
  rw [h, mul_zero, Real.exp_zero]
  ring

private theorem gammaTotal_nonneg (ω : ℕ → ℝ) : 0 ≤ gammaTotal ω :=
  ENNReal.toReal_nonneg

private theorem integrable_exp_gammaTotal {p t : ℝ} (hp : 0 < p) :
    Integrable (fun ω : ℕ → ℝ => Real.exp (-(t ^ 2) * gammaTotal ω)) (gammaProduct p) := by
  letI : IsProbabilityMeasure (gammaProduct p) := gammaProduct_probability hp
  have hm : Measurable (fun ω : ℕ → ℝ => Real.exp (-(t ^ 2) * gammaTotal ω)) :=
    (((measurable_const (a := -(t ^ 2))).mul measurable_gammaTotal).exp)
  refine (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable ?_
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sq_nonneg t)) (gammaTotal_nonneg ω))

/-- The auxiliary deficit is a positive average of exponential intervals. -/
theorem deficitProfile_div_sq_eq {p t : ℝ} (hp : 0 < p) (ht : 0 < t) :
    deficitProfile p t / t ^ 2 =
      t ^ (-p) * ∫ ω : ℕ → ℝ, (∫ q : ℝ in Ioo 0 (gammaTotal ω),
        Real.exp (-(t ^ 2) * q)) ∂gammaProduct p := by
  letI : IsProbabilityMeasure (gammaProduct p) := gammaProduct_probability hp
  let f (ω : ℕ → ℝ) := Real.exp (-(t ^ 2) * gammaTotal ω)
  have hf : Integrable f (gammaProduct p) := integrable_exp_gammaTotal hp
  have hsin : 0 < 2 * Real.sinh (t / 2) :=
    mul_pos (by norm_num) (Real.sinh_pos_iff.mpr (by positivity))
  have he : t ^ (-p) * (t / (2 * Real.sinh (t / 2))) ^ p = sinhProfile p t := by
    rw [sinhProfile, Real.div_rpow ht.le hsin.le, Real.rpow_neg ht.le, Real.rpow_neg hsin.le]
    field_simp [(Real.rpow_pos_of_pos ht p).ne', (Real.rpow_pos_of_pos hsin p).ne']
  calc
    _ = (t ^ (-p) / t ^ 2) * (1 - ∫ ω : ℕ → ℝ, f ω ∂gammaProduct p) := by
      change _ = _ * (1 - ∫ ω : ℕ → ℝ, Real.exp (-(t ^ 2) * gammaTotal ω) ∂gammaProduct p)
      rw [gammaTotal_laplace hp ht, deficitProfile, ← he]
      ring
    _ = t ^ (-p) * ∫ ω : ℕ → ℝ, (1 - f ω) / t ^ 2 ∂gammaProduct p := by
      rw [integral_div, integral_sub (integrable_const (1 : ℝ)) hf, integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
      ring
    _ = _ := by
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun ω => (integral_exp_toTime ht (gammaTotal_nonneg ω)).symm

private theorem gaussian_power_integral {p t : ℝ} (hp : 0 < p) (ht : 0 < t) :
    (∫ r : ℝ in Ioi 0, (r ^ (p / 2 - 1) / Real.Gamma (p / 2)) *
      Real.exp (-(r * t ^ 2))) = t ^ (-p) := by
  have hp₂ : 0 < p / 2 := by positivity
  have ht₂ : 0 < t ^ (2 : ℕ) := by positivity
  calc
    _ = (Real.Gamma (p / 2))⁻¹ *
        ∫ r : ℝ in Ioi 0, r ^ (p / 2 - 1) * Real.exp (-(t ^ 2 * r)) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r _
      dsimp only
      ring
    _ = _ := by
      rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hp₂ ht₂,
        Real.div_rpow zero_le_one ht₂.le, Real.one_rpow, ← Real.rpow_natCast,
        ← Real.rpow_mul ht.le, show (↑(2 : ℕ) : ℝ) * (p / 2) = p by norm_num; ring,
        Real.rpow_neg ht.le]
      field_simp [(Real.Gamma_pos_of_pos hp₂).ne', (Real.rpow_pos_of_pos ht p).ne']

private abbrev MixtureSpace := (ℕ → ℝ) × (ℝ × ℝ)

private noncomputable def mixtureMeasure (p : ℝ) : Measure MixtureSpace :=
  (gammaProduct p).prod (volume.prod volume)

private noncomputable def timeGate (x : (ℕ → ℝ) × ℝ) : ℝ :=
  if 0 < x.2 ∧ x.2 < gammaTotal x.1 then 1 else 0

private noncomputable def gammaGate (p r : ℝ) : ℝ :=
  if 0 < r then r ^ (p / 2 - 1) / Real.Gamma (p / 2) else 0

private noncomputable def mixtureWeight (p : ℝ) (x : MixtureSpace) : ℝ :=
  timeGate (x.1, x.2.1) * gammaGate p x.2.2

private noncomputable def mixtureKernel (p t : ℝ) (x : MixtureSpace) : ℝ :=
  mixtureWeight p x * Real.exp (-(x.2.1 + x.2.2) * t ^ 2)

private theorem timeGate_nonneg (x : (ℕ → ℝ) × ℝ) : 0 ≤ timeGate x := by
  unfold timeGate
  split_ifs <;> norm_num

private theorem gammaGate_nonneg {p : ℝ} (hp : 0 < p) (r : ℝ) : 0 ≤ gammaGate p r := by
  unfold gammaGate
  split_ifs with hr
  · exact div_nonneg (Real.rpow_nonneg hr.le _) (Real.Gamma_pos_of_pos (by positivity)).le
  · exact le_rfl

private theorem mixtureWeight_nonneg {p : ℝ} (hp : 0 < p) (x : MixtureSpace) :
    0 ≤ mixtureWeight p x :=
  mul_nonneg (timeGate_nonneg _) (gammaGate_nonneg hp _)

private theorem measurable_timeGate : Measurable timeGate := by
  unfold timeGate
  exact Measurable.ite ((measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_lt measurable_snd (measurable_gammaTotal.comp measurable_fst)))
    measurable_const measurable_const

private theorem measurable_gammaGate (p : ℝ) : Measurable (gammaGate p) := by
  unfold gammaGate
  exact Measurable.ite measurableSet_Ioi (by fun_prop) measurable_const

private theorem measurable_mixtureWeight (p : ℝ) : Measurable (mixtureWeight p) := by
  unfold mixtureWeight
  exact (measurable_timeGate.comp (measurable_fst.prodMk measurable_snd.fst)).mul
    ((measurable_gammaGate p).comp measurable_snd.snd)

private theorem measurable_mixtureKernel (p t : ℝ) : Measurable (mixtureKernel p t) := by
  unfold mixtureKernel
  exact (measurable_mixtureWeight p).mul (by fun_prop)

private theorem lintegral_timeGate {t : ℝ} (ht : 0 < t) (ω : ℕ → ℝ) :
    (∫⁻ q : ℝ, ENNReal.ofReal (timeGate (ω, q) * Real.exp (-(t ^ 2) * q))) =
      ENNReal.ofReal ((1 - Real.exp (-(t ^ 2) * gammaTotal ω)) / t ^ 2) := by
  have hfun : (fun q : ℝ => ENNReal.ofReal (timeGate (ω, q) * Real.exp (-(t ^ 2) * q))) =
      (Ioo 0 (gammaTotal ω)).indicator (fun q => ENNReal.ofReal (Real.exp (-(t ^ 2) * q))) := by
    funext q
    by_cases h : q ∈ Ioo 0 (gammaTotal ω)
    · simp [timeGate, h.1, h.2]
    · rw [indicator_of_notMem h]
      have h' : ¬(0 < q ∧ q < gammaTotal ω) := h
      simp [timeGate, h']
  rw [hfun, lintegral_indicator measurableSet_Ioo]
  have hc : Continuous (fun q : ℝ => Real.exp (-(t ^ 2) * q)) := by fun_prop
  have hi := (hc.integrableOn_Icc (μ := volume) (a := 0) (b := gammaTotal ω)).mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => (Real.exp_pos _).le),
    integral_exp_toTime ht (gammaTotal_nonneg ω)]

private theorem lintegral_gammaGate {p t : ℝ} (hp : 0 < p) (ht : 0 < t) :
    (∫⁻ r : ℝ, ENNReal.ofReal (gammaGate p r * Real.exp (-(t ^ 2) * r))) =
      ENNReal.ofReal (t ^ (-p)) := by
  have hfun : (fun r : ℝ => ENNReal.ofReal (gammaGate p r * Real.exp (-(t ^ 2) * r))) =
      (Ioi (0 : ℝ)).indicator (fun r =>
        ENNReal.ofReal ((r ^ (p / 2 - 1) / Real.Gamma (p / 2)) * Real.exp (-(r * t ^ 2)))) := by
    funext r
    by_cases h : r ∈ Ioi (0 : ℝ)
    · change 0 < r at h
      simp only [gammaGate, if_pos h, indicator_of_mem (show r ∈ Ioi (0 : ℝ) from h)]
      rw [show -(t ^ 2) * r = -(r * t ^ 2) by ring]
    · rw [indicator_of_notMem h]
      have h' : ¬0 < r := h
      simp [gammaGate, h']
  rw [hfun, lintegral_indicator measurableSet_Ioi]
  have h := gaussian_power_integral hp ht
  have hi : IntegrableOn (fun r : ℝ => (r ^ (p / 2 - 1) / Real.Gamma (p / 2)) *
      Real.exp (-(r * t ^ 2))) (Ioi 0) :=
    Integrable.of_integral_ne_zero (h ▸ (Real.rpow_pos_of_pos ht (-p)).ne')
  have hn : ∀ᵐ r : ℝ ∂volume.restrict (Ioi 0), 0 ≤
      (r ^ (p / 2 - 1) / Real.Gamma (p / 2)) * Real.exp (-(r * t ^ 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    change 0 < r at hr
    exact mul_nonneg (div_nonneg (Real.rpow_nonneg hr.le _)
      (Real.Gamma_pos_of_pos (by positivity : 0 < p / 2)).le) (Real.exp_pos _).le
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn, h]

private theorem lintegral_mixtureKernel {p t : ℝ} (hp : 0 < p) (ht : 0 < t) :
    (∫⁻ x : MixtureSpace, ENNReal.ofReal (mixtureKernel p t x) ∂mixtureMeasure p) =
      ENNReal.ofReal (deficitProfile p t / t ^ 2) := by
  letI : IsProbabilityMeasure (gammaProduct p) := gammaProduct_probability hp
  rw [mixtureMeasure, lintegral_prod _ (measurable_mixtureKernel p t).ennreal_ofReal.aemeasurable]
  have hinner (ω : ℕ → ℝ) :
      (∫⁻ x : ℝ × ℝ, ENNReal.ofReal (mixtureKernel p t (ω, x)) ∂volume.prod volume) =
        ENNReal.ofReal ((1 - Real.exp (-(t ^ 2) * gammaTotal ω)) / t ^ 2) *
          ENNReal.ofReal (t ^ (-p)) := by
    have hfun : (fun x : ℝ × ℝ => ENNReal.ofReal (mixtureKernel p t (ω, x))) =
        fun x => ENNReal.ofReal (timeGate (ω, x.1) * Real.exp (-(t ^ 2) * x.1)) *
          ENNReal.ofReal (gammaGate p x.2 * Real.exp (-(t ^ 2) * x.2)) := by
      funext x
      rw [← ENNReal.ofReal_mul (mul_nonneg (timeGate_nonneg _) (Real.exp_pos _).le)]
      congr 1
      unfold mixtureKernel mixtureWeight
      rw [show -(x.1 + x.2) * t ^ 2 = -(t ^ 2) * x.1 + -(t ^ 2) * x.2 by ring, Real.exp_add]
      ring
    have hq : AEMeasurable (fun q : ℝ =>
        ENNReal.ofReal (timeGate (ω, q) * Real.exp (-(t ^ 2) * q))) volume :=
      (((measurable_timeGate.comp (measurable_const.prodMk measurable_id)).mul
        (by fun_prop)).ennreal_ofReal).aemeasurable
    have hr : AEMeasurable (fun r : ℝ =>
        ENNReal.ofReal (gammaGate p r * Real.exp (-(t ^ 2) * r))) volume :=
      (((measurable_gammaGate p).mul (by fun_prop)).ennreal_ofReal).aemeasurable
    calc
      _ = (∫⁻ q : ℝ, ENNReal.ofReal (timeGate (ω, q) * Real.exp (-(t ^ 2) * q))) *
          (∫⁻ r : ℝ, ENNReal.ofReal (gammaGate p r * Real.exp (-(t ^ 2) * r))) := by
        rw [hfun]
        exact lintegral_prod_mul hq hr
      _ = _ := by rw [lintegral_timeGate ht, lintegral_gammaGate hp ht]
  simp_rw [hinner]
  let f (ω : ℕ → ℝ) := (1 - Real.exp (-(t ^ 2) * gammaTotal ω)) / t ^ 2
  have hf : Integrable f (gammaProduct p) :=
    ((integrable_const (1 : ℝ)).sub (integrable_exp_gammaTotal hp (t := t))).div_const _
  have hnn (ω : ℕ → ℝ) : 0 ≤ f ω := by
    apply div_nonneg _ (sq_nonneg t)
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sq_nonneg t)) (gammaTotal_nonneg ω)))
  change (∫⁻ ω, ENNReal.ofReal (f ω) * ENNReal.ofReal (t ^ (-p)) ∂gammaProduct p) = _
  rw [lintegral_mul_const'' _ hf.aemeasurable.ennreal_ofReal,
    ← ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall hnn),
    ← ENNReal.ofReal_mul (integral_nonneg hnn), mul_comm _ (t ^ (-p)),
    deficitProfile_div_sq_eq hp ht]
  congr 2
  apply integral_congr_ae
  exact Eventually.of_forall fun ω => (integral_exp_toTime ht (gammaTotal_nonneg ω)).symm

private theorem mixtureKernel_nonneg {p : ℝ} (hp : 0 < p) (t : ℝ) (x : MixtureSpace) :
    0 ≤ mixtureKernel p t x :=
  mul_nonneg (mixtureWeight_nonneg hp _) (Real.exp_pos _).le

private theorem integral_mixtureKernel {p t : ℝ} (hp : 0 < p) (ht : 0 < t) :
    (∫ x : MixtureSpace, mixtureKernel p t x ∂mixtureMeasure p) = deficitProfile p t / t ^ 2 := by
  have hn := mixtureKernel_nonneg hp t
  have hi : Integrable (mixtureKernel p t) (mixtureMeasure p) := by
    refine ⟨(measurable_mixtureKernel p t).aestronglyMeasurable, ?_⟩
    change (∫⁻ x : MixtureSpace, ‖mixtureKernel p t x‖ₑ ∂mixtureMeasure p) < ∞
    simp_rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hn _)]
    rw [lintegral_mixtureKernel hp ht]
    exact ENNReal.ofReal_lt_top
  have h := (ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hn)).trans
    (lintegral_mixtureKernel hp ht)
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg hn)
    (div_nonneg (deficitProfile_nonneg hp ht) (sq_nonneg t))).mp h

private theorem mixtureWeight_positive_time {p : ℝ} (x : MixtureSpace)
    (h : mixtureWeight p x ≠ 0) : 0 < x.2.1 + x.2.2 := by
  have hq : 0 < x.2.1 := by
    by_contra! hq
    apply h
    simp [mixtureWeight, timeGate, not_lt.mpr hq]
  have hr : 0 < x.2.2 := by
    by_contra! hr
    apply h
    simp [mixtureWeight, gammaGate, not_lt.mpr hr]
  exact add_pos hq hr

/-- The integrated deficit sine bracket is strictly positive after the
absolute Fubini interchange over the Gamma mixture. -/
theorem integral_deficit_bracket_pos {p U : ℝ} (hp : 0 < p) (hp₂ : p < 2) (hU : 0 < U) :
    0 < ∫ t : ℝ in Ioi 0, deficitProfile p t / t ^ 2 * sineBracket U t := by
  letI : IsProbabilityMeasure (gammaProduct p) := gammaProduct_probability hp
  letI : SFinite (mixtureMeasure p) := by unfold mixtureMeasure; infer_instance
  let ν := volume.restrict (Ioi (0 : ℝ))
  let F (z : MixtureSpace × ℝ) := mixtureKernel p z.2 z.1 * sineBracket U z.2
  have hm : Measurable F := by
    unfold F mixtureKernel sineBracket
    exact (((measurable_mixtureWeight p).comp measurable_fst).mul (by fun_prop)).mul
      (by fun_prop)
  have hI : Integrable F ((mixtureMeasure p).prod ν) := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    change (∫⁻ z, ‖F z‖ₑ ∂(mixtureMeasure p).prod ν) < ∞
    rw [lintegral_prod_symm _ hm.enorm.aemeasurable]
    have hfun : ∀ᵐ t ∂ν, (∫⁻ x : MixtureSpace, ‖F (x, t)‖ₑ ∂mixtureMeasure p) =
        ‖deficitProfile p t / t ^ 2 * sineBracket U t‖ₑ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      change 0 < t at ht
      have he (x : MixtureSpace) : ‖F (x, t)‖ₑ =
          ENNReal.ofReal |sineBracket U t| * ENNReal.ofReal (mixtureKernel p t x) := by
        simp only [F, Real.enorm_eq_ofReal_abs, abs_mul,
          abs_of_nonneg (mixtureKernel_nonneg hp t x), ENNReal.ofReal_mul (mixtureKernel_nonneg hp t x)]
        rw [mul_comm]
      simp_rw [he]
      rw [lintegral_const_mul _ (measurable_mixtureKernel p t).ennreal_ofReal,
        lintegral_mixtureKernel hp ht, ← ENNReal.ofReal_mul (abs_nonneg _), Real.enorm_eq_ofReal_abs,
        abs_mul, abs_of_nonneg (div_nonneg (deficitProfile_nonneg hp ht) (sq_nonneg t)), mul_comm]
    rw [lintegral_congr_ae hfun]
    exact (integrable_deficit_bracket hp hp₂ hU).hasFiniteIntegral
  have hrow : ∀ᵐ t ∂ν,
      (∫ x : MixtureSpace, F (x, t) ∂mixtureMeasure p) =
        deficitProfile p t / t ^ 2 * sineBracket U t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    change (∫ x : MixtureSpace, mixtureKernel p t x * sineBracket U t ∂mixtureMeasure p) = _
    rw [integral_mul_const, integral_mixtureKernel hp ht]
  have hswap : (∫ t : ℝ in Ioi 0, deficitProfile p t / t ^ 2 * sineBracket U t) =
      ∫ x : MixtureSpace, (∫ t : ℝ, F (x, t) ∂ν) ∂mixtureMeasure p := by
    calc
      _ = ∫ t : ℝ, (∫ x : MixtureSpace, F (x, t) ∂mixtureMeasure p) ∂ν :=
        integral_congr_ae (hrow.mono fun _ h => h.symm)
      _ = ∫ z, F z ∂(mixtureMeasure p).prod ν := (integral_prod_symm F hI).symm
      _ = _ := integral_prod F hI
  let G (x : MixtureSpace) := ∫ t : ℝ, F (x, t) ∂ν
  have hG (x : MixtureSpace) : G x = mixtureWeight p x *
      ∫ t : ℝ in Ioi 0, Real.exp (-(x.2.1 + x.2.2) * t ^ 2) * sineBracket U t := by
    unfold G F mixtureKernel
    simp_rw [mul_assoc]
    exact integral_const_mul _ _
  have hGpos (x : MixtureSpace) (hw : mixtureWeight p x ≠ 0) : 0 < G x := by
    rw [hG]
    exact mul_pos (lt_of_le_of_ne (mixtureWeight_nonneg hp x) (Ne.symm hw))
      (GaussianSine.integral_sine_bracket_pos (mixtureWeight_positive_time x hw) hU)
  have hsupp : Function.support G =
      Function.support (fun x : MixtureSpace => ENNReal.ofReal (mixtureKernel p 1 x)) := by
    ext x
    by_cases hw : mixtureWeight p x = 0
    · simp [hG, mixtureKernel, hw, Function.mem_support]
    · have h := hGpos x hw
      have h' : 0 < mixtureKernel p 1 x :=
        mul_pos (lt_of_le_of_ne (mixtureWeight_nonneg hp x) (Ne.symm hw)) (Real.exp_pos _)
      simp [Function.mem_support, h.ne', (ENNReal.ofReal_pos.mpr h').ne']
  have hDeficit : 0 < deficitProfile p 1 := by
    have hSinh : (1 : ℝ) < 2 * Real.sinh (1 / 2) := by
      linarith [Real.self_lt_sinh_iff.mpr (by norm_num : 0 < (1 : ℝ) / 2)]
    exact sub_pos.mpr (Real.rpow_lt_rpow_of_neg zero_lt_one hSinh (neg_neg_of_pos hp))
  have hSupport : 0 < mixtureMeasure p
      (Function.support (fun x : MixtureSpace => ENNReal.ofReal (mixtureKernel p 1 x))) := by
    apply (lintegral_pos_iff_support (measurable_mixtureKernel p 1).ennreal_ofReal).mp
    rw [lintegral_mixtureKernel hp zero_lt_one]
    simpa using ENNReal.ofReal_pos.mpr hDeficit
  rw [hswap]
  change 0 < ∫ x : MixtureSpace, G x ∂mixtureMeasure p
  have hGnn (x : MixtureSpace) : 0 ≤ G x := by
    by_cases hw : mixtureWeight p x = 0
    · simp [hG, hw]
    · exact (hGpos x hw).le
  have hGi : Integrable G (mixtureMeasure p) := hI.integral_prod_left
  apply (integral_pos_iff_support_of_nonneg_ae (Eventually.of_forall hGnn) hGi).mpr
  rw [hsupp]
  exact hSupport

end ACS12.GammaDeficit

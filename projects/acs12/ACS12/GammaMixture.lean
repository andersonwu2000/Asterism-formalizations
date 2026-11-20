import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.NumberTheory.ZetaValues

/-! The product of Gamma laws used for the positive Gaussian mixture. -/

namespace ACS12.GammaMixture

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal BigOperators

private theorem measurable_gammaPDF (a r : ℝ) : Measurable (gammaPDF a r) :=
  (measurable_gammaPDFReal a r).ennreal_ofReal

private theorem ae_pos_gammaMeasure {a r : ℝ} :
    ∀ᵐ x : ℝ ∂gammaMeasure a r, 0 < x := by
  unfold gammaMeasure
  apply (ae_withDensity_iff (measurable_gammaPDF a r)).mpr
  have hn : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [hn] with x hx hpdf
  by_contra! h
  exact hpdf (gammaPDF_of_neg (lt_of_le_of_ne h hx))

private theorem integral_gammaMeasure_eq {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (f : ℝ → ℝ) :
    (∫ x : ℝ, f x ∂gammaMeasure a r) =
      ∫ x : ℝ in Ioi 0, (r ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-(r * x))) * f x := by
  unfold gammaMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_gammaPDF a r)
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top) f,
    ← integral_Ici_eq_integral_Ioi, ← integral_indicator measurableSet_Ici]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x), smul_eq_mul]
    by_cases h : 0 ≤ x
    · simp [gammaPDFReal, h, indicator_of_mem]
    · simp [gammaPDFReal, h, indicator_of_notMem]

private theorem integral_gammaMeasure_id {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (∫ x : ℝ, x ∂gammaMeasure a r) = a / r := by
  rw [integral_gammaMeasure_eq ha hr]
  calc
    _ = ∫ x : ℝ in Ioi 0, (r ^ a / Real.Gamma a) * (x ^ a * Real.exp (-(r * x))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change 0 < x at hx
      dsimp only
      rw [show x ^ a = x ^ (a - 1) * x by
        rw [← Real.rpow_add_one hx.ne', sub_add_cancel]]
      ring
    _ = _ := by
      have hi := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := a + 1) (r := r)
        (by positivity) hr
      rw [add_sub_cancel_right] at hi
      rw [integral_const_mul, hi, Real.Gamma_add_one ha.ne',
        Real.div_rpow zero_le_one hr.le, Real.one_rpow, Real.rpow_add_one hr.ne']
      field_simp [(Real.Gamma_pos_of_pos ha).ne', (Real.rpow_pos_of_pos hr a).ne', hr.ne']

private theorem lintegral_gammaMeasure_id {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (∫⁻ x : ℝ, ENNReal.ofReal x ∂gammaMeasure a r) = ENNReal.ofReal (a / r) := by
  have h := integral_gammaMeasure_id ha hr
  have hi : Integrable (fun x : ℝ => x) (gammaMeasure a r) :=
    Integrable.of_integral_ne_zero (h ▸ (div_pos ha hr).ne')
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_pos_gammaMeasure.mono fun _ hx => hx.le), h]

private theorem integral_gammaMeasure_exp {a r c : ℝ} (ha : 0 < a) (hr : 0 < r) (hc : 0 ≤ c) :
    (∫ x : ℝ, Real.exp (-c * x) ∂gammaMeasure a r) = (r / (r + c)) ^ a := by
  have hrc : 0 < r + c := add_pos_of_pos_of_nonneg hr hc
  rw [integral_gammaMeasure_eq ha hr]
  calc
    _ = ∫ x : ℝ in Ioi 0, (r ^ a / Real.Gamma a) *
        (x ^ (a - 1) * Real.exp (-((r + c) * x))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      dsimp only
      rw [mul_assoc, mul_assoc, ← Real.exp_add,
        show -(r * x) + -c * x = -((r + c) * x) by ring]
    _ = _ := by
      rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi ha hrc,
        Real.div_rpow zero_le_one hrc.le, Real.one_rpow, Real.div_rpow hr.le hrc.le]
      field_simp [(Real.Gamma_pos_of_pos ha).ne', (Real.rpow_pos_of_pos hrc a).ne']

noncomputable def gammaRate (n : ℕ) : ℝ := (2 * Real.pi) ^ 2 * ((n : ℝ) + 1) ^ 2

theorem gammaRate_pos (n : ℕ) : 0 < gammaRate n := by
  unfold gammaRate
  positivity

private theorem summable_gamma_mean (a : ℝ) :
    Summable (fun n : ℕ => a / gammaRate n) := by
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℕ)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hn : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (2 : ℕ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hs
  convert hn.mul_left (a / (2 * Real.pi) ^ (2 : ℕ)) using 1
  funext n
  unfold gammaRate
  field_simp [Real.pi_ne_zero, show (n : ℝ) + 1 ≠ 0 by positivity]

noncomputable def gammaProduct (a : ℝ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun n : ℕ => gammaMeasure a (gammaRate n))

theorem gammaProduct_probability {a : ℝ} (ha : 0 < a) :
    IsProbabilityMeasure (gammaProduct a) := by
  letI : ∀ n : ℕ, IsProbabilityMeasure (gammaMeasure a (gammaRate n)) :=
    fun n => isProbabilityMeasure_gammaMeasure ha (gammaRate_pos n)
  unfold gammaProduct
  infer_instance

theorem gammaProduct_coordinate {a : ℝ} (ha : 0 < a) (n : ℕ) :
    MeasurePreserving (fun ω : ℕ → ℝ => ω n) (gammaProduct a) (gammaMeasure a (gammaRate n)) := by
  letI : ∀ n : ℕ, IsProbabilityMeasure (gammaMeasure a (gammaRate n)) :=
    fun n => isProbabilityMeasure_gammaMeasure ha (gammaRate_pos n)
  exact measurePreserving_eval_infinitePi (fun n : ℕ => gammaMeasure a (gammaRate n)) n

noncomputable def gammaTotal (ω : ℕ → ℝ) : ℝ :=
  (∑' n, ENNReal.ofReal (ω n)).toReal

theorem measurable_gammaTotal : Measurable gammaTotal :=
  (Measurable.ennreal_tsum fun n =>
    (measurable_pi_apply n : Measurable (fun ω : ℕ → ℝ => ω n)).ennreal_ofReal).ennreal_toReal

private theorem gammaProduct_total_ne_top {a : ℝ} (ha : 0 < a) :
    (∫⁻ ω : ℕ → ℝ, ∑' n : ℕ, ENNReal.ofReal (ω n) ∂gammaProduct a) ≠ ∞ := by
  have hm (n : ℕ) : Measurable (fun ω : ℕ → ℝ => ENNReal.ofReal (ω n)) :=
    (measurable_pi_apply n).ennreal_ofReal
  have hi (n : ℕ) :
      (∫⁻ ω, ENNReal.ofReal (ω n) ∂gammaProduct a) =
        ENNReal.ofReal (a / gammaRate n) := by
    calc
      _ = ∫⁻ x : ℝ, ENNReal.ofReal x ∂gammaMeasure a (gammaRate n) :=
        (gammaProduct_coordinate ha n).lintegral_comp (by fun_prop)
      _ = _ := lintegral_gammaMeasure_id ha (gammaRate_pos n)
  rw [lintegral_tsum (fun n => (hm n).aemeasurable)]
  simp_rw [hi]
  exact (summable_gamma_mean a).tsum_ofReal_ne_top

private theorem gammaProduct_ae_finite {a : ℝ} (ha : 0 < a) :
    ∀ᵐ ω ∂gammaProduct a, (∑' n : ℕ, ENNReal.ofReal (ω n)) < ∞ :=
  ae_lt_top (Measurable.ennreal_tsum fun n =>
    (measurable_pi_apply n : Measurable (fun ω : ℕ → ℝ => ω n)).ennreal_ofReal)
    (gammaProduct_total_ne_top ha)

theorem integrable_gammaTotal {a : ℝ} (ha : 0 < a) :
    Integrable gammaTotal (gammaProduct a) :=
  integrable_toReal_of_lintegral_ne_top
    (Measurable.ennreal_tsum fun n =>
      (measurable_pi_apply n : Measurable (fun ω : ℕ → ℝ => ω n)).ennreal_ofReal).aemeasurable
    (gammaProduct_total_ne_top ha)

theorem gammaTotal_integral {a : ℝ} (ha : 0 < a) :
    (∫ ω, gammaTotal ω ∂gammaProduct a) = a / 24 := by
  let μ := gammaProduct a
  let f (ω : ℕ → ℝ) (n : ℕ) := ENNReal.ofReal (ω n)
  have hNN : ∀ᵐ ω ∂μ, 0 ≤ gammaTotal ω :=
    Eventually.of_forall fun _ => ENNReal.toReal_nonneg
  have hI := ofReal_integral_eq_lintegral_ofReal (integrable_gammaTotal ha) hNN
  have hE : (fun ω => ENNReal.ofReal (gammaTotal ω)) =ᵐ[μ] fun ω => ∑' n, f ω n := by
    filter_upwards [gammaProduct_ae_finite ha] with ω hω
    exact ENNReal.ofReal_toReal hω.ne
  have hm (n : ℕ) : Measurable (fun ω => f ω n) :=
    (measurable_pi_apply n : Measurable (fun ω : ℕ → ℝ => ω n)).ennreal_ofReal
  have hG (n : ℕ) : (∫⁻ ω, f ω n ∂μ) = ENNReal.ofReal (a / gammaRate n) := by
    calc
      _ = ∫⁻ x : ℝ, ENNReal.ofReal x ∂gammaMeasure a (gammaRate n) :=
        (gammaProduct_coordinate ha n).lintegral_comp (by fun_prop)
      _ = _ := lintegral_gammaMeasure_id ha (gammaRate_pos n)
  rw [lintegral_congr_ae hE,lintegral_tsum (fun n => (hm n).aemeasurable)] at hI
  simp_rw [hG] at hI
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => (div_pos ha (gammaRate_pos n)).le) (summable_gamma_mean a)] at hI
  have hSum : (∑' n, a / gammaRate n) = a / 24 := by
    have hZ := hasSum_zeta_two.summable.tsum_eq_zero_add
    simp only [Nat.cast_zero,Nat.cast_add,Nat.cast_one] at hZ
    rw [show (1 : ℝ) / (0 : ℝ) ^ (2 : ℕ) = 0 by norm_num,zero_add] at hZ
    have hM (n : ℕ) : a / gammaRate n = (a / (2 * Real.pi) ^ (2 : ℕ)) *
        (1 / ((n : ℝ) + 1) ^ (2 : ℕ)) := by
      unfold gammaRate
      field_simp [Real.pi_ne_zero,(show 0 < (n : ℝ) + 1 by positivity).ne']
    simp_rw [hM,tsum_mul_left]
    rw [← hZ,hasSum_zeta_two.tsum_eq]
    field_simp [Real.pi_ne_zero]
    ring
  rw [hSum] at hI
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg_of_ae hNN) (by positivity)).mp hI

private theorem gammaProduct_ae_coordinate_pos {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ∀ᵐ ω ∂gammaProduct a, 0 < ω n := by
  have h := gammaProduct_coordinate ha n
  have hp : ∀ᵐ x : ℝ ∂(gammaProduct a).map (fun ω : ℕ → ℝ => ω n), 0 < x := by
    rw [h.map_eq]
    exact ae_pos_gammaMeasure
  exact (ae_map_iff h.measurable.aemeasurable measurableSet_Ioi).mp hp

theorem gammaProduct_ae_total_pos {a : ℝ} (ha : 0 < a) :
    ∀ᵐ ω ∂gammaProduct a, 0 < gammaTotal ω := by
  filter_upwards [gammaProduct_ae_finite ha, gammaProduct_ae_coordinate_pos ha 0] with ω hω h0
  have h := (ENNReal.ofReal_pos.mpr h0).trans_le
    (ENNReal.le_tsum (f := fun n : ℕ => ENNReal.ofReal (ω n)) 0)
  exact ENNReal.toReal_pos h.ne' hω.ne

theorem gammaProduct_ae_hasSum {a : ℝ} (ha : 0 < a) :
    ∀ᵐ ω ∂gammaProduct a, HasSum ω (gammaTotal ω) := by
  filter_upwards [gammaProduct_ae_finite ha,
    (eventually_countable_forall.mpr (gammaProduct_ae_coordinate_pos ha))] with ω hω hp
  have h := ENNReal.hasSum_toReal hω.ne
  rw [gammaTotal, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  simpa only [ENNReal.toReal_ofReal (hp _).le] using h

private theorem tendsto_sinh_product {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n : ℕ => ∏ j ∈ Finset.range n, (1 + t ^ 2 / gammaRate j))
      atTop (𝓝 (2 * Real.sinh (t / 2) / t)) := by
  let z := ((t / (2 * Real.pi) : ℝ) : ℂ) * Complex.I
  have hz : (Real.pi : ℂ) * z = ((t / 2 : ℝ) : ℂ) * Complex.I := by
    dsimp [z]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  have hz₀ : (Real.pi : ℂ) * z ≠ 0 := by
    rw [hz]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity : (t / 2) ≠ 0)) Complex.I_ne_zero
  have hfac (j : ℕ) : (1 : ℂ) - z ^ 2 / ((j : ℂ) + 1) ^ 2 =
      ((1 + t ^ 2 / gammaRate j : ℝ) : ℂ) := by
    unfold gammaRate
    dsimp [z]
    push_cast
    rw [mul_pow, Complex.I_sq]
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero,
      show (j : ℂ) + 1 ≠ 0 by exact_mod_cast (by positivity : (j : ℝ) + 1 ≠ 0)]
    ring
  have hs : Complex.sin ((Real.pi : ℂ) * z) / ((Real.pi : ℂ) * z) =
      ((2 * Real.sinh (t / 2) / t : ℝ) : ℂ) := by
    rw [hz, Complex.sin_mul_I, ← Complex.ofReal_sinh, mul_div_mul_right _ _ Complex.I_ne_zero]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr ht.ne']
  have hc := (Complex.tendsto_euler_sin_prod z).div_const ((Real.pi : ℂ) * z)
  rw [hs] at hc
  have hlim := (Complex.continuous_re.tendsto _).comp hc
  simp only [Complex.ofReal_re] at hlim
  convert hlim using 1
  funext n
  dsimp only [Function.comp_apply]
  rw [mul_div_cancel_left₀ _ hz₀]
  simp_rw [hfac]
  rw [← Complex.ofReal_prod, Complex.ofReal_re]

private theorem integral_finite_gamma_product {a : ℝ} (ha : 0 < a) (t : ℝ) (n : ℕ) :
    (∫ ω : ℕ → ℝ, Real.exp (-(t ^ 2) * (∑ j ∈ Finset.range n, ω j)) ∂gammaProduct a) =
      ∏ j ∈ Finset.range n, (gammaRate j / (gammaRate j + t ^ 2)) ^ a := by
  letI : ∀ j : ℕ, IsProbabilityMeasure (gammaMeasure a (gammaRate j)) :=
    fun j => isProbabilityMeasure_gammaMeasure ha (gammaRate_pos j)
  have hInd : iIndepFun (fun j (ω : ℕ → ℝ) => Real.exp (-(t ^ 2) * ω j)) (gammaProduct a) :=
    iIndepFun_infinitePi (P := fun j : ℕ => gammaMeasure a (gammaRate j))
      (X := fun (_ : ℕ) (x : ℝ) => Real.exp (-(t ^ 2) * x)) (fun _ => by fun_prop)
  have hfin := (hInd.restrict (Finset.range n)).integral_fun_prod_eq_prod_integral
    (fun j => by
      change AEStronglyMeasurable (fun ω : ℕ → ℝ => Real.exp (-(t ^ 2) * ω j)) (gammaProduct a)
      exact (by fun_prop : Measurable (fun ω : ℕ → ℝ =>
        Real.exp (-(t ^ 2) * ω j))).aestronglyMeasurable)
  have hfactor (j : ℕ) :
      (∫ ω : ℕ → ℝ, Real.exp (-(t ^ 2) * ω j) ∂gammaProduct a) =
        (gammaRate j / (gammaRate j + t ^ 2)) ^ a := by
    have h := gammaProduct_coordinate ha j
    have hm : Continuous (fun x : ℝ => Real.exp (-(t ^ 2) * x)) := by fun_prop
    have he := integral_map (μ := gammaProduct a) h.measurable.aemeasurable
      (f := fun x : ℝ => Real.exp (-(t ^ 2) * x)) hm.aestronglyMeasurable
    rw [h.map_eq] at he
    exact he.symm.trans (integral_gammaMeasure_exp ha (gammaRate_pos j) (sq_nonneg t))
  calc
    _ = ∫ ω : ℕ → ℝ, ∏ j ∈ Finset.range n, Real.exp (-(t ^ 2) * ω j) ∂gammaProduct a := by
      simp_rw [Finset.mul_sum, Real.exp_sum]
    _ = ∏ j ∈ Finset.range n, ∫ ω : ℕ → ℝ, Real.exp (-(t ^ 2) * ω j) ∂gammaProduct a := by
      have hl (ω : ℕ → ℝ) :
          (∏ j : Finset.range n, Real.exp (-(t ^ 2) * ω j)) =
            ∏ j ∈ Finset.range n, Real.exp (-(t ^ 2) * ω j) :=
        Finset.prod_coe_sort (Finset.range n) (fun j : ℕ => Real.exp (-(t ^ 2) * ω j))
      have hr :
          (∏ j : Finset.range n, ∫ ω : ℕ → ℝ, Real.exp (-(t ^ 2) * ω j) ∂gammaProduct a) =
            ∏ j ∈ Finset.range n, ∫ ω : ℕ → ℝ, Real.exp (-(t ^ 2) * ω j) ∂gammaProduct a :=
        Finset.prod_coe_sort (Finset.range n) (fun j : ℕ =>
          ∫ ω : ℕ → ℝ, Real.exp (-(t ^ 2) * ω j) ∂gammaProduct a)
      simp only [Finset.restrict] at hfin
      simp_rw [hl, hr] at hfin
      exact hfin
    _ = _ := by simp_rw [hfactor]

/-- The exact Gaussian transform of the summed independent Gamma variables. -/
theorem gammaTotal_laplace {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    (∫ ω : ℕ → ℝ, Real.exp (-(t ^ 2) * gammaTotal ω) ∂gammaProduct a) =
      (t / (2 * Real.sinh (t / 2))) ^ a := by
  letI : IsProbabilityMeasure (gammaProduct a) := gammaProduct_probability ha
  let F (n : ℕ) (ω : ℕ → ℝ) := Real.exp (-(t ^ 2) * (∑ j ∈ Finset.range n, ω j))
  have hlim : Tendsto (fun n => ∫ ω, F n ω ∂gammaProduct a) atTop
      (𝓝 (∫ ω : ℕ → ℝ, Real.exp (-(t ^ 2) * gammaTotal ω) ∂gammaProduct a)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : ℕ → ℝ => (1 : ℝ))
    · intro n
      exact (by unfold F; fun_prop : Measurable (F n)).aestronglyMeasurable
    · exact integrable_const 1
    · intro n
      filter_upwards [eventually_countable_forall.mpr (gammaProduct_ae_coordinate_pos ha)]
        with ω hω
      change ‖Real.exp (-(t ^ 2) * ∑ j ∈ Finset.range n, ω j)‖ ≤ 1
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg t))
        (Finset.sum_nonneg fun j _ => (hω j).le))
    · filter_upwards [gammaProduct_ae_hasSum ha] with ω hω
      exact (Real.continuous_exp.tendsto _).comp (hω.tendsto_sum_nat.const_mul (-(t ^ 2)))
  have hterm (n : ℕ) :
      (∫ ω, F n ω ∂gammaProduct a) = (∏ j ∈ Finset.range n, (1 + t ^ 2 / gammaRate j)) ^ (-a) := by
    rw [integral_finite_gamma_product ha t n,
      ← Real.finsetProd_rpow _ _ (fun j _ => by have hj := gammaRate_pos j; positivity) (-a)]
    apply Finset.prod_congr rfl
    intro j _
    have hr := gammaRate_pos j
    rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity)]
    congr 1
    field_simp [hr.ne', (add_pos_of_pos_of_nonneg hr (sq_nonneg t)).ne']
  have hs : 0 < Real.sinh (t / 2) := Real.sinh_pos_iff.mpr (by positivity)
  have hpow := (tendsto_sinh_product ht).rpow_const (p := -a) (Or.inl (by positivity))
  have h := tendsto_nhds_unique (hlim.congr hterm) hpow
  rw [h, Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity)]
  congr 1
  field_simp [ht.ne', hs.ne']

end ACS12.GammaMixture

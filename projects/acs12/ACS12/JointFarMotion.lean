import ACS12.JointFarEnvelopes

/-! Ordinary exponent motion of the exact far native envelope. -/
namespace ACS12.GammaMeasure

open Set MeasureTheory Filter
open scoped Topology

noncomputable def farPowerJet (k : ℕ) (x p : ℝ) : ℝ := (-Real.log x) ^ k * x ^ (-p)

theorem farPowerJet_deriv {x p : ℝ} (hx : 0 < x) (k : ℕ) :
    HasDerivAt (farPowerJet k x) (farPowerJet (k + 1) x p) p := by
  have h := (((hasDerivAt_id p).const_mul (-Real.log x)).exp).const_mul ((-Real.log x) ^ k)
  convert h using 1
  · funext q
    unfold farPowerJet
    rw [Real.rpow_def_of_pos hx,show Real.log x * -q = -Real.log x * q by ring]
    rfl
  · unfold farPowerJet
    rw [pow_succ,Real.rpow_def_of_pos hx,show Real.log x * -p = -Real.log x * p by ring]
    simp only [id_eq,mul_one]
    ring

noncomputable def farPolyPower (a b c x p : ℝ) : ℝ :=
  (a * p ^ 2 + b * p + c) * x ^ (-p)

noncomputable def farPolyPowerD (a b c x p : ℝ) : ℝ :=
  (2 * a * p + b - Real.log x * (a * p ^ 2 + b * p + c)) * x ^ (-p)

noncomputable def farPolyPowerDD (a b c x p : ℝ) : ℝ :=
  (2 * a - 2 * Real.log x * (2 * a * p + b) +
    (Real.log x) ^ 2 * (a * p ^ 2 + b * p + c)) * x ^ (-p)

theorem farPolyPower_deriv (a b c : ℝ) {x p : ℝ} (hx : 0 < x) :
    HasDerivAt (farPolyPower a b c x) (farPolyPowerD a b c x p) p := by
  have h := hasDerivAt_id p
  have hP := (((h.pow 2).const_mul a).add (h.const_mul b)).add_const c
  have hF := farPowerJet_deriv (p := p) hx 0
  unfold farPowerJet at hF
  simp only [pow_zero,one_mul,zero_add,pow_one] at hF
  convert hP.mul hF using 1
  unfold farPolyPowerD
  simp only [Pi.add_apply,Pi.sub_apply,Pi.pow_apply,id_eq,mul_one]
  ring

theorem farPolyPowerD_deriv (a b c : ℝ) {x p : ℝ} (hx : 0 < x) :
    HasDerivAt (farPolyPowerD a b c x) (farPolyPowerDD a b c x p) p := by
  have h := hasDerivAt_id p
  have hP := (((h.pow 2).const_mul a).add (h.const_mul b)).add_const c
  have hD := ((h.const_mul (2 * a)).add_const b).sub (hP.const_mul (Real.log x))
  have hF := farPowerJet_deriv (p := p) hx 0
  unfold farPowerJet at hF
  simp only [pow_zero,one_mul,zero_add,pow_one] at hF
  convert hD.mul hF using 1
  unfold farPolyPowerDD
  simp only [Pi.add_apply,Pi.sub_apply,Pi.pow_apply,id_eq,mul_one]
  ring

noncomputable def farIntegralJet (k : ℕ) (p : ℝ) : ℝ :=
  ∫ x : ℝ in Ioc (13 / 8 : ℝ) (21 / 8), farPowerJet k x p

theorem farIntegralJet_deriv {p : ℝ} (hp : 0 < p) (k : ℕ) :
    HasDerivAt (farIntegralJet k) (farIntegralJet (k + 1) p) p := by
  let μ := volume.restrict (Ioc (13 / 8 : ℝ) (21 / 8))
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (by simp)
  have hMeas (j : ℕ) (q : ℝ) : Measurable (fun x => farPowerJet j x q) := by
    unfold farPowerJet
    fun_prop
  have hAE : ∀ᵐ x ∂μ, x ∈ Ioc (13 / 8 : ℝ) (21 / 8) := ae_restrict_mem measurableSet_Ioc
  have hBound (j : ℕ) (q : ℝ) (hq : 0 < q) (x : ℝ) (hx : x ∈ Ioc (13 / 8 : ℝ) (21 / 8)) :
      ‖farPowerJet j x q‖ ≤ 1 := by
    have hx₁ : 1 < x := (by norm_num : (1 : ℝ) < 13 / 8).trans hx.1
    have hx₀ := zero_lt_one.trans hx₁
    have hL : Real.log x ≤ 1 := by
      have h := Real.log_le_log hx₀ (show x ≤ 21 / 8 from hx.2)
      have he : (21 / 8 : ℝ) < Real.exp 1 := by
        have hE := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num) 4
        norm_num [Finset.sum_range_succ] at hE
        linarith only [hE]
      exact h.trans ((Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 21 / 8)).mpr he).le
    have hPow : x ^ (-q) ≤ 1 := by
      simpa only [Real.rpow_zero] using (Real.rpow_le_rpow_left_iff hx₁).mpr (neg_nonpos.mpr hq.le)
    unfold farPowerJet
    rw [norm_mul,norm_pow,Real.norm_eq_abs,abs_neg,abs_of_nonneg (Real.log_nonneg hx₁.le),
      Real.norm_of_nonneg (Real.rpow_nonneg hx₀.le _)]
    exact mul_le_one₀ (pow_le_one₀ (Real.log_nonneg hx₁.le) hL) (Real.rpow_nonneg hx₀.le _) hPow
  have hInt : Integrable (fun x => farPowerJet k x p) μ :=
    (integrable_const (1 : ℝ)).mono' (hMeas k p).aestronglyMeasurable
      (hAE.mono fun x hx => hBound k p hp x hx)
  have hDom : ∀ᵐ x ∂μ, ∀ q ∈ Ioi (0 : ℝ), ‖farPowerJet (k + 1) x q‖ ≤ 1 :=
    hAE.mono fun x hx q hq => hBound (k + 1) q hq x hx
  have hD : ∀ᵐ x ∂μ, ∀ q ∈ Ioi (0 : ℝ),
      HasDerivAt (fun p => farPowerJet k x p) (farPowerJet (k + 1) x q) q :=
    hAE.mono fun x hx q _ => farPowerJet_deriv ((by norm_num : (0 : ℝ) < 13 / 8).trans hx.1) k
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (Ioi_mem_nhds hp)
    (Eventually.of_forall fun q => (hMeas k q).aestronglyMeasurable) hInt
    (hMeas (k + 1) p).aestronglyMeasurable hDom (integrable_const (1 : ℝ)) hD).2

theorem farIntegralJet_zero (p : ℝ) :
    farIntegralJet 0 p = ∫ x : ℝ in (13 / 8 : ℝ)..(21 / 8), x ^ (-p) := by
  rw [intervalIntegral.integral_of_le (by norm_num)]
  simp only [farIntegralJet,farPowerJet,pow_zero,one_mul]

end ACS12.GammaMeasure

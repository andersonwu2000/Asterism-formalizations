import ACS12.GammaDeficitDerivative
import ACS12.PressureHalfPath
import ACS12.BoseMoments
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! The ordinary fractional-deficit integral reduced by the exact hyperbolic recurrence. -/
namespace ACS12.GammaDeficit

open Set Filter MeasureTheory
open scoped Topology

private theorem sinh_gap_le_cube {z : ℝ} (hz : 0 ≤ z) (hZ : z ≤ 1) :
    Real.sinh z - z ≤ z ^ 3 * (Real.sinh 1 - 1) := by
  have hS (x : ℝ) : HasSum (fun k : ℕ => x ^ (2 * (k + 1) + 1) / ((2 * (k + 1) + 1).factorial : ℝ))
      (Real.sinh x - x) := by
    simpa only [Finset.sum_range_one,Nat.mul_zero,zero_add,pow_one,Nat.factorial_one,Nat.cast_one,div_one]
      using (hasSum_nat_add_iff' 1).mpr (Real.hasSum_sinh x)
  have h := (hS z).summable.tsum_le_tsum (fun k => show _ ≤
      z ^ 3 * ((1 : ℝ) ^ (2 * (k + 1) + 1) / ((2 * (k + 1) + 1).factorial : ℝ)) from by
      rw [one_pow]
      have hPow := pow_le_pow_of_le_one hz hZ (show 3 ≤ 2 * (k + 1) + 1 by omega)
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right hPow (by positivity)) ((hS 1).mul_left (z ^ 3)).summable
  rwa [(hS z).tsum_eq,((hS 1).mul_left (z ^ 3)).tsum_eq] at h

private theorem rpow_negative_gap_le {a x y : ℝ} (ha : 0 < a) (hx : 0 < x) (hxy : x ≤ y) :
    x ^ (-a) - y ^ (-a) ≤ a * (y - x) * x ^ (-a - 1) := by
  rcases hxy.eq_or_lt with rfl | h
  · simp
  let f (t : ℝ) := t ^ (-a)
  have hD (t : ℝ) (ht : 0 < t) : HasDerivAt f (-a * t ^ (-a - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl ht.ne')
  obtain ⟨c,hc,hE⟩ := exists_deriv_eq_slope f h
    (fun t ht => (hD t (hx.trans_le ht.1)).continuousAt.continuousWithinAt)
    (fun t ht => (hD t (hx.trans ht.1)).differentiableAt.differentiableWithinAt)
  rw [(hD c (hx.trans hc.1)).deriv] at hE
  have hF := (eq_div_iff (sub_pos.mpr h).ne').mp hE
  have hExp : -a - 1 ≤ 0 := by linarith only [ha]
  have hG := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hx hc.1.le hExp) (mul_nonneg ha.le (sub_nonneg.mpr h.le))
  unfold f at hF
  nlinarith only [hF,hG]

private theorem deficitProfile_near_le {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (hT : t ≤ 2) :
    deficitProfile a t ≤ (a * (Real.sinh 1 - 1) / 4) * t ^ (2 - a) := by
  have hS : t ≤ 2 * Real.sinh (t / 2) := by
    have h := Real.self_le_sinh_iff.mpr (show 0 ≤ t / 2 by positivity)
    linarith only [h]
  have h := rpow_negative_gap_le ha ht hS
  have hSmall := sinh_gap_le_cube (show 0 ≤ t / 2 by positivity) (show t / 2 ≤ 1 by linarith only [hT])
  have hDiff : 2 * Real.sinh (t / 2) - t ≤ ((Real.sinh 1 - 1) / 4) * t ^ 3 := by
    nlinarith only [hSmall]
  have hMul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDiff ha.le)
    (Real.rpow_nonneg ht.le (-a - 1))
  have hE : t ^ 3 * t ^ (-a - 1) = t ^ (2 - a) := by
    rw [← Real.rpow_natCast t 3,← Real.rpow_add ht]
    congr 1
    norm_num
    ring
  unfold deficitProfile sinhProfile
  refine h.trans (hMul.trans_eq ?_)
  rw [show a * ((Real.sinh 1 - 1) / 4 * t ^ 3) * t ^ (-a - 1) =
    (a * (Real.sinh 1 - 1) / 4) * (t ^ 3 * t ^ (-a - 1)) by ring,hE]

private theorem coth_gap_bounds {z : ℝ} (hz : 0 < z) :
    0 ≤ z * Real.cosh z / Real.sinh z - 1 ∧ z * Real.cosh z / Real.sinh z - 1 ≤ z ^ 2 / 3 := by
  let f (x : ℝ) := x * Real.cosh x - Real.sinh x
  have hD (x : ℝ) : HasDerivAt f (x * Real.sinh x) x := by
    convert ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub (Real.hasDerivAt_sinh x) using 1
    simp only [id_eq,one_mul,add_sub_cancel_left]
  have hF : 0 < f z := BoseShape.positive_of_derivative (by norm_num [f]) hD
    (fun x hx => mul_pos hx (Real.sinh_pos_iff.mpr hx)) hz
  have hs := Real.sinh_pos_iff.mpr hz
  have hc := Real.cosh_pos z
  have hT := (Pressure.tanh_rational_bounds hz).1
  rw [Real.tanh_eq_sinh_div_cosh] at hT
  have h := (div_lt_div_iff₀ (by positivity : 0 < 3 + z ^ 2) hc).mp hT
  refine ⟨sub_nonneg.mpr ((one_le_div hs).mpr (sub_pos.mp hF).le),?_⟩
  apply sub_le_iff_le_add.mpr
  apply (div_le_iff₀ hs).mpr
  nlinarith only [h]

private theorem sinhProfile_le_exp {a t : ℝ} (ha : 0 < a) (ht : 1 ≤ t) :
    sinhProfile a t ≤ (2 : ℝ) ^ a * Real.exp (-(a / 2) * t) := by
  have ht₀ := zero_lt_one.trans_le ht
  have hE : 2 * Real.sinh (t / 2) = Real.exp (t / 2) * (1 - Real.exp (-t)) := by
    rw [Real.sinh_eq,mul_sub,mul_one,← Real.exp_add,show t / 2 + -t = -(t / 2) by ring]
    ring
  have hB : Real.exp (-t) ≤ 1 / 2 := by
    have h := (Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)).trans_le (Real.exp_le_exp.mpr ht)
    rw [Real.exp_neg,← one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by norm_num at h; exact h.le)
  have hL : (1 / 2) * Real.exp (t / 2) ≤ 2 * Real.sinh (t / 2) := by
    rw [hE,mul_comm (1 / 2 : ℝ)]
    exact mul_le_mul_of_nonneg_left (by linarith only [hB]) (Real.exp_pos _).le
  have h := Real.rpow_le_rpow_of_nonpos (mul_pos (by norm_num : (0 : ℝ) < 1 / 2) (Real.exp_pos _))
    hL (neg_nonpos.mpr ha.le)
  unfold sinhProfile
  refine h.trans_eq ?_
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2) (Real.exp_pos _).le,
    Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,
    show (t / 2) * (-a) = -(a / 2) * t by ring,
    show (1 / 2 : ℝ) ^ (-a) = (2 : ℝ) ^ a by
      rw [Real.rpow_neg (by norm_num),Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 2),
        Real.one_rpow,one_div,inv_inv]]

theorem sinhProfile_moment_one_integrable {a : ℝ} (ha : 0 < a) (ha₂ : a < 2) :
    IntegrableOn (fun t => t * sinhProfile a t) (Ioi 0) := by
  let f (t : ℝ) := t * sinhProfile a t
  have hM : Measurable f := by unfold f sinhProfile; fun_prop
  have hLocal : IntegrableOn f (Ioo 0 2) := by
    have hI := (intervalIntegral.integrableOn_Ioo_rpow_iff (t := (2 : ℝ)) (by norm_num)).mpr
      (show -1 < 1 - a by linarith only [ha₂])
    refine hI.mono' hM.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have ht₀ := ht.1
    have h := Real.rpow_le_rpow_of_nonpos ht₀ (show t ≤ 2 * Real.sinh (t / 2) by
      have h := Real.self_le_sinh_iff.mpr (show 0 ≤ t / 2 by positivity); linarith only [h]) (neg_nonpos.mpr ha.le)
    have hPos : 0 ≤ f t := by unfold f sinhProfile; positivity
    rw [Real.norm_of_nonneg hPos]
    calc
      _ ≤ t * t ^ (-a) := mul_le_mul_of_nonneg_left h ht₀.le
      _ = _ := by rw [mul_comm,← Real.rpow_add_one ht₀.ne']; congr 1; ring
  have hFar : IntegrableOn f (Ioi 1) := by
    have hI : IntegrableOn (fun t : ℝ => t * Real.exp (-(a / 2) * t)) (Ioi 0) := by
      simpa only [pow_one,neg_mul,mul_comm (a / 2)] using GammaMeasure.expMoment_nat_integrable 1 (c := a / 2) (by positivity)
    have hI' : IntegrableOn (fun t : ℝ => (2 : ℝ) ^ a * (t * Real.exp (-(a / 2) * t))) (Ioi 0) :=
      hI.const_mul _
    refine (hI'.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))).mono'
      hM.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht₀ := zero_lt_one.trans (show 1 < t from ht)
    have h := mul_le_mul_of_nonneg_left (sinhProfile_le_exp ha (show 1 < t from ht).le) ht₀.le
    rw [Real.norm_of_nonneg (show 0 ≤ f t by unfold f sinhProfile; positivity)]
    convert h using 1
    ring
  rw [← show Ioo (0 : ℝ) 2 ∪ Ioi 1 = Ioi 0 by
    ext t
    simp only [mem_union,mem_Ioo,mem_Ioi]
    constructor
    · rintro (h | h) <;> linarith
    · intro h
      by_cases ht : t < 2
      · exact Or.inl ⟨h,ht⟩
      · exact Or.inr (by linarith)]
  exact hLocal.union hFar

private theorem deficitBoundary_abs_le {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    |deficitBoundary a t| ≤ (a + 1) * deficitProfile a t + (a / 12) * t ^ 2 * sinhProfile a t := by
  let z := t / 2
  let d := 2 * Real.sinh z
  let H := sinhProfile a t
  let D := deficitProfile a t
  let q := z * Real.cosh z / Real.sinh z - 1
  have hz : 0 < z := div_pos ht (by norm_num)
  have hs := Real.sinh_pos_iff.mpr hz
  have hd : 0 < d := mul_pos (by norm_num) hs
  have hH : 0 ≤ H := Real.rpow_nonneg hd.le _
  have hD : 0 ≤ D := deficitProfile_nonneg ha ht
  have hQ := coth_gap_bounds hz
  have hEq : deficitBoundary a t = -(a + 1) * D + a * q * H := by
    unfold deficitBoundary deficitProfileDerivative sinhProfileDerivative D deficitProfile H sinhProfile
    change t * (-a * t ^ (-a - 1) - -a * Real.cosh z * d ^ (-a - 1)) -
      (t ^ (-a) - d ^ (-a)) = -(a + 1) * (t ^ (-a) - d ^ (-a)) + a * q * d ^ (-a)
    rw [Real.rpow_sub_one ht.ne',Real.rpow_sub_one hd.ne']
    unfold q d z
    field_simp [ht.ne',hs.ne'] <;> ring
  have hTri := abs_add_le (-(a + 1) * D) (a * q * H)
  rw [abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hD),
    abs_of_nonneg (mul_nonneg (mul_nonneg ha.le hQ.1) hH)] at hTri
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQ.2 ha.le) hH
  rw [hEq]
  refine hTri.trans ?_
  unfold z at h
  nlinarith only [h]

private theorem deficitBoundary_atZero {a : ℝ} (ha : 0 < a) (ha₂ : a < 2) :
    Tendsto (deficitBoundary a) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let C := (a + 1) * (a * (Real.sinh 1 - 1) / 4) + a / 12
  have hP : 0 < 2 - a := sub_pos.mpr ha₂
  have hLim : Tendsto (fun t : ℝ => C * t ^ (2 - a)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 (2 - a) (Or.inr hP.le)).tendsto.const_mul C
    rw [Real.zero_rpow hP.ne',mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg (deficitBoundary a t)) ?_ hLim
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), t < 2 from Iio_mem_nhds (by norm_num)).filter_mono nhdsWithin_le_nhds] with t ht ht'
  have ht₀ : 0 < t := ht
  have hD := deficitProfile_near_le ha ht₀ (show t < 2 from ht').le
  have hS : sinhProfile a t ≤ t ^ (-a) := by
    have h := Real.self_le_sinh_iff.mpr (show 0 ≤ t / 2 by positivity)
    exact Real.rpow_le_rpow_of_nonpos ht₀ (by linarith only [h]) (neg_nonpos.mpr ha.le)
  have hR : t ^ 2 * t ^ (-a) = t ^ (2 - a) := by
    rw [← Real.rpow_two,← Real.rpow_add ht₀,show (2 : ℝ) + -a = 2 - a by ring]
  rw [Real.norm_eq_abs]
  refine (deficitBoundary_abs_le ha ht₀).trans ?_
  have h₁ := mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ a + 1)
  have h₂ := mul_le_mul_of_nonneg_left hS (by positivity : 0 ≤ a / 12 * t ^ 2)
  have hT : a / 12 * t ^ 2 * t ^ (-a) = a / 12 * t ^ (2 - a) := by rw [mul_assoc,hR]
  rw [hT] at h₂
  unfold C
  nlinarith only [h₁,h₂]

private theorem deficitBoundary_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (deficitBoundary a) atTop (𝓝 0) := by
  have hL := (tendsto_rpow_neg_atTop ha).const_mul (a + 1)
  have hR := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (a / 2) (by positivity)).const_mul
    (a / 12 * (2 : ℝ) ^ a)
  have h := hL.add hR
  simp only [mul_zero,add_zero,Real.rpow_two] at h
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg (deficitBoundary a t)) ?_ h
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht₀ := zero_lt_one.trans_le ht
  rw [Real.norm_eq_abs]
  refine (deficitBoundary_abs_le ha ht₀).trans ?_
  have h₁ := mul_le_mul_of_nonneg_left (deficitProfile_le_power a t ht₀) (by positivity : 0 ≤ a + 1)
  have h₂ := mul_le_mul_of_nonneg_left (sinhProfile_le_exp ha ht) (by positivity : 0 ≤ a / 12 * t ^ 2)
  change _ ≤ (a + 1) * t ^ (-a) + (a / 12 * (2 : ℝ) ^ a) * (t ^ 2 * Real.exp (-(a / 2) * t))
  nlinarith only [h₁,h₂]

theorem deficit_moment_reduction {a : ℝ} (ha : 0 < a) (ha₂ : a < 2) :
    (∫ t : ℝ in Ioi 0, t * deficitProfile (a + 2) t) =
      (a / (4 * (a + 1))) * ∫ t : ℝ in Ioi 0, t * sinhProfile a t := by
  let f (t : ℝ) := t * (a * (a + 1) * deficitProfile (a + 2) t - a ^ 2 / 4 * sinhProfile a t)
  let g (t : ℝ) := t * deficitProfile (a + 2) t
  let h (t : ℝ) := t * sinhProfile a t
  have hG : IntegrableOn g (Ioi 0) := (GammaMixture.gammaTotal_fractional_eq_profile
    (p := a + 2) (by linarith only [ha]) (by linarith only [ha₂])).1
  have hH : IntegrableOn h (Ioi 0) := sinhProfile_moment_one_integrable ha ha₂
  have hF : f = fun t => (a * (a + 1)) * g t - (a ^ 2 / 4) * h t := by
    funext t
    unfold f g h
    ring
  have hI : IntegrableOn f (Ioi 0) := by
    rw [hF]
    exact (hG.const_mul _).sub (hH.const_mul _)
  have hZ : deficitBoundary a 0 = 0 := by
    simp only [deficitBoundary,zero_mul,deficitProfile,sinhProfile,zero_div,Real.sinh_zero,mul_zero,sub_self]
  have hC : ContinuousWithinAt (deficitBoundary a) (Ici 0) 0 := by
    rw [← continuousWithinAt_Ioi_iff_Ici]
    change Tendsto (deficitBoundary a) (𝓝[>] 0) (𝓝 (deficitBoundary a 0))
    rw [hZ]
    exact deficitBoundary_atZero ha ha₂
  have hInt := integral_Ioi_of_hasDerivAt_of_tendsto hC
    (fun t ht => deficitBoundary_hasDerivAt a ht) hI (deficitBoundary_atTop ha)
  change (∫ t : ℝ in Ioi 0, f t) = _ at hInt
  rw [hZ,sub_zero,hF,integral_sub (hG.const_mul _) (hH.const_mul _),
    integral_const_mul,integral_const_mul] at hInt
  change (∫ t : ℝ in Ioi 0, g t) = _ * ∫ t : ℝ in Ioi 0, h t
  have hEq : (a * (a + 1)) * (∫ t : ℝ in Ioi 0, g t) = (a ^ 2 / 4) * (∫ t : ℝ in Ioi 0, h t) :=
    sub_eq_zero.mp hInt
  apply (mul_left_cancel₀ (by positivity : a * (a + 1) ≠ 0))
  rw [hEq]
  field_simp [show a + 1 ≠ 0 by positivity]

end ACS12.GammaDeficit

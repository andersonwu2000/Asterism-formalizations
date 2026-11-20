import ACS12.PureAdjacentArc
import ACS12.PureRightUpper

/-! Whole-tail estimates and the normalized B scaling at p = 9/5. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set
open scoped BigOperators

theorem purePeano_quadratic_upper {p u x : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hu : 0 < u) (hx : 0 < x)
    (k : CircleKernelKind) :
    lawPeanoKernel p 1 0 u k x ≤
      (u ^ 2 / 2) * (p * (p + 1) * x ^ (-(p + 2))) := by
  have hp₀ := zero_lt_one.trans_le hp
  have hθ : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have hf := lawPeanoKernel_integrable hp hp₂ zero_lt_one hθ hu hx k
  have hg := (lawMoment_integrable hp hp₂ zero_lt_one hθ hx 2).const_mul (u ^ 2 / 2)
  have h := integral_mono_ae hf hg (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0 < s := hs
    have hP := (densityPolynomial_lt_quadratic k (mul_pos hu hs₀)).le
    have hM := mul_le_mul_of_nonneg_left hP
      (mul_pos (lawDensity_pos hp₀ zero_lt_one hθ hs₀) (Real.exp_pos (-s * x))).le
    change lawPeanoDensity p 1 0 u k s * Real.exp (-s * x) ≤
      (u ^ 2 / 2) * (lawDensity p 1 0 s * s ^ 2 * Real.exp (-s * x))
    unfold lawPeanoDensity
    calc
      _ = _ := by ring
      _ ≤ _ := hM
      _ = _ := by ring)
  rw [integral_const_mul] at h
  change lawPeanoKernel p 1 0 u k x ≤ (u ^ 2 / 2) * lawMoment p 1 0 2 x at h
  rw [pureMoment_succ hp₀ hx 1, lawMoment_zero_slope hp₀ hx, Nat.cast_one] at h
  refine h.trans_eq ?_
  rw [show x ^ (-(p + 2)) = x ^ (-(p + 1)) / x by
    rw [show -(p + 2) = -(p + 1) - 1 by ring, Real.rpow_sub_one hx.ne']]
  ring

theorem purePeanoB_series_scale {p u r : ℝ} (hu : 0 < u) (hr : 0 < r) :
    purePeanoB p u r = r ^ (-p) * purePeanoB p (u / r) 1 := by
  have hU : r * (1 + u / r) = r + u := by field_simp [hr.ne']
  unfold purePeanoB
  rw [← hU, Real.mul_rpow hr.le (by positivity : 0 ≤ 1 + u / r), Real.one_rpow, Real.one_rpow,
    show -(p + 1) = -p - 1 by ring, Real.rpow_sub_one hr.ne']
  ring

theorem pureBStack_upperArc {u : ℝ} (hu : 0 < u) (hu' : u ≤ 7 / 8) :
    pureBStack (9 / 5) u ≤ (u / (7 / 8)) ^ 2 * pureBStack (9 / 5) (7 / 8) := by
  let U : ℝ := 7 / 8
  let p : ℝ := 9 / 5
  have hU : 0 < U := by norm_num [U]
  have hp : 1 ≤ p := by norm_num [p]
  have hp₂ : p ≤ 2 := by norm_num [p]
  have hP : p - 3 = -(6 / 5 : ℝ) := by norm_num [p]
  have hF (x : ℝ) (hx : 0 < x) :
      pureBStack p x / x ^ 2 =
        ∑' j : ℕ, ((j : ℝ) + 1) ^ (-(3 : ℝ)) *
          (((x / ((j : ℝ) + 1)) ^ (-(6 / 5 : ℝ))) * purePeanoB p (x / ((j : ℝ) + 1)) 1) := by
    unfold pureBStack samplingTail
    simp only [Nat.cast_add, Nat.cast_one, mul_one, zero_add, one_mul]
    rw [mul_div_assoc, div_eq_mul_inv]
    -- The factor x^(p-1)/x² is independent of the site.
    rw [show (∑' j : ℕ, purePeanoB p x ((j : ℝ) + 1)) * (x ^ 2)⁻¹ =
      (x ^ 2)⁻¹ * (∑' j : ℕ, purePeanoB p x ((j : ℝ) + 1)) by ring, ← mul_assoc,
      ← div_eq_mul_inv, ← Real.rpow_two, ← Real.rpow_sub hx,
      show p - 1 - 2 = p - 3 by ring, ← tsum_mul_left]
    apply tsum_congr
    intro j
    let r := (j : ℝ) + 1
    have hr : 0 < r := by dsimp only [r]; positivity
    change x ^ (p - 3) * purePeanoB p x r = r ^ (-(3 : ℝ)) *
      ((x / r) ^ (-(6 / 5 : ℝ)) * purePeanoB p (x / r) 1)
    rw [purePeanoB_series_scale hx hr, show -(6 / 5 : ℝ) = p - 3 from hP.symm,
      Real.div_rpow hx.le hr.le, show -(3 : ℝ) = -p + (p - 3) by ring,
      Real.rpow_add hr]
    field_simp [(Real.rpow_pos_of_pos hr _).ne']
  have hS (x : ℝ) (hx : 0 < x) :
      Summable (fun j : ℕ => ((j : ℝ) + 1) ^ (-(3 : ℝ)) *
        (((x / ((j : ℝ) + 1)) ^ (-(6 / 5 : ℝ))) * purePeanoB p (x / ((j : ℝ) + 1)) 1)) := by
    apply ((pureBStack_samples_summable hp hp₂ hx).mul_left (x ^ (p - 3))).congr
    intro j
    let r := (j : ℝ) + 1
    have hr : 0 < r := by dsimp only [r]; positivity
    change x ^ (p - 3) * purePeanoB p x r = r ^ (-(3 : ℝ)) *
      ((x / r) ^ (-(6 / 5 : ℝ)) * purePeanoB p (x / r) 1)
    rw [purePeanoB_series_scale hx hr, show -(6 / 5 : ℝ) = p - 3 from hP.symm,
      Real.div_rpow hx.le hr.le, show -(3 : ℝ) = -p + (p - 3) by ring,
      Real.rpow_add hr]
    field_simp [(Real.rpow_pos_of_pos hr _).ne']
  have hOrd : pureBStack p u / u ^ 2 ≤ pureBStack p U / U ^ 2 := by
    rw [hF u hu, hF U hU]
    apply (hS u hu).tsum_le_tsum _ (hS U hU)
    intro j
    let r := (j : ℝ) + 1
    have hr : 1 ≤ r := le_add_of_nonneg_left (Nat.cast_nonneg _)
    have hr₀ := zero_lt_one.trans_le hr
    have huR : u / r ≤ U / r := div_le_div_of_nonneg_right hu' hr₀.le
    have hUR : U / r ≤ U := div_le_self hU.le hr
    exact mul_le_mul_of_nonneg_left
      (upperBscaled_mono ⟨div_pos hu hr₀, huR.trans hUR⟩ ⟨div_pos hU hr₀, hUR⟩ huR)
      (Real.rpow_nonneg hr₀.le _)
  have h := (div_le_div_iff₀ (sq_pos_of_pos hu) (sq_pos_of_pos hU)).mp hOrd
  change pureBStack p u ≤ (u / U) ^ 2 * pureBStack p U
  apply (le_of_mul_le_mul_right _ (sq_pos_of_pos hU))
  have hE : ((u / U) ^ 2 * pureBStack p U) * U ^ 2 = pureBStack p U * u ^ 2 := by
    rw [show (u / U) ^ 2 = u ^ 2 / U ^ 2 from div_pow u U 2]
    field_simp [hU.ne']
  rwa [hE]

end ACS12.GammaMeasure

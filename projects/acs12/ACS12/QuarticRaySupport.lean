import ACS12.ConcaveSupport
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds

/-! An affine majorant of the integrated rank debit on the entire exponent ray. -/
namespace ACS12.NativeCells

open Finset Set

private noncomputable def debitPrimitive (A B g t : ℝ) : ℝ :=
  A * (1 - Real.exp (-g * t)) +
    B * ((1 - Real.exp (-g * t)) / g - t * Real.exp (-g * t))

private noncomputable def debitRate (A B g t : ℝ) : ℝ :=
  g * Real.exp (-g * t) * (A + B * t)

private theorem debitPrimitive_deriv {A B g : ℝ} (hg : 0 < g) (t : ℝ) :
    HasDerivAt (debitPrimitive A B g) (debitRate A B g t) t := by
  have hE := ((hasDerivAt_id t).const_mul (-g)).exp
  have hC := hE.const_sub 1
  convert (hC.const_mul A).add (((hC.div_const g).sub ((hasDerivAt_id t).mul hE)).const_mul B) using 1
  simp only [debitRate, id_eq, mul_one, one_mul]
  field_simp [hg.ne']
  ring

private theorem debitRate_deriv (A B g t : ℝ) :
    HasDerivAt (debitRate A B g) (-g * Real.exp (-g * t) * (g * (A + B * t) - B)) t := by
  have hE := ((hasDerivAt_id t).const_mul (-g)).exp.const_mul g
  have hB := ((hasDerivAt_id t).const_mul B).const_add A
  convert hE.mul hB using 1
  simp only [id_eq, mul_one]
  ring

private theorem log_rank_ratio_lower {g : ℝ} (hg : 0 ≤ g) :
    2 * (1 - Real.exp (-g)) / (1 + Real.exp (-g)) ≤ g := by
  let a := Real.exp g - 1
  have ha : 0 ≤ a := sub_nonneg.mpr (Real.one_le_exp_iff.mpr hg)
  have h := (Real.hasSum_log_one_add ha).summable.sum_le_tsum (range 1) (fun j _ => by positivity)
  rw [(Real.hasSum_log_one_add ha).tsum_eq, sum_range_one] at h
  norm_num at h
  have hLog : Real.log (1 + a) = g := by
    rw [show 1 + a = Real.exp g by dsimp [a]; ring, Real.log_exp]
  rw [hLog] at h
  convert h using 1
  dsimp only [a]
  rw [Real.exp_neg]
  have hE : 0 < Real.exp g := Real.exp_pos _
  field_simp [hE.ne', show Real.exp g + 1 ≠ 0 by positivity,
    show Real.exp g - 1 + 2 ≠ 0 by linarith]
  ring

private theorem debitPrimitive_affine {A B g t : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hBA : B ≤ 4 * A / 23)
    (hg : 1 / 4 ≤ g) (ht : 0 ≤ t) :
    debitPrimitive A B g t ≤
      (A + B / 2) * (1 - Real.exp (-g)) ^ 2 / (1 + Real.exp (-g)) +
        t * (A + B) * Real.exp (-1) := by
  have hg₀ : 0 < g := by linarith only [hg]
  have hD (x : ℝ) := debitPrimitive_deriv (A := A) (B := B) hg₀ x
  have hK : ConcaveOn ℝ (Ici (0 : ℝ)) (debitPrimitive A B g) := by
    have hRate : AntitoneOn (debitRate A B g) (Ici (0 : ℝ)) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici _)
      · exact fun x _ => (debitRate_deriv A B g x).continuousAt.continuousWithinAt
      · exact fun x _ => (debitRate_deriv A B g x).differentiableAt.differentiableWithinAt
      · intro x hx
        have hx₀ : 0 ≤ x := interior_subset hx
        have hGA : A / 4 ≤ g * A := by nlinarith only [mul_nonneg (sub_nonneg.mpr hg) hA]
        have hAB : 0 ≤ g * (A + B * x) - B := by
          nlinarith only [hGA, hBA, hA, mul_nonneg hg₀.le (mul_nonneg hB hx₀)]
        rw [(debitRate_deriv A B g x).deriv]
        exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hg₀.le)
          (Real.exp_pos _).le) hAB
    apply AntitoneOn.concaveOn_of_deriv (convex_Ici _)
    · exact fun x _ => (hD x).continuousAt.continuousWithinAt
    · exact fun x _ => (hD x).differentiableAt.differentiableWithinAt
    · intro x hx y hy hxy
      rw [(hD x).deriv, (hD y).deriv]
      exact hRate (interior_subset hx) (interior_subset hy) hxy
  have hT := ACS12.concave_tangent_upper hK (show t ∈ Set.Ici (0 : ℝ) from ht)
    (show (1 : ℝ) ∈ Set.Ici (0 : ℝ) by norm_num) (hD 1)
  let q := Real.exp (-g)
  have hq : 0 < q := Real.exp_pos _
  have hLog : 2 * (1 - q) ≤ g * (1 + q) :=
    (div_le_iff₀ (by positivity : 0 < 1 + q)).mp (log_rank_ratio_lower hg₀.le)
  have hMoment : (1 - q) / g - q ≤ (1 - q) / 2 := by
    rw [sub_le_iff_le_add, div_le_iff₀ hg₀]
    nlinarith only [hLog]
  have hR : 1 - q - g * q ≤ (1 - q) ^ 2 / (1 + q) := by
    apply (le_div_iff₀ (by positivity : 0 < 1 + q)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hLog hq.le]
  have hIntercept : debitPrimitive A B g 1 - debitRate A B g 1 ≤
      (A + B / 2) * (1 - q) ^ 2 / (1 + q) := by
    have h₁ := mul_le_mul_of_nonneg_left hMoment hB
    have h₂ := mul_le_mul_of_nonneg_left hR (show 0 ≤ A + B / 2 by positivity)
    have h₃ := mul_nonneg (mul_nonneg hB hg₀.le) hq.le
    change A * (1 - Real.exp (-g * 1)) + B * ((1 - Real.exp (-g * 1)) / g - 1 * Real.exp (-g * 1)) -
      g * Real.exp (-g * 1) * (A + B * 1) ≤ _
    simp only [mul_one, one_mul]
    change A * (1 - q) + B * ((1 - q) / g - q) - g * q * (A + B) ≤ _
    have h₂' : (A + B / 2) * (1 - q - g * q) ≤
        (A + B / 2) * (1 - q) ^ 2 / (1 + q) := by simpa only [mul_div_assoc] using h₂
    linarith only [h₁, h₂', h₃]
  have hSlope : debitRate A B g 1 ≤ (A + B) * Real.exp (-1) := by
    simp only [debitRate, mul_one]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (Real.mul_exp_neg_le_exp_neg_one g) (add_nonneg hA hB)
  have hBound := mul_le_mul_of_nonneg_left hSlope ht
  change _ ≤ (A + B / 2) * (1 - q) ^ 2 / (1 + q) + t * (A + B) * Real.exp (-1)
  linarith only [hT, hIntercept, hBound]

private theorem rank_moment_price {q : ℝ} (hq : 0 ≤ q) (hq₁ : q ≤ 1) :
    q ^ 2 * (1 - q) ^ 2 / (1 + q) ≤ 1 / 20 := by
  apply (div_le_iff₀ (by positivity : 0 < 1 + q)).mpr
  have hP : 0 ≤ q * (1 - q) := mul_nonneg hq (sub_nonneg.mpr hq₁)
  by_cases h : q ≤ 1 / 4
  · have hProd : q * (1 - q) ≤ 3 / 16 := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ 3 / 4 - q by linarith)]
    have hh := pow_le_pow_left₀ hP hProd 2
    rw [mul_pow] at hh
    nlinarith only [hh, hq]
  · have hProd : q * (1 - q) ≤ 1 / 4 := by nlinarith only [sq_nonneg (q - 1 / 2)]
    have hh := pow_le_pow_left₀ hP hProd 2
    rw [mul_pow] at hh
    nlinarith only [hh, lt_of_not_ge h]

private theorem quarticRay_affine {ι : Type*} (s : Finset ι) (μ g : ι → ℝ) {A B t : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hBA : B ≤ 4 * A / 23) (ht : 0 ≤ t)
    (hμ : ∀ i ∈ s, 0 ≤ μ i) (hg : ∀ i ∈ s, 1 / 4 ≤ g i)
    (h₂ : (∑ i ∈ s, μ i * Real.exp (-g i) ^ 2) ≤ 13 / 20)
    (h₄ : (∑ i ∈ s, μ i * Real.exp (-g i) ^ 4) ≤ 3 / 20) :
    (∑ i ∈ s, μ i * Real.exp (-g i) ^ 4 * debitPrimitive A B (g i) t) ≤
      (13 / 400) * (A + B / 2) + t * (69 / 1250) * (A + B) := by
  let q (i : ι) := Real.exp (-g i)
  have hq (i : ι) : 0 < q i := Real.exp_pos _
  have hSlope : (3 / 20 : ℝ) * Real.exp (-1) ≤ 69 / 1250 := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact (div_le_iff₀ (Real.exp_pos _)).mpr (by linarith only [Real.exp_one_gt_d9])
  have hpoint (i : ι) (hi : i ∈ s) :
      μ i * q i ^ 4 * debitPrimitive A B (g i) t ≤
        (A + B / 2) / 20 * (μ i * q i ^ 2) +
          t * (A + B) * Real.exp (-1) * (μ i * q i ^ 4) := by
    have hμi := hμ i hi
    have h₁ := mul_le_mul_of_nonneg_left (debitPrimitive_affine hA hB hBA (hg i hi) ht)
      (show 0 ≤ μ i * q i ^ 4 by positivity)
    have hq₁ : q i ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hg i hi])
    have h₂ := mul_le_mul_of_nonneg_left (rank_moment_price (hq i).le hq₁)
      (show 0 ≤ (A + B / 2) * (μ i * q i ^ 2) by positivity)
    change _ ≤ μ i * q i ^ 4 * ((A + B / 2) * (1 - q i) ^ 2 / (1 + q i) +
      t * (A + B) * Real.exp (-1)) at h₁
    simp only [div_eq_mul_inv] at h₁ h₂ ⊢
    linarith only [h₁, h₂]
  have h := sum_le_sum hpoint
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at h
  have h₂' := mul_le_mul_of_nonneg_left h₂ (show 0 ≤ (A + B / 2) / 20 by positivity)
  have h₄' := mul_le_mul_of_nonneg_left h₄
    (show 0 ≤ t * (A + B) * Real.exp (-1) by positivity)
  have hS := mul_le_mul_of_nonneg_left hSlope (show 0 ≤ t * (A + B) by positivity)
  dsimp only [q] at h
  linarith only [h, h₂', h₄', hS]

/-- Integrate the pointwise rank derivative comparison using the one whole-ray supporting line. -/
theorem quarticRay_defect_le {ι : Type*} (s : Finset ι) (μ g : ι → ℝ)
    (F F' : ℝ → ℝ) {A B t pInf : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hBA : B ≤ 4 * A / 23)
    (ht : 0 ≤ t) (hpInf : 0 ≤ pInf)
    (hμ : ∀ i ∈ s, 0 ≤ μ i) (hg : ∀ i ∈ s, 1 / 4 ≤ g i)
    (h₂ : (∑ i ∈ s, μ i * Real.exp (-g i) ^ 2) ≤ 13 / 20)
    (h₄ : (∑ i ∈ s, μ i * Real.exp (-g i) ^ 4) ≤ 3 / 20)
    (hF : ∀ v : ℝ, 0 ≤ v → HasDerivAt F (F' v) v)
    (hPrice : ∀ v : ℝ, 0 ≤ v → F' v ≤ pInf *
      ∑ i ∈ s, μ i * Real.exp (-g i) ^ 4 * (g i * Real.exp (-g i * v) * (A + B * v))) :
    F t ≤ F 0 + pInf * ((13 / 400) * (A + B / 2) + t * (69 / 1250) * (A + B)) := by
  let G (t : ℝ) := pInf * ∑ i ∈ s, μ i * Real.exp (-g i) ^ 4 * debitPrimitive A B (g i) t
  let G' (t : ℝ) := pInf * ∑ i ∈ s, μ i * Real.exp (-g i) ^ 4 * debitRate A B (g i) t
  have hG (v : ℝ) : HasDerivAt G (G' v) v := by
    exact (HasDerivAt.fun_sum (u := s) (fun i hi =>
      (debitPrimitive_deriv (A := A) (B := B) (g := g i) (by linarith only [hg i hi]) v).const_mul
        (μ i * Real.exp (-g i) ^ 4))).const_mul pInf
  have hMono : AntitoneOn (fun v => F v - G v) (Set.Ici (0 : ℝ)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · exact fun v hv => ((hF v hv).sub (hG v)).continuousAt.continuousWithinAt
    · exact fun v hv => ((hF v (interior_subset hv)).sub (hG v)).differentiableAt.differentiableWithinAt
    · intro v hv
      change deriv (F - G) v ≤ 0
      rw [((hF v (interior_subset hv)).sub (hG v)).deriv]
      exact sub_nonpos.mpr (hPrice v (interior_subset hv))
  have hDiff := hMono (show (0 : ℝ) ∈ Set.Ici 0 by simp) (show t ∈ Set.Ici (0 : ℝ) from ht) ht
  have hZero : G 0 = 0 := by simp [G, debitPrimitive]
  have hBound : G t ≤ pInf * ((13 / 400) * (A + B / 2) + t * (69 / 1250) * (A + B)) :=
    mul_le_mul_of_nonneg_left (quarticRay_affine s μ g hA hB hBA ht hμ hg h₂ h₄) hpInf
  linarith only [hDiff, hZero, hBound]

end ACS12.NativeCells

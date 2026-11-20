import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! The complete centered-moment curvature used by the pressure route, including literal two. -/
namespace ACS12.Pressure

open Set

noncomputable def entropyExp (x : ℝ) : ℝ := Real.exp x - 1 - x

noncomputable def momentCurvature (p x : ℝ) : ℝ :=
  (p + 1) * entropyExp ((p / (p + 1)) * x) - (18 / 25) * entropyExp x

noncomputable def momentCurvatureD (p x : ℝ) : ℝ :=
  p * (Real.exp ((p / (p + 1)) * x) - 1) - (18 / 25) * (Real.exp x - 1)

private noncomputable def momentCurvatureDD (p x : ℝ) : ℝ :=
  Real.exp ((p / (p + 1)) * x) * (p ^ 2 / (p + 1) - (18 / 25) * Real.exp (x / (p + 1)))

theorem exp_pressure_cap_lt : Real.exp (111 / 40) < 16039 / 1000 := by
  have h := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 111 / 160) (by norm_num : (111 / 160 : ℝ) ≤ 1)
    (n := 9) (by decide)
  have h' : Real.exp (111 / 160) ≤ 200121 / 100000 := by
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith only [h]
  rw [show (111 / 40 : ℝ) = ((4 : ℕ) : ℝ) * (111 / 160) by norm_num, Real.exp_nat_mul]
  exact (pow_le_pow_left₀ (Real.exp_pos _).le h' 4).trans_lt (by norm_num)

theorem pressure_log16_lt_cap : Real.log 16 < 111 / 40 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 16)).mpr
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 111 / 40) 10
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith only [h]

private theorem exp_scaled_pressure_cap_gt : (5953 / 1000 : ℝ) < Real.exp ((9 / 14) * (111 / 40)) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ (9 / 14) * (111 / 40)) 10
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith only [h]

theorem momentCurvature_zero (p : ℝ) : momentCurvature p 0 = 0 := by
  simp [momentCurvature, entropyExp]

private theorem momentCurvatureD_zero (p : ℝ) : momentCurvatureD p 0 = 0 := by
  simp [momentCurvatureD]

private theorem momentCurvature_hasDerivAt {p : ℝ} (hp : 0 < p) (x : ℝ) :
    HasDerivAt (momentCurvature p) (momentCurvatureD p x) x := by
  let a := p / (p + 1)
  have h := hasDerivAt_id x
  have h₁ := h.const_mul a
  have hd := (((h₁.exp.sub_const 1).sub h₁).const_mul (p + 1)).sub
    ((((Real.hasDerivAt_exp x).sub_const 1).sub h).const_mul (18 / 25))
  convert hd using 1
  simp only [momentCurvatureD, a, id_eq, mul_one]
  field_simp [(show p + 1 ≠ 0 by positivity)]

private theorem momentCurvatureD_hasDerivAt {p : ℝ} (hp : 0 < p) (x : ℝ) :
    HasDerivAt (momentCurvatureD p) (momentCurvatureDD p x) x := by
  let a := p / (p + 1)
  have h := ((hasDerivAt_id x).const_mul a).exp
  have hd := ((h.sub_const 1).const_mul p).sub (((Real.hasDerivAt_exp x).sub_const 1).const_mul (18 / 25))
  convert hd using 1
  have hE : Real.exp (a * x) * Real.exp (x / (p + 1)) = Real.exp x := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [a]
    field_simp [(show p + 1 ≠ 0 by positivity)]
  change Real.exp (a * x) * (p ^ 2 / (p + 1) - 18 / 25 * Real.exp (x / (p + 1))) =
    p * (Real.exp (a * x) * (a * 1)) - 18 / 25 * Real.exp x
  linear_combination -(18 / 25) * hE

private theorem momentCurvature_cap_pos {p : ℝ} (hp : 9 / 5 ≤ p) :
    0 < momentCurvature p (111 / 40) := by
  let A : ℝ := 111 / 40
  have h₀ : 0 < momentCurvature (9 / 5) A := by
    have hF : (9 / 5 : ℝ) / (9 / 5 + 1) = 9 / 14 := by norm_num
    unfold momentCurvature entropyExp
    rw [hF]
    change 0 < (9 / 5 + 1) * (Real.exp ((9 / 14) * A) - 1 - (9 / 14) * A) -
      (18 / 25) * (Real.exp A - 1 - A)
    dsimp only [A]
    linarith only [exp_pressure_cap_lt, exp_scaled_pressure_cap_gt]
  have hD (x : ℝ) (hx : 0 < x) : HasDerivAt (fun z => momentCurvature z A)
      (Real.exp ((x / (x + 1)) * A) * (1 + A / (x + 1)) - 1 - A) x := by
    have h := hasDerivAt_id x
    have hd := h.div (h.add_const 1) (show x + 1 ≠ 0 by positivity)
    have hA := hd.mul_const A
    convert ((h.add_const 1).mul ((hA.exp.sub_const 1).sub hA)).sub_const ((18 / 25) * entropyExp A) using 1
    simp only [Pi.div_apply, Pi.sub_apply, id_eq, one_mul, mul_one]
    field_simp [(show x + 1 ≠ 0 by positivity)]
    ring
  have hM : MonotoneOn (fun z => momentCurvature z A) (Ici (9 / 5)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · exact fun x hx => (hD x ((by norm_num : (0 : ℝ) < 9 / 5).trans_le hx)).continuousAt.continuousWithinAt
    · exact fun x hx => (hD x ((by norm_num : (0 : ℝ) < 9 / 5).trans_le (interior_subset hx))).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : (9 / 5 : ℝ) ≤ x := show x ∈ Ici (9 / 5 : ℝ) from interior_subset hx
      have hx₀ := (by norm_num : (0 : ℝ) < 9 / 5).trans_le hx'
      rw [(hD x hx₀).deriv]
      have hN : 0 ≤ A / (x + 1) := by dsimp only [A]; positivity
      have hE : x / (x + 1) * A + A / (x + 1) = A := by
        field_simp [(show x + 1 ≠ 0 by positivity)]
      have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp ((x / (x + 1)) * A))
        (by linarith only [hN] : 0 ≤ 1 + A / (x + 1))
      have h' : 0 ≤ (x / (x + 1) * A) * (A / (x + 1)) := by dsimp only [A]; positivity
      nlinarith only [h,hE,h']
  exact h₀.trans_le (hM (mem_Ici.mpr le_rfl) (mem_Ici.mpr hp) hp)

theorem momentCurvature_pos {p x : ℝ} (hp : 9 / 5 ≤ p) (hP : p ≤ 2) (hx : x ≤ 111 / 40)
    (hx₀ : x ≠ 0) : 0 < momentCurvature p x := by
  let A : ℝ := 111 / 40
  let F := momentCurvature p
  let D := momentCurvatureD p
  let E := momentCurvatureDD p
  let c := p ^ 2 / ((18 / 25) * (p + 1))
  let T := (p + 1) * Real.log c
  have hp₀ := (by norm_num : (0 : ℝ) < 9 / 5).trans_le hp
  have hc : 1 < c := by
    apply (lt_div_iff₀ (show 0 < (18 / 25 : ℝ) * (p + 1) by positivity)).mpr
    nlinarith only [hp,hP,pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9 / 5) hp 2]
  have hT : 0 < T := mul_pos (by positivity) (Real.log_pos hc)
  have hEl (s : ℝ) : Real.exp (s / (p + 1)) < c ↔ s < T := by
    calc
      _ ↔ Real.exp (s / (p + 1)) < Real.exp (Real.log c) := by rw [Real.exp_log (zero_lt_one.trans hc)]
      _ ↔ s / (p + 1) < Real.log c := Real.exp_lt_exp
      _ ↔ _ := by rw [div_lt_iff₀ (by positivity : 0 < p + 1), mul_comm]
  have hcE : p ^ 2 / (p + 1) = (18 / 25) * c := by dsimp only [c]; field_simp
  have hPos (s : ℝ) (hs : s < T) : 0 < E s := by
    change 0 < Real.exp ((p / (p + 1)) * s) * (p ^ 2 / (p + 1) - (18 / 25) * Real.exp (s / (p + 1)))
    rw [hcE, ← mul_sub]
    exact mul_pos (Real.exp_pos _) (mul_pos (by norm_num) (sub_pos.mpr ((hEl s).mpr hs)))
  have hNeg (s : ℝ) (hs : T ≤ s) : E s ≤ 0 := by
    have h : c ≤ Real.exp (s / (p + 1)) := le_of_not_gt (fun h => (not_lt_of_ge hs) ((hEl s).mp h))
    change Real.exp ((p / (p + 1)) * s) * (p ^ 2 / (p + 1) - (18 / 25) * Real.exp (s / (p + 1))) ≤ 0
    rw [hcE, ← mul_sub]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (sub_nonpos.mpr h))
  have hD : StrictMonoOn D (Iic T) := by
    apply strictMonoOn_of_deriv_pos (convex_Iic _)
    · exact fun y _ => (momentCurvatureD_hasDerivAt hp₀ y).continuousAt.continuousWithinAt
    · intro y hy
      rw [(momentCurvatureD_hasDerivAt hp₀ y).deriv]
      exact hPos y (by simpa only [interior_Iic, mem_Iio] using hy)
  have hL (y : ℝ) (hy : y < 0) : 0 < F y := by
    have hMono : StrictAntiOn F (Iic 0) := by
      apply strictAntiOn_of_deriv_neg (convex_Iic _)
      · exact fun z _ => (momentCurvature_hasDerivAt hp₀ z).continuousAt.continuousWithinAt
      · intro z hz
        rw [(momentCurvature_hasDerivAt hp₀ z).deriv, ← momentCurvatureD_zero p]
        have h : z < 0 := by simpa only [interior_Iic, mem_Iio] using hz
        exact hD (mem_Iic.mpr (h.trans hT).le) (mem_Iic.mpr hT.le) h
    have h := hMono (mem_Iic.mpr hy.le) (mem_Iic.mpr le_rfl) hy
    simpa only [F, momentCurvature_zero] using h
  have hR (y : ℝ) (hy : 0 < y) (hyT : y ≤ T) : 0 < F y := by
    have hMono : StrictMonoOn F (Icc 0 T) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      · exact fun z _ => (momentCurvature_hasDerivAt hp₀ z).continuousAt.continuousWithinAt
      · intro z hz
        rw [(momentCurvature_hasDerivAt hp₀ z).deriv, ← momentCurvatureD_zero p]
        have hz₀ : z ∈ Ioo (0 : ℝ) T := by simpa only [interior_Icc] using hz
        exact hD (mem_Iic.mpr hT.le) (mem_Iic.mpr hz₀.2.le) hz₀.1
    have h := hMono ⟨le_rfl,hT.le⟩ ⟨hy.le,hyT⟩ hy
    simpa only [F, momentCurvature_zero] using h
  rcases lt_or_gt_of_ne hx₀ with hxN | hxP
  · exact hL x hxN
  · by_cases hxT : x ≤ T
    · exact hR x hxP hxT
    · have hTA : T < A := (lt_of_not_ge hxT).trans_le hx
      have hConv : ConvexOn ℝ (Icc T A) (fun z => -F z) := by
        apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
          (fun y _ => (momentCurvature_hasDerivAt hp₀ y).neg.continuousAt.continuousWithinAt)
          (fun y _ => (momentCurvature_hasDerivAt hp₀ y).neg.hasDerivWithinAt)
          (fun y _ => (momentCurvatureD_hasDerivAt hp₀ y).neg.hasDerivWithinAt)
        intro z hz
        exact neg_nonneg.mpr (hNeg z (show z ∈ Icc T A from interior_subset hz).1)
      let b := (x - T) / (A - T)
      have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr (lt_of_not_ge hxT).le) (sub_nonneg.mpr hTA.le)
      have hbU : b ≤ 1 := (div_le_one (sub_pos.mpr hTA)).mpr (sub_le_sub_right hx T)
      have hX : (1 - b) • T + b • A = x := by
        simp only [smul_eq_mul, b]
        field_simp [(sub_pos.mpr hTA).ne']
        ring
      have h := hConv.2 ⟨le_rfl,hTA.le⟩ ⟨hTA.le,le_rfl⟩ (sub_nonneg.mpr hbU) hb (sub_add_cancel 1 b)
      rw [hX] at h
      simp only [smul_eq_mul] at h
      have hF := hR T hT le_rfl
      have hA : 0 < F A := momentCurvature_cap_pos hp
      have hMin : 0 < min (F T) (F A) := lt_min hF hA
      have h₁ := mul_le_mul_of_nonneg_left (min_le_left (F T) (F A)) (sub_nonneg.mpr hbU)
      have h₂ := mul_le_mul_of_nonneg_left (min_le_right (F T) (F A)) hb
      nlinarith only [h,hMin,h₁,h₂]

end ACS12.Pressure

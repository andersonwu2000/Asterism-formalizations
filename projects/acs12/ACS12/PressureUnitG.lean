import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! The original fixed-ratio unit mass gap, with monotonicity in the physical exponent. -/
namespace ACS12.Pressure

open Set

private noncomputable def pairPowerMean (r x : ℝ) : ℝ := ((1 + x ^ r) / 2) ^ (1 / r)

private theorem pairPowerMean_mono_order {r R x : ℝ} (hr : 0 < r) (hR : r ≤ R) (hx : 0 < x) :
    pairPowerMean r x ≤ pairPowerMean R x := by
  have hR₀ := hr.trans_le hR
  have hρ : 1 ≤ R / r := (one_le_div hr).mpr hR
  have hx₀ := Real.rpow_pos_of_pos hx r
  have h := (convexOn_rpow hρ).2 (mem_Ici.mpr zero_le_one) (mem_Ici.mpr hx₀.le)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num)
  simp only [smul_eq_mul,mul_one,Real.one_rpow,← Real.rpow_mul hx.le] at h
  have hE : r * (R / r) = R := by field_simp [hr.ne']
  rw [hE] at h
  have h' : ((1 + x ^ r) / 2) ^ (R / r) ≤ (1 + x ^ R) / 2 := by
    convert h using 1 <;> ring
  have hP := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity : 0 ≤ (1 + x ^ r) / 2) _)
    h' (one_div_pos.mpr hR₀).le
  unfold pairPowerMean
  rw [← Real.rpow_mul (by positivity : 0 ≤ (1 + x ^ r) / 2),
    show (R / r) * (1 / R) = 1 / r by field_simp [hr.ne',hR₀.ne']] at hP
  exact hP

private theorem pairPowerMean_gap_antitone {r : ℝ} (hr : 1 ≤ r) :
    AntitoneOn (fun x => pairPowerMean r x - (1 + x) / 2) (Ioc 0 1) := by
  have hr₀ := zero_lt_one.trans_le hr
  let F (x : ℝ) := pairPowerMean r x - (1 + x) / 2
  let A (x : ℝ) := (1 + x ^ r) / 2
  have hD (x : ℝ) (hx : 0 < x) : HasDerivAt F
      (x ^ (r - 1) * A x ^ (1 / r - 1) / 2 - 1 / 2) x := by
    have h := (((Real.hasDerivAt_rpow_const (p := r) (Or.inl hx.ne')).const_add 1).div_const 2)
    have hA : 0 < A x := by unfold A; positivity
    convert (h.rpow_const (p := 1 / r) (Or.inl hA.ne')).sub
      (((hasDerivAt_id x).const_add 1).div_const 2) using 1
    field_simp [hr₀.ne']
    ring
  apply antitoneOn_of_deriv_nonpos (convex_Ioc _ _)
    (fun x hx => (hD x hx.1).continuousAt.continuousWithinAt)
    (fun x hx => (hD x (interior_subset hx).1).differentiableAt.differentiableWithinAt)
  intro x hx
  have hx' := interior_subset hx
  have hA : 0 < A x := by unfold A; have := hx'.1; positivity
  have hR : x ^ r ≤ A x := by
    have h := Real.rpow_le_one hx'.1.le hx'.2 hr₀.le
    unfold A
    linarith only [h]
  have hP := Real.rpow_le_rpow (Real.rpow_nonneg hx'.1.le r) hR
    (show 0 ≤ (r - 1) / r by exact div_nonneg (sub_nonneg.mpr hr) hr₀.le)
  rw [← Real.rpow_mul hx'.1.le,show r * ((r - 1) / r) = r - 1 by field_simp [hr₀.ne']] at hP
  have h := mul_le_mul_of_nonneg_right hP (Real.rpow_nonneg hA.le (1 / r - 1))
  rw [← Real.rpow_add hA,show (r - 1) / r + (1 / r - 1) = 0 by field_simp [hr₀.ne']; ring,
    Real.rpow_zero] at h
  rw [(hD x hx'.1).deriv]
  linarith only [h]

noncomputable def unitGapG (p z : ℝ) : ℝ :=
  Real.exp (-(p / (p + 1)) * z) *
    (Real.cosh (p * z) ^ (1 / (p + 1)) - Real.cosh ((p / (p + 1)) * z))

noncomputable def unitGapD (p z : ℝ) : ℝ :=
  Real.exp (-z) * (Real.cosh z - Real.cosh ((p - 1) * z) ^ (1 / (p + 1)))

private theorem expCosh_average (s : ℝ) : (1 + Real.exp (-2 * s)) / 2 = Real.exp (-s) * Real.cosh s := by
  rw [Real.cosh_eq]
  have hE : Real.exp (-s) * Real.exp s = 1 := by rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
  have hE' : Real.exp (-s) * Real.exp (-s) = Real.exp (-2 * s) := by rw [← Real.exp_add]; congr 1; ring
  linear_combination (-1 / 2) * hE - (1 / 2) * hE'

private theorem unitGapG_powerMean {p z : ℝ} (hp : 0 < p) :
    unitGapG p z =
      pairPowerMean (p + 1) (Real.exp (-2 * ((p / (p + 1)) * z))) -
        (1 + Real.exp (-2 * ((p / (p + 1)) * z))) / 2 := by
  let a : ℝ := 1 / (p + 1)
  let β : ℝ := p / (p + 1)
  have hE : Real.exp (-2 * (β * z)) ^ (p + 1) = Real.exp (-2 * (p * z)) := by
    rw [← Real.exp_mul]
    congr 1
    unfold β
    field_simp [show p + 1 ≠ 0 by positivity]
  unfold pairPowerMean
  change unitGapG p z = ((1 + Real.exp (-2 * (β * z)) ^ (p + 1)) / 2) ^ a -
    (1 + Real.exp (-2 * (β * z))) / 2
  rw [hE,expCosh_average,expCosh_average,Real.mul_rpow (Real.exp_pos _).le (Real.cosh_pos _).le,← Real.exp_mul]
  have hF : -(p * z) * a = -β * z := by unfold a β; ring
  rw [hF,show -(β * z) = -β * z by ring]
  unfold unitGapG
  change Real.exp (-β * z) * (Real.cosh (p * z) ^ a - Real.cosh (β * z)) = _
  ring

theorem unitGapG_mono {p P z : ℝ} (hp : 0 < p) (hP : p ≤ P) (hz : 0 ≤ z) :
    unitGapG p z ≤ unitGapG P z := by
  let β (t : ℝ) := t / (t + 1)
  let x (t : ℝ) := Real.exp (-2 * (β t * z))
  have hP₀ := hp.trans_le hP
  have hβ : β p ≤ β P := by
    unfold β
    apply (div_le_div_iff₀ (by positivity : 0 < p + 1) (by positivity : 0 < P + 1)).mpr
    nlinarith only [hP]
  have hX : x P ≤ x p := by
    unfold x
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (mul_le_mul_of_nonneg_right hβ hz) (by norm_num))
  have hX₀ (t : ℝ) : 0 < x t := Real.exp_pos _
  have hX₁ (t : ℝ) (ht : 0 < t) : x t ≤ 1 := by
    unfold x
    apply Real.exp_le_one_iff.mpr
    have h : 0 ≤ β t * z := by unfold β; positivity
    linarith only [h]
  rw [unitGapG_powerMean hp,unitGapG_powerMean hP₀]
  change pairPowerMean (p + 1) (x p) - (1 + x p) / 2 ≤
    pairPowerMean (P + 1) (x P) - (1 + x P) / 2
  have hOrder := pairPowerMean_mono_order (show 0 < p + 1 by positivity) (add_le_add_left hP 1) (hX₀ p)
  have hM := pairPowerMean_gap_antitone (show 1 ≤ P + 1 by linarith only [hp,hP])
    (show x P ∈ Ioc 0 1 from ⟨hX₀ _,hX₁ _ hP₀⟩) ⟨hX₀ _,hX₁ _ hp⟩ hX
  exact (sub_le_sub_right hOrder _).trans hM

end ACS12.Pressure


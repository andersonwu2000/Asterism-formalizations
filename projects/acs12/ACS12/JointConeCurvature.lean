import ACS12.JointBoseReturnShape
import ACS12.JointGapK

/-! A complete exponential majorant for the curvature of the Bose head. -/
namespace ACS12.GammaMeasure

open CenteredCircle.AllN Polynomial Set
open BoseShape (expQuad expQuad_deriv)
open MeasureTheory Filter GammaDeficit
set_option maxRecDepth 4096

noncomputable def jointConeQ (x : ℝ) : ℝ := Real.exp (-x) * ((1 + x) / 6 + (47 / 500) * x ^ 2)

private noncomputable def coneCurvatureGuard (n : ℕ) (x : ℝ) : ℝ :=
  let A : ℝ := 47 / 500
  let jet (c a b d : ℝ) := expQuad c (c ^ n * a)
    (c ^ n * b + 2 * a * (n : ℝ) * c ^ (n - 1))
    (c ^ n * d + b * (n : ℝ) * c ^ (n - 1) +
      a * (n : ℝ) * ((n : ℝ) - 1) * c ^ (n - 2)) x
  jet 3 A (-5 / 6) (13 / 6) + jet 2 (-3 * A) (-3 / 2) (-5 / 2) +
    jet 1 (3 * A) (1 / 2) (1 / 2) -
    ((derivative^[n] (C A * X ^ 2 + C (1 / 6) * X + C (1 / 6) : ℝ[X])).eval x)

private theorem coneCurvatureGuard_deriv (n : ℕ) (x : ℝ) :
    HasDerivAt (coneCurvatureGuard n) (coneCurvatureGuard (n + 1) x) x := by
  let A : ℝ := 47 / 500
  have h (c a b d : ℝ) :
      HasDerivAt (expQuad c (c ^ n * a)
        (c ^ n * b + 2 * a * (n : ℝ) * c ^ (n - 1))
        (c ^ n * d + b * (n : ℝ) * c ^ (n - 1) +
          a * (n : ℝ) * ((n : ℝ) - 1) * c ^ (n - 2)))
        (expQuad c (c ^ (n + 1) * a)
          (c ^ (n + 1) * b + 2 * a * ((n + 1 : ℕ) : ℝ) * c ^ (n + 1 - 1))
          (c ^ (n + 1) * d + b * ((n + 1 : ℕ) : ℝ) * c ^ (n + 1 - 1) +
            a * ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) - 1) * c ^ (n + 1 - 2)) x) x := by
    convert expQuad_deriv c (c ^ n * a)
      (c ^ n * b + 2 * a * (n : ℝ) * c ^ (n - 1))
      (c ^ n * d + b * (n : ℝ) * c ^ (n - 1) +
        a * (n : ℝ) * ((n : ℝ) - 1) * c ^ (n - 2)) x using 1
    rcases lt_or_ge n 2 with hn | hn
    · interval_cases n <;> simp [expQuad] <;> ring
    · have h₁ : n = n - 1 + 1 := by omega
      have h₂ : n - 1 = n - 2 + 1 := by omega
      simp only [expQuad,Nat.cast_succ,pow_succ,show n + 1 - 1 = n by omega,
        show n + 1 - 2 = n - 1 by omega]
      conv_lhs => rw [show c ^ n = c ^ (n - 1) * c by rw [← pow_succ,← h₁]]
      have hp₁ : c ^ n = c ^ (n - 1) * c := by rw [← pow_succ,← h₁]
      have hp₂ : c ^ (n - 1) = c ^ (n - 2) * c := by rw [← pow_succ,← h₂]
      rw [hp₁,hp₂]
      ring
  unfold coneCurvatureGuard
  simpa only [Function.iterate_succ_apply'] using
    ((((h 3 A (-5 / 6) (13 / 6)).add (h 2 (-3 * A) (-3 / 2) (-5 / 2))).add
      (h 1 (3 * A) (1 / 2) (1 / 2))).sub
        (((derivative^[n] (C A * X ^ 2 + C (1 / 6) * X + C (1 / 6) : ℝ[X])).hasDerivAt x)))

private theorem coneCurvatureGuard_pos {x : ℝ} (hx : 0 < x) : 0 < coneCurvatureGuard 0 x := by
  have hP (j : ℕ) (hj : 3 ≤ j) :
      derivative^[j] (C (47 / 500 : ℝ) * X ^ 2 + C (1 / 6) * X + C (1 / 6)) = 0 := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [add_comm,Function.iterate_add_apply]
    norm_num [Function.iterate_succ_apply',derivative_add,derivative_C_mul]
  have hC (j : ℕ) (hj : j < 18) : 0 ≤ coneCurvatureGuard j 0 := by
    interval_cases j <;>
      norm_num [coneCurvatureGuard,expQuad,Function.iterate_succ_apply',derivative_add,derivative_C_mul]
  have hN (t : ℝ) (ht : 0 < t) : 0 < coneCurvatureGuard 18 t := by
    have he : Real.exp (2 * t) ≤ Real.exp (3 * t) := Real.exp_le_exp.mpr (by linarith only [ht])
    norm_num [coneCurvatureGuard,expQuad,hP 18 (by decide)]
    have hp : 0 ≤ 1231192064 / 125 + 215482368 / 125 * t + 9240576 / 125 * t ^ 2 := by positivity
    have hPay := mul_le_mul_of_nonneg_left he hp
    have hRem := mul_pos (show 0 <
      (17563062168 / 125 - 1231192064 / 125) +
        (28539976023 / 250 - 215482368 / 125) * t +
        (18208762983 / 500 - 9240576 / 125) * t ^ 2 by
      norm_num
      positivity) (Real.exp_pos (3 * t))
    have hR := mul_nonneg (show 0 ≤ 141 / 500 * t ^ 2 + 2663 / 250 * t + 11974 / 125 by positivity)
      (Real.exp_pos t).le
    nlinarith only [hPay,hRem,hR]
  have hDesc (k : ℕ) (hk : k ≤ 18) : ∀ t > 0, 0 < coneCurvatureGuard (18 - k) t := by
    induction k with
    | zero => exact fun t ht => hN t ht
    | succ k ih =>
      have hidx : 18 - (k + 1) + 1 = 18 - k := by omega
      intro t ht
      have h := BoseShape.positive_of_derivative (f := fun x =>
          coneCurvatureGuard (18 - (k + 1)) x - coneCurvatureGuard (18 - (k + 1)) 0)
        (d := coneCurvatureGuard (18 - k)) (sub_self _)
        (fun x => by rw [← hidx]; exact (coneCurvatureGuard_deriv _ x).sub_const _)
        (ih (by omega)) ht
      linarith only [h,hC (18 - (k + 1)) (by omega)]
  exact hDesc 18 le_rfl x hx

theorem boseC_exp_upper {x : ℝ} (hx : 0 < x) :
    BoseShape.C x ≤ Real.exp (-x / 3) / 2 := by
  have hE : Real.exp (-(2 / 3) * x) * Real.exp (x / 3) = Real.exp (-x / 3) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (x / 3))
    (show 0 ≤ Real.exp (-(2 / 3) * x) / 2 by positivity)
  have h' := boseC_le_decaySharp hx
  rw [show Real.exp (-(2 / 3) * x) / 2 * Real.exp (x / 3) =
    Real.exp (-(2 / 3) * x) * Real.exp (x / 3) / 2 by ring,hE] at h
  nlinarith only [h,h']

theorem boseCurvature_cone_le {x : ℝ} (hx : 0 < x) :
    -BoseShape.C₁ x ≤ jointConeQ x := by
  have h := coneCurvatureGuard_pos hx
  have hD : 0 < 1 - Real.exp (-x) := expHead_den_pos hx
  have hE : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
  rw [BoseShape.neg_C₁_eq hx]
  apply (div_le_iff₀ (pow_pos hD 3)).mpr
  have hGuard : jointConeQ x * (1 - Real.exp (-x)) ^ 3 -
      Real.exp (-x) * ((x - 2) + (x + 2) * Real.exp (-x)) =
      Real.exp (-4 * x) * coneCurvatureGuard 0 x := by
    norm_num [jointConeQ,coneCurvatureGuard,expQuad,Function.iterate_zero_apply,eval_add,eval_mul,eval_C,eval_pow,eval_X]
    rw [show -(4 * x) = ((4 : ℕ) : ℝ) * (-x) by norm_num,Real.exp_nat_mul,
      show (3 : ℝ) * x = ((3 : ℕ) : ℝ) * x by norm_num,Real.exp_nat_mul,
      show (2 : ℝ) * x = ((2 : ℕ) : ℝ) * x by norm_num,Real.exp_nat_mul]
    have hInv : Real.exp x = (Real.exp (-x))⁻¹ :=
      (eq_div_iff (Real.exp_ne_zero (-x))).mpr hE |>.trans (one_div _)
    rw [hInv]
    generalize hE' : Real.exp (-x) = y at *
    have hy : y ≠ 0 := hE' ▸ Real.exp_ne_zero (-x)
    field_simp [hy]
    ring
  exact sub_nonneg.mp (hGuard.symm ▸ (mul_pos (Real.exp_pos _) h).le)


private theorem pureC_shift_moment_le {p r b : ℝ} (hp : 0 < p) (hr : 0 < r) (hb : 0 < b) :
    (∫ x : ℝ in Ioi 0, lineDensity p x * x ^ 2 * Real.exp (-x * b) * BoseShape.C (r * x)) ≤
      (p * (p + 1) / 2) * (b + r / 3) ^ (-(p + 2)) := by
  let f (x : ℝ) := lineDensity p x * x ^ 2 * Real.exp (-x * b) * BoseShape.C (r * x)
  let g (x : ℝ) := (1 / 2 : ℝ) * (lineDensity p x * x ^ 2 * Real.exp (-x * (b + r / 3)))
  have hRate : 0 < b + r / 3 := by positivity
  obtain ⟨hG,hGE⟩ := lineDensity_moment hp hRate 2
  have hg : IntegrableOn g (Ioi 0) := hG.const_mul (1 / 2)
  have hPoint (x : ℝ) (hx : 0 < x) : 0 ≤ f x ∧ f x ≤ g x := by
    have hC := boseC_exp_upper (mul_pos hr hx)
    have hW : 0 ≤ lineDensity p x * x ^ 2 * Real.exp (-x * b) :=
      mul_nonneg (mul_nonneg (lineDensity_pos hp hx).le (sq_nonneg _)) (Real.exp_pos _).le
    refine ⟨mul_nonneg hW (BoseShape.C_pos (mul_pos hr hx)).le,?_⟩
    have h := mul_le_mul_of_nonneg_left hC hW
    have hExp : Real.exp (-x * b) * Real.exp (-(r * x) / 3) = Real.exp (-x * (b + r / 3)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    unfold f g
    calc
      _ ≤ lineDensity p x * x ^ 2 * Real.exp (-x * b) * (Real.exp (-(r * x) / 3) / 2) := h
      _ = _ := by rw [← hExp]; ring
  have hf : IntegrableOn f (Ioi 0) := by
    have hfM : Measurable f := by unfold f lineDensity BoseShape.C; fun_prop
    apply hg.mono' hfM.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_of_nonneg (hPoint x hx).1]
    exact (hPoint x hx).2
  have h := setIntegral_mono_on hf hg measurableSet_Ioi fun x hx => (hPoint x hx).2
  unfold g at h
  rw [integral_const_mul,hGE] at h
  have hΓ : Real.Gamma (p + 2) = p * (p + 1) * Real.Gamma p := by
    rw [show p + 2 = (p + 1) + 1 by ring,Real.Gamma_add_one (by positivity : 0 < p + 1).ne',
      Real.Gamma_add_one hp.ne']
    ring
  norm_num only [Nat.cast_ofNat] at h
  rw [hΓ] at h
  convert h using 1
  field_simp [(Real.Gamma_pos_of_pos hp).ne']

theorem jointCone_negative_part_le {p b r : ℝ} (hp : 1 ≤ p)
    (hb : 0 < b) (hbU : b ≤ 13 / 6) (hr : 17 / 20 ≤ r) :
    (∫ x : ℝ in Ioi 0, lineDensity p x * x ^ 2 * Real.exp (-x * b) * BoseShape.C (r * x)) ≤
      (1 / 2) * (130 / 147 : ℝ) ^ (p + 2) * (p * (p + 1) * b ^ (-(p + 2))) := by
  have hr₀ : 0 < r := (by norm_num : (0 : ℝ) < 17 / 20).trans_le hr
  have h := pureC_shift_moment_le (zero_lt_one.trans_le hp) hr₀ hb
  have hRatio : 0 < b / (b + r / 3) := div_pos hb (by positivity)
  have hR : b / (b + r / 3) ≤ (130 / 147 : ℝ) :=
    (div_le_iff₀ (by positivity : 0 < b + r / 3)).mpr (by linarith only [hbU,hr])
  have hB : b ^ (-(p + 2)) * (b / (b + r / 3)) ^ (p + 2) = (b + r / 3) ^ (-(p + 2)) := by
    rw [Real.div_rpow hb.le (by positivity),Real.rpow_neg hb.le,← mul_div_assoc,
      inv_mul_cancel₀ (Real.rpow_pos_of_pos hb _).ne',one_div,← Real.rpow_neg (by positivity)]
  rw [← hB] at h
  have hB' := Real.rpow_le_rpow hRatio.le hR (show 0 ≤ p + 2 by positivity)
  have hF := mul_le_mul_of_nonneg_left hB'
    (show 0 ≤ p * (p + 1) / 2 * b ^ (-(p + 2)) by positivity)
  exact h.trans (by nlinarith only [hF])

end ACS12.GammaMeasure


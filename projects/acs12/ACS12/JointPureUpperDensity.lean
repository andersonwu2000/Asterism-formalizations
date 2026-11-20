import ACS12.JointFrequencyGuards
import ACS12.OuterPureDensity

/-! Full positive frequency scaling for the fixed pure upper corner in G23–30. -/
namespace ACS12.GammaMeasure

open CenteredCircle.AllN Polynomial Set
open BoseShape (expQuad expQuad_deriv)

noncomputable def jointPureLambda : ℝ := 89 / 500

noncomputable def jointPureR (mu u s : ℝ) : ℝ :=
  middleRightDensity u s - jointPureLambda * polyB (u * s) -
    mu * Real.exp (-s * u) * polyB (u * s)

theorem jointPureR_one_bounds {mu s : ℝ} (hmu : 0 ≤ mu) (hmuU : mu ≤ 9 / 500) (hs : 0 < s) :
    0 < jointPureR mu 1 s ∧ jointPureR mu 1 s ≤ s := by
  let X := Real.exp (-s)
  have hE : jointPureR mu 1 s =
      (1 - jointPureLambda - mu * X) * polyB s - (6 / 25) * s * (1 - X) := by
    simp only [jointPureR, middleRightDensity, middleA0, middleZ, middleA, polyB, mul_one, one_mul, X]
    ring
  have hX₀ : 0 < X := Real.exp_pos _
  have hX₁ : X ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.le)
  have h := mul_le_of_le_one_right hmu hX₁
  have hPos := mul_pos (show 0 < 1 - jointPureLambda - mu * X - 12 / 25 by
    unfold jointPureLambda; linarith only [h,hmuU]) (polyB_pos hs)
  have hLoss := mul_le_mul_of_nonneg_left (polyB_elasticity hs.le) (by norm_num : (0 : ℝ) ≤ 6 / 25)
  have hMu := mul_nonneg hmu hX₀.le
  have hB : polyB s ≤ s := by unfold polyB; linarith only [hX₁]
  have hU := mul_le_mul_of_nonneg_right
    (show 1 - jointPureLambda - mu * X ≤ 1 by unfold jointPureLambda; linarith only [hMu]) (polyB_pos hs).le
  have hN := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6 / 25) hs.le) (sub_nonneg.mpr hX₁)
  rw [hE]
  exact ⟨by nlinarith only [hPos,hLoss], by nlinarith only [hU,hB,hN]⟩

theorem jointPureR_scale_bound {mu u s : ℝ} (hmu : 0 ≤ mu) (hu : 0 < u) (hu₁ : u ≤ 1) (hs : 0 < s) :
    jointPureR mu u s ≤ u ^ 2 * jointPureR mu 1 s + (1 - u) * outerK u s := by
  have hR : middleRightDensity u s =
      u ^ 2 * middleRightDensity 1 s + (1 - u) * outerK u s := by
    simp only [middleRightDensity, middleA0, middleZ, middleA, outerK]
    ring
  have hB := polyB_scale_lower hu hu₁ hs
  have hX : Real.exp (-s) ≤ Real.exp (-s * u) :=
    Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left hu₁ hs.le])
  have h₁ := mul_le_mul_of_nonneg_left hB (by norm_num [jointPureLambda] : 0 ≤ jointPureLambda)
  have h₂ := mul_le_mul hX hB (mul_nonneg (sq_nonneg u) (polyB_pos hs).le) (Real.exp_pos _).le
  have h₃ := mul_le_mul_of_nonneg_left h₂ hmu
  unfold jointPureR
  rw [hR, one_mul, mul_one]
  nlinarith only [h₁,h₃]

private noncomputable def pureElasticityD (mu : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  expQuad 2 0 (2 ^ n * (19 / 25 - jointPureLambda))
    (2 ^ n * (-2 * (1 - jointPureLambda) + (n : ℝ) / 2 * (19 / 25 - jointPureLambda))) s +
  expQuad 1 (6 / 25 - mu) (31 / 25 - jointPureLambda + 2 * n * (6 / 25 - mu))
    (2 * (1 - jointPureLambda + mu) + n * (31 / 25 - jointPureLambda) +
      (n : ℝ) * (n - 1) * (6 / 25 - mu)) s

private noncomputable def pureElasticityCoeff (mu : ℝ) (j : ℕ) : ℝ :=
  match j with
  | 0 => 2 * mu
  | 1 => 2 * mu
  | 2 => 0
  | 3 => (7 / 25 - jointPureLambda - 4 * mu) / 6
  | 4 => (54 / 25 - 6 * jointPureLambda - 10 * mu) / 24
  | _ => (49 / 5 - 23 * jointPureLambda - 18 * mu) / 120

private noncomputable def pureElasticityP (mu : ℝ) : ℝ[X] :=
  ∑ j ∈ Finset.range 6, C (pureElasticityCoeff mu j) * X ^ j

private theorem pureElasticityP_coeff (mu : ℝ) (n : ℕ) :
    (pureElasticityP mu).coeff n = if n < 6 then pureElasticityCoeff mu n else 0 := by
  unfold pureElasticityP
  simp only [finsetSum_coeff, coeff_C_mul_X_pow]
  by_cases h : n < 6
  · rw [if_pos h, Finset.sum_eq_single n]
    · simp
    · intro j hj hne
      simp [Ne.symm hne]
    · exact fun hn => False.elim (hn (Finset.mem_range.mpr h))
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro j hj
    rw [if_neg (by rintro rfl; exact h (Finset.mem_range.mp hj))]

private theorem pureElasticity_start (mu : ℝ) (n : ℕ) (hn : n < 6) :
    pureElasticityD mu n 0 = (derivative^[n] (pureElasticityP mu)).eval 0 := by
  rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative, zero_add, Nat.descFactorial_self,
    pureElasticityP_coeff, if_pos hn, nsmul_eq_mul]
  interval_cases n <;> norm_num [pureElasticityD, expQuad, pureElasticityCoeff, jointPureLambda, Nat.factorial] <;> ring

set_option maxHeartbeats 400000 in
private theorem pureElasticity_pos {mu s : ℝ} (hmu : 0 ≤ mu) (hmuU : mu ≤ 9 / 500) (hs : 0 < s) :
    0 < ((19 / 25 - jointPureLambda) * s - 2 * (1 - jointPureLambda)) * Real.exp (2 * s) +
      (2 * (1 - jointPureLambda + mu) + (31 / 25 - jointPureLambda) * s + (6 / 25 - mu) * s ^ 2) *
        Real.exp s - 2 * mu * (s + 1) := by
  have hd (n : ℕ) (t : ℝ) : HasDerivAt (pureElasticityD mu n) (pureElasticityD mu (n + 1) t) t := by
    unfold pureElasticityD
    convert (expQuad_deriv 2 0 (2 ^ n * (19 / 25 - jointPureLambda))
      (2 ^ n * (-2 * (1 - jointPureLambda) + (n : ℝ) / 2 * (19 / 25 - jointPureLambda))) t).add
      (expQuad_deriv 1 (6 / 25 - mu) (31 / 25 - jointPureLambda + 2 * n * (6 / 25 - mu))
        (2 * (1 - jointPureLambda + mu) + n * (31 / 25 - jointPureLambda) +
          (n : ℝ) * (n - 1) * (6 / 25 - mu)) t) using 1
    simp only [expQuad, pow_succ, Nat.cast_add, Nat.cast_one]
    ring
  have hN (t : ℝ) (ht : 0 < t) : (derivative^[6] (pureElasticityP mu)).eval t < pureElasticityD mu 6 t := by
    have hP₀ : (derivative^[6] (pureElasticityP mu)) = 0 := by
      ext j
      rw [coeff_iterate_derivative, pureElasticityP_coeff, if_neg (by omega), smul_zero, coeff_zero]
    have hP : (derivative^[6] (pureElasticityP mu)).eval t = 0 := by rw [hP₀, eval_zero]
    rw [hP]
    norm_num [pureElasticityD, expQuad, jointPureLambda]
    have hA : 0 < (4656 / 125 : ℝ) * t + 816 / 125 := by positivity
    have hB : 0 ≤ (6 / 25 - mu) * t ^ 2 + ((531 / 500) + 12 * (6 / 25 - mu)) * t +
        (2 * (411 / 500 + mu) + 6 * (531 / 500) + 30 * (6 / 25 - mu)) := by
      have hm := show 0 ≤ 6 / 25 - mu by linarith only [hmuU]
      nlinarith only [hmu,hmuU,ht,mul_nonneg hm (sq_nonneg t),mul_nonneg hm ht.le]
    have h := add_pos_of_pos_of_nonneg (mul_pos hA (Real.exp_pos (2 * t))) (mul_nonneg hB (Real.exp_pos t).le)
    linear_combination h
  have hR := expGuard_remainder (pureElasticity_start mu) hd hN hs
  norm_num [pureElasticityD, expQuad, pureElasticityP, pureElasticityCoeff, Finset.sum_range_succ] at hR
  have h₃ := mul_pos (show 0 < (7 / 25 - jointPureLambda - 4 * mu) / 6 by unfold jointPureLambda; linarith only [hmuU])
    (pow_pos hs 3)
  have h₄ := mul_nonneg (show 0 ≤ (54 / 25 - 6 * jointPureLambda - 10 * mu) / 24 by unfold jointPureLambda; linarith only [hmuU])
    (pow_nonneg hs.le 4)
  have h₅ := mul_nonneg (show 0 ≤ (49 / 5 - 23 * jointPureLambda - 18 * mu) / 120 by unfold jointPureLambda; linarith only [hmuU])
    (pow_nonneg hs.le 5)
  linear_combination hR + h₃ + h₄ + h₅

private theorem pureElasticity_derivative (mu s : ℝ) :
    HasDerivAt (jointPureR mu 1)
      ((19 / 25 - jointPureLambda) + Real.exp (-s) *
        ((6 / 25 - mu) - (1 - jointPureLambda + mu) - (6 / 25 - mu) * s) +
        2 * mu * Real.exp (-s) ^ 2) s := by
  have h := hasDerivAt_id s
  have hX := (hasDerivAt_neg s).exp
  have hL := (h.const_mul (19 / 25 - jointPureLambda)).sub_const (1 - jointPureLambda)
  have hP := ((h.const_mul (6 / 25 - mu)).const_add (1 - jointPureLambda + mu)).mul hX
  convert (hL.add hP).sub ((hX.pow 2).const_mul mu) using 1
  · funext t
    simp only [jointPureR, middleRightDensity, middleA0, middleZ, middleA, polyB, Pi.add_apply, Pi.sub_apply,
      Pi.mul_apply, Pi.pow_apply, id_eq, one_mul, mul_one]
    ring
  · simp only [id_eq, mul_one, show (2 - 1 : ℕ) = 1 by decide, pow_one]
    ring

theorem jointPureR_one_scale_le {mu t s : ℝ} (hmu : 0 ≤ mu) (hmuU : mu ≤ 9 / 500)
    (ht : 0 < t) (ht₁ : t ≤ 1) (hs : 0 < s) :
    jointPureR mu 1 (s / t) ≤ t⁻¹ ^ 2 * jointPureR mu 1 s := by
  let R := jointPureR mu 1
  let d (x : ℝ) := (19 / 25 - jointPureLambda) + Real.exp (-x) *
    ((6 / 25 - mu) - (1 - jointPureLambda + mu) - (6 / 25 - mu) * x) + 2 * mu * Real.exp (-x) ^ 2
  have hF (x : ℝ) (hx : 0 < x) : 0 < 2 * R x - x * d x := by
    have hX : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hX₂ : Real.exp (2 * x) * Real.exp (-x) ^ 2 = 1 := by
      rw [two_mul, Real.exp_add, ← sq, ← mul_pow, hX, one_pow]
    have hX₁ : Real.exp (2 * x) * Real.exp (-x) = Real.exp x := by
      rw [two_mul, Real.exp_add, mul_assoc, hX, mul_one]
    have hE : (2 * R x - x * d x) * Real.exp (2 * x) =
        ((19 / 25 - jointPureLambda) * x - 2 * (1 - jointPureLambda)) * Real.exp (2 * x) +
        (2 * (1 - jointPureLambda + mu) + (31 / 25 - jointPureLambda) * x + (6 / 25 - mu) * x ^ 2) *
          Real.exp x - 2 * mu * (x + 1) := by
      simp only [R, d, jointPureR, middleRightDensity, middleA0, middleZ, middleA, polyB, one_mul, mul_one]
      linear_combination
        (2 * (1 - jointPureLambda + mu) + (31 / 25 - jointPureLambda) * x + (6 / 25 - mu) * x ^ 2) * hX₁ -
        2 * mu * (x + 1) * hX₂
    exact pos_of_mul_pos_left (hE.symm ▸ pureElasticity_pos hmu hmuU hx) (Real.exp_pos _).le
  let f (x : ℝ) := R x / x ^ 2
  have hd (x : ℝ) (hx : 0 < x) : HasDerivAt f ((x * d x - 2 * R x) / x ^ 3) x := by
    convert (pureElasticity_derivative mu x).div ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 hx.ne') using 1
    simp only [Pi.pow_apply, id_eq, show (2 - 1 : ℕ) = 1 by decide, pow_one, mul_one]
    change _ = (d x * x ^ 2 - R x * (2 * x)) / (x ^ 2) ^ 2
    field_simp [hx.ne']
  have hM : AntitoneOn f (Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi _)
    · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
    · exact fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : 0 < x := interior_subset hx
      rw [(hd x hx').deriv]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith only [hF x hx']) (by positivity)
  have h := hM hs (div_pos hs ht) ((le_div_iff₀ ht).mpr (mul_le_of_le_one_right hs.le ht₁))
  change R (s / t) / (s / t) ^ 2 ≤ R s / s ^ 2 at h
  have hL := (div_le_div_iff₀ (by positivity : 0 < (s / t) ^ 2) (sq_pos_of_pos hs)).mp h
  apply le_of_mul_le_mul_right _ (sq_pos_of_pos hs)
  calc
    _ ≤ R s * (s / t) ^ 2 := hL
    _ = _ := by rw [div_eq_mul_inv, mul_pow]; ring

end ACS12.GammaMeasure

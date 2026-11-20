import ACS12.SpeedMoments
import ACS12.GammaLawPath

/-! Transfer of the full speed moments to every original/interpolated law. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaDeficit (lineDensity)

private theorem speedKernel_abs_le {x : ℝ} (hx : 0 < x) :
    |diagonalSpeedKernel x| ≤
      (3 + 2 * BoseShape.decayConstant) * (1 + x + x ^ 2) * Real.exp (-x) := by
  have hA₀ := (polyA_pos hx).le
  have hA₁ : polyA x ≤ 1 := by
    unfold polyA
    exact sub_le_self _ (mul_nonneg (by linarith) (Real.exp_pos _).le)
  have hHead₀ : 0 ≤ expHeadFactor x := (div_pos hx (expHead_den_pos hx)).le
  have hHead₁ : expHeadFactor x ≤ x + 1 := by
    rw [expHeadFactor_eq_add_expTail hx]
    exact add_le_add le_rfl (BoseShape.expTail_bounds hx).2
  have hP : |-1 - 2 * x + x * expHeadFactor x| ≤ 3 * (1 + x + x ^ 2) := by
    rw [abs_le]
    constructor
    · nlinarith only [hx, sq_nonneg x, mul_nonneg hx.le hHead₀]
    · nlinarith only [hx, sq_nonneg x, mul_le_mul_of_nonneg_left hHead₁ hx.le]
  have hD := BoseShape.decayConstant_pos.le
  unfold diagonalSpeedKernel
  calc
    _ ≤ |Real.exp (-x) * (-1 - 2 * x + x * expHeadFactor x)| +
        |2 * polyA x * BoseShape.C x| := abs_sub _ _
    _ ≤ Real.exp (-x) * (3 * (1 + x + x ^ 2)) +
        2 * (BoseShape.decayConstant * (x + 1) * Real.exp (-x)) := by
      rw [abs_mul (Real.exp (-x)), abs_of_pos (Real.exp_pos _),
        abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA₀) (BoseShape.C_pos hx).le)]
      apply add_le_add (mul_le_mul_of_nonneg_left hP (Real.exp_pos _).le)
      calc
        2 * polyA x * BoseShape.C x ≤ 2 * 1 * BoseShape.C x :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA₁ (by norm_num)) (BoseShape.C_pos hx).le
        _ = 2 * BoseShape.C x := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (BoseShape.C_le_decay hx) (by norm_num)
    _ ≤ _ := by
      have h := mul_nonneg (mul_nonneg (sq_nonneg x) hD) (Real.exp_pos (-x)).le
      nlinarith only [h]

private theorem fixedMassSpeedKernel_abs_le {θ x : ℝ} (hx : 0 < x) (hθ : 0 ≤ θ)
    (hθ₁ : θ ≤ 1) :
    |fixedMassSpeedKernel θ x| ≤
      (4 + 2 * BoseShape.decayConstant) * (1 + x + x ^ 2) * Real.exp (-x) := by
  have hQ : |(1 - θ) * x - 1| ≤ 1 + x + x ^ 2 := by
    rw [abs_le]
    constructor
    · nlinarith only [mul_nonneg (sub_nonneg.mpr hθ₁) hx.le, hx, sq_nonneg x]
    · nlinarith only [mul_nonneg hθ hx.le, sq_nonneg x]
  have h := abs_add_le (diagonalSpeedKernel x) (Real.exp (-x) * ((1 - θ) * x - 1))
  unfold fixedMassSpeedKernel
  refine h.trans ?_
  rw [abs_mul (Real.exp (-x)), abs_of_pos (Real.exp_pos _)]
  have h' := add_le_add (speedKernel_abs_le hx) (mul_le_mul_of_nonneg_left hQ (Real.exp_pos (-x)).le)
  refine h'.trans_eq ?_
  ring

theorem lawDensity_linear_envelope {p L θ : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) :
    ∃ B ≥ 0, ∀ s > 0, |lawDensity p L θ s| ≤ B * (1 + s) := by
  have hp₀ := zero_lt_one.trans_le hp
  obtain ⟨D, hD, hBound⟩ := imageDensity_linear_bound hp₀ hp₂ hL
  let A := (Real.Gamma p)⁻¹
  have hA : 0 < A := inv_pos.mpr (Real.Gamma_pos_of_pos hp₀)
  refine ⟨A + D, by positivity, ?_⟩
  intro s hs
  have hPow : s ^ (p - 1) ≤ 1 + s := by
    rcases le_total s 1 with h | h
    · exact (show s ^ (p - 1) ≤ 1 by
        simpa only [Real.one_rpow] using Real.rpow_le_rpow hs.le h (sub_nonneg.mpr hp)).trans
          (le_add_of_nonneg_right hs.le)
    · exact (show s ^ (p - 1) ≤ s by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le h (by linarith : p - 1 ≤ 1)).trans
          (le_add_of_nonneg_left zero_le_one)
  have hRef : lineDensity p s ≤ A * (1 + s) := by
    unfold lineDensity
    rw [div_eq_mul_inv, mul_comm]
    exact mul_le_mul_of_nonneg_left hPow hA.le
  have hw : imageDensity p L s ≤ D * (1 + s) := (hBound s hs).trans
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) hD)
  rw [abs_of_pos (lawDensity_pos hp₀ hL hθ hs), lawDensity]
  calc
    _ ≤ (1 - θ) * (A * (1 + s)) + θ * (D * (1 + s)) :=
      add_le_add (mul_le_mul_of_nonneg_left hRef (sub_nonneg.mpr hθ.2))
        (mul_le_mul_of_nonneg_left hw hθ.1)
    _ ≤ A * (1 + s) + D * (1 + s) :=
      add_le_add (mul_le_of_le_one_left (by positivity) (by linarith [hθ.1]))
        (mul_le_of_le_one_left (by positivity) hθ.2)
    _ = _ := by ring

theorem lawDensity_measurable {p L θ : ℝ} (hp : 0 < p) (hL : 0 < L) :
    Measurable (lawDensity p L θ) := by
  unfold lawDensity
  have hρ : Measurable (lineDensity p) := by unfold lineDensity; fun_prop
  exact (hρ.const_mul _).add ((continuous_imageDensity hp hL).measurable.const_mul _)

private theorem speedProduct_integrable {w K : ℝ → ℝ} {B C v : ℝ}
    (hw : Measurable w) (hK : Measurable K) (hB : 0 ≤ B) (hC : 0 ≤ C) (hv : 0 < v)
    (hW : ∀ s > 0, |w s| ≤ B * (1 + s))
    (hN : ∀ x > 0, |K x| ≤ C * (1 + x + x ^ 2) * Real.exp (-x)) :
    IntegrableOn (fun s => w s * K (v * s)) (Ioi 0) := by
  let D := B * C * (1 + v + v ^ 2)
  have h0 := expMoment_nat_integrable 0 hv
  have h1 := (expMoment_nat_integrable 1 hv).const_mul 2
  have h2 := (expMoment_nat_integrable 2 hv).const_mul 2
  have h3 := expMoment_nat_integrable 3 hv
  have hI := (((h0.add h1).add h2).add h3).const_mul D
  have hMeas : Measurable (fun s => w s * K (v * s)) :=
    hw.mul (hK.comp (measurable_id.const_mul v))
  refine hI.mono' hMeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs₀ : 0 < s := hs
  have hvs := mul_pos hv hs₀
  have hArg : 1 + v * s + (v * s) ^ 2 ≤ (1 + v + v ^ 2) * (1 + s + s ^ 2) := by
    have h₀ : 0 ≤ v * s ^ 2 := by positivity
    have h₁ : 0 ≤ v ^ 2 * s := by positivity
    have h₂ : 0 ≤ v ^ 2 := by positivity
    nlinarith only [hv, hs₀, h₀, h₁, h₂, sq_nonneg s]
  rw [Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ B * (1 + s) * (C * (1 + v * s + (v * s) ^ 2) * Real.exp (-(v * s))) :=
      mul_le_mul (hW s hs₀) (hN (v * s) hvs) (abs_nonneg _) (by positivity)
    _ ≤ B * (1 + s) * (C * ((1 + v + v ^ 2) * (1 + s + s ^ 2)) * Real.exp (-(v * s))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hArg hC)
        (Real.exp_pos _).le) (by positivity)
    _ = _ := by
      simp only [Pi.add_apply, pow_zero, pow_one, D]
      rw [show -(v * s) = -s * v by ring]
      ring

private theorem speedIntegral_neg {K w : ℝ → ℝ} {v : ℝ} (hv : 0 < v)
    (hCut : NegativePositiveCut K) (hRef : (∫ x : ℝ in Ioi 0, x * K x) < 0)
    (hW : ∀ s > 0, 0 < w s) (hOrder : AntitoneOn (fun s => w s / s) (Ioi 0))
    (hInt : IntegrableOn (fun s => w s * K (v * s)) (Ioi 0)) :
    (∫ s : ℝ in Ioi 0, w s * K (v * s)) < 0 := by
  obtain ⟨c, hc, hBefore, _, hAfter⟩ := hCut
  let d := c / v
  have hd : 0 < d := div_pos hc hv
  have hdv : v * d = c := by dsimp [d]; field_simp
  let f (s : ℝ) := -(s * K (v * s))
  let g (s : ℝ) := w s / s
  have hScale : (∫ s : ℝ in Ioi 0, s * K (v * s)) =
      v⁻¹ * (v⁻¹ * ∫ x : ℝ in Ioi 0, x * K x) := by
    have he (s : ℝ) : s * K (v * s) = v⁻¹ * ((s * v) * K (s * v)) := by
      rw [mul_comm v s]
      field_simp [hv.ne']
    simp_rw [he]
    rw [integral_const_mul, integral_comp_mul_right_Ioi (fun x : ℝ => x * K x) 0 hv]
    simp only [zero_mul, smul_eq_mul]
  have hF : 0 < ∫ s : ℝ in Ioi 0, f s := by
    simp only [f, integral_neg, hScale]
    exact neg_pos.mpr (mul_neg_of_pos_of_neg (inv_pos.mpr hv) (mul_neg_of_pos_of_neg (inv_pos.mpr hv) hRef))
  have hE (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) : f s * g s = -(w s * K (v * s)) := by
    dsimp only [f, g]
    field_simp [(mem_Ioi.mp hs).ne']
  have hG := hInt.neg.congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hE s hs).symm)
  have h := positive_integral_of_one_cut hd (Integrable.of_integral_ne_zero hF.ne') hG
    (fun s hs => neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hs.1.le
      (hBefore (v * s) ⟨mul_pos hv hs.1, by
        have he := mul_lt_mul_of_pos_left hs.2 hv
        rwa [hdv] at he⟩).le))
    (fun s hs => neg_nonpos.mpr (mul_nonneg (hd.trans hs).le
      (hAfter (v * s) (by have he := mul_lt_mul_of_pos_left hs hv; rwa [hdv] at he)).le))
    hOrder (div_pos (hW d hd) hd) hF
  rw [setIntegral_congr_fun measurableSet_Ioi hE, integral_neg] at h
  exact neg_pos.mp h

theorem law_diagonal_speedIntegral_neg {p L θ v : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hv : 0 < v) :
    (∫ s : ℝ in Ioi 0, lawDensity p L θ s * diagonalSpeedKernel (v * s)) < 0 := by
  have hp₀ := zero_lt_one.trans_le hp
  obtain ⟨B, hB, hW⟩ := lawDensity_linear_envelope hp hp₂ hL hθ
  apply speedIntegral_neg hv diagonalSpeedKernel_cut diagonalSpeedKernel_moment_neg
    (fun s hs => lawDensity_pos hp₀ hL hθ hs) (lawDensity_div_antitone hp₀ hp₂ hL hθ)
  exact speedProduct_integrable (lawDensity_measurable hp₀ hL)
    (by unfold diagonalSpeedKernel expHeadFactor polyA BoseShape.C; fun_prop)
    hB (by linarith [BoseShape.decayConstant_pos]) hv hW (fun _ hx => speedKernel_abs_le hx)

theorem law_fixed_mass_speedIntegral_neg {p L θ v q : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hv : 0 < v)
    (hq : 1 / 3 ≤ q) (hq₁ : q ≤ 1) :
    (∫ s : ℝ in Ioi 0, lawDensity p L θ s * fixedMassSpeedKernel q (v * s)) < 0 := by
  have hp₀ := zero_lt_one.trans_le hp
  have hq₀ : 0 ≤ q := by linarith
  obtain ⟨B, hB, hW⟩ := lawDensity_linear_envelope hp hp₂ hL hθ
  apply speedIntegral_neg hv (fixedMassSpeedKernel_cut hq₀ hq₁) (fixedMassSpeedKernel_moment_neg hq)
    (fun s hs => lawDensity_pos hp₀ hL hθ hs) (lawDensity_div_antitone hp₀ hp₂ hL hθ)
  exact speedProduct_integrable (lawDensity_measurable hp₀ hL)
    (by unfold fixedMassSpeedKernel diagonalSpeedKernel expHeadFactor polyA BoseShape.C; fun_prop)
    hB (by linarith [BoseShape.decayConstant_pos]) hv hW (fun _ hx => fixedMassSpeedKernel_abs_le hx hq₀ hq₁)

end ACS12.GammaMeasure


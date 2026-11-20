import ACS12.FourthBound

/-! Exact same-exponent Bose moments of the pure comparison law. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaDeficit (lineDensity gamma_exp_integral integrable_gamma_exp)
open scoped Topology

private theorem rpowBand_upper {p s : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hs : 0 < s) :
    s ^ (p - 1) ≤ 1 + s := by
  rcases le_total s 1 with h | h
  · exact (show s ^ (p - 1) ≤ 1 by
      simpa only [Real.one_rpow] using Real.rpow_le_rpow hs.le h (sub_nonneg.mpr hp)).trans
        (le_add_of_nonneg_right hs.le)
  · exact (show s ^ (p - 1) ≤ s by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le h (by linarith : p - 1 ≤ 1)).trans
        (le_add_of_nonneg_left zero_le_one)

private theorem rpow_mul_self {s : ℝ} (hs : 0 < s) (a : ℝ) :
    s ^ a * s = s ^ (a + 1) := by
  calc
    s ^ a * s = s ^ a * s ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = _ := (Real.rpow_add hs a 1).symm

private theorem polyB_le_self {s : ℝ} (hs : 0 < s) : polyB s ≤ s := by
  unfold polyB
  linarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.le)]

/-- Multiplying the reference B moment by e^(-k s) gives a shifted complete tail. -/
theorem pureBoseB_moment {p : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) (k : ℕ) :
    (∫ s : ℝ in Ioi 0, lineDensity p s * polyB s * Real.exp (-s * k) * BoseShape.C s) =
      ((k : ℝ) + 1) ^ (-p) + p * (p - 1) * powerTail (p + 1) (k + 1) -
        (k : ℝ) * p * (p + 1) * powerTail (p + 2) (k + 1) := by
  have hp₀ : 0 < p := zero_lt_one.trans_le hp
  have hG : 0 < Real.Gamma p := Real.Gamma_pos_of_pos hp₀
  let m : ℕ := k + 1
  let d : ℝ := (m : ℝ)
  have hd : 0 < d := by dsimp only [d, m]; positivity
  have hm : 0 < m := by dsimp only [m]; omega
  let f (s : ℝ) := s ^ (p - 1) * polyB s * Real.exp (-s * k)
  let f' (s : ℝ) := ((p - 1) * s ^ (p - 2) * polyB s +
    s ^ (p - 1) * (1 - Real.exp (-s) - k * polyB s)) * Real.exp (-s * k)
  let β := expTailFactor
  have hD (s : ℝ) (hs : 0 < s) : HasDerivAt f (f' s) s := by
    have hP := Real.hasDerivAt_rpow_const (p := p - 1) (Or.inl hs.ne')
    have hX := ((hasDerivAt_id s).const_mul (-(k : ℝ))).exp
    convert (hP.mul (hasDerivAt_polyB s)).mul hX using 1
    · funext x
      dsimp only [f, Pi.mul_apply, id_eq]
      rw [mul_comm (-(k : ℝ)) x, show x * -(k : ℝ) = -x * k by ring]
    · simp only [f', Pi.mul_apply, id_eq, mul_one, show p - 1 - 1 = p - 2 by ring,
        show -(k : ℝ) * s = -s * k by ring]
      ring
  have hExp (s : ℝ) (hs : 0 < s) : Real.exp (-s * k) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) (Nat.cast_nonneg _))
  have hFP (s : ℝ) (hs : 0 < s) : 0 ≤ f s :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hs.le _) (polyB_pos hs).le) (Real.exp_pos _).le
  have hZero : Tendsto (f * β) (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hC : Continuous (fun s : ℝ => s ^ 2) := by fun_prop
    have ht : Tendsto (fun s : ℝ => s ^ 2) (𝓝[>] 0) (𝓝 0) := by
      simpa only [zero_pow (by decide : 2 ≠ 0)] using
        (hC.continuousAt (x := (0 : ℝ))).tendsto.mono_left
          (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ ht
    filter_upwards [self_mem_nhdsWithin,
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0) (Iio_mem_nhds zero_lt_one)] with s hs hs₁
    have hs₀ : 0 < s := hs
    obtain ⟨hb₀, hb₁⟩ := BoseShape.expTail_bounds hs₀
    have hP : s ^ (p - 1) ≤ 1 := by
      simpa only [Real.one_rpow] using Real.rpow_le_rpow hs₀.le hs₁.le (sub_nonneg.mpr hp)
    have hB : polyB s ≤ s ^ 2 := by
      have h := densityPolynomial_lt_quadratic .b hs₀
      change polyB s < s ^ 2 / 2 at h
      linarith [sq_nonneg s]
    rw [Pi.mul_apply, Real.norm_of_nonneg (mul_nonneg (hFP s hs₀) hb₀)]
    calc
      _ ≤ f s := mul_le_of_le_one_right (hFP s hs₀) hb₁
      _ ≤ s ^ (p - 1) * polyB s := mul_le_of_le_one_right
        (mul_nonneg (Real.rpow_nonneg hs₀.le _) (polyB_pos hs₀).le) (hExp s hs₀)
      _ ≤ polyB s := mul_le_of_le_one_left (polyB_pos hs₀).le hP
      _ ≤ _ := hB
  have hInf : Tendsto (f * β) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    let D := 1 - Real.exp (-1)
    have hD : 0 < D := expHead_den_pos zero_lt_one
    have hLim := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).const_mul D⁻¹
    simp only [mul_zero] at hLim
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hLim
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    have hs₀ := zero_lt_one.trans_le hs
    have hP : s ^ (p - 1) ≤ s := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hs (by linarith : p - 1 ≤ 1)
    have hβ : β s ≤ s * Real.exp (-s) / D := by
      change expTailFactor s ≤ _
      rw [BoseShape.expTail_eq_decay hs₀]
      exact div_le_div_of_nonneg_left (by positivity) hD
        (sub_le_sub_left (Real.exp_le_exp.mpr (neg_le_neg hs)) _)
    have hF : f s ≤ s ^ 2 := by
      calc
        _ ≤ s ^ (p - 1) * polyB s := mul_le_of_le_one_right
          (mul_nonneg (Real.rpow_nonneg hs₀.le _) (polyB_pos hs₀).le) (hExp s hs₀)
        _ ≤ s * s := mul_le_mul hP (polyB_le_self hs₀) (polyB_pos hs₀).le hs₀.le
        _ = _ := (sq s).symm
    rw [Pi.mul_apply, Real.norm_of_nonneg (mul_nonneg (hFP s hs₀) (BoseShape.expTail_bounds hs₀).1)]
    refine (mul_le_mul hF hβ (BoseShape.expTail_bounds hs₀).1 (sq_nonneg _)).trans_eq ?_
    ring
  have hCInt : IntegrableOn (f * fun s => -BoseShape.C s) (Ioi 0) := by
    have hM : Measurable (f * fun s => -BoseShape.C s) := by
      unfold f polyB BoseShape.C
      fun_prop
    have hI := integrable_cubic_exp_envelope zero_lt_one BoseShape.decayConstant
    refine hI.mono' hM.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0 < s := hs
    have hF : f s ≤ (1 + s) * s := by
      calc
        _ ≤ s ^ (p - 1) * polyB s := mul_le_of_le_one_right
          (mul_nonneg (Real.rpow_nonneg hs₀.le _) (polyB_pos hs₀).le) (hExp s hs₀)
        _ ≤ _ := mul_le_mul (rpowBand_upper hp hp₂ hs₀) (polyB_le_self hs₀) (polyB_pos hs₀).le (by positivity)
    rw [Pi.mul_apply, norm_mul, Real.norm_of_nonneg (hFP s hs₀), norm_neg,
      Real.norm_of_nonneg (BoseShape.C_pos hs₀).le, mul_one]
    refine (mul_le_mul hF (BoseShape.C_le_decay hs₀) (BoseShape.C_pos hs₀).le (by positivity)).trans ?_
    have hP : s * (s + 1) ≤ 1 + s + s ^ 2 := by nlinarith
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP
      (mul_nonneg BoseShape.decayConstant_pos.le (by positivity : 0 ≤ 1 + s))) (Real.exp_pos (-s)).le
    nlinarith only [h]
  let A (s : ℝ) := s ^ p * (Real.exp (-s * m) / (1 - Real.exp (-s)))
  let B (s : ℝ) := s ^ p * Real.exp (-s * d)
  let C (s : ℝ) := s ^ (p - 1) * Real.exp (-s * d)
  let J (s : ℝ) := s ^ (p + 1) * (Real.exp (-s * m) / (1 - Real.exp (-s)))
  let μ := volume.restrict (Ioi (0 : ℝ))
  have hA : Integrable A μ := boseMoment_integrable hp₀ hm
  have hB : Integrable B μ := by
    simpa only [B, μ, add_sub_cancel_right, neg_mul, mul_comm d] using
      integrable_gamma_exp (show 0 < p + 1 by positivity) hd
  have hC : Integrable C μ := by
    simpa only [C, μ, neg_mul, mul_comm d] using integrable_gamma_exp hp₀ hd
  have hJ : Integrable J μ := boseMoment_integrable (show 0 < p + 1 by positivity) hm
  have hPoint (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      (f' * β) s = (p - 1) * A s + (1 + k) * B s - (p - 1) * C s - k * J s := by
    have hs₀ : 0 < s := hs
    have hd0 := (expHead_den_pos hs₀).ne'
    have hpA : s ^ (p - 2) * s = s ^ (p - 1) := by
      rw [rpow_mul_self hs₀, show p - 2 + 1 = p - 1 by ring]
    have hpB : s ^ (p - 1) * s = s ^ p := by rw [rpow_mul_self hs₀, sub_add_cancel]
    have hpC : s ^ p * s = s ^ (p + 1) := rpow_mul_self hs₀ p
    have he : Real.exp (-s * d) = Real.exp (-s * k) * Real.exp (-s) := by
      rw [← Real.exp_add]
      congr 1
      simp only [d, m, Nat.cast_add, Nat.cast_one]
      ring
    have hb1 : s ^ (p - 1) * polyB s = s ^ p - s ^ (p - 1) * (1 - Real.exp (-s)) := by
      unfold polyB
      linear_combination hpB
    have hb2 : s ^ p * (1 - Real.exp (-s) - k * polyB s) =
        (1 + k) * s ^ p * (1 - Real.exp (-s)) - k * s ^ (p + 1) := by
      unfold polyB
      linear_combination -(k : ℝ) * hpC
    have h' : (f' * β) s =
        ((p - 1) * (s ^ (p - 2) * s) * polyB s +
          (s ^ (p - 1) * s) * (1 - Real.exp (-s) - k * polyB s)) *
            (Real.exp (-s * d) / (1 - Real.exp (-s))) := by
      simp only [Pi.mul_apply, f', β, BoseShape.expTail_eq_decay hs₀, he]
      field_simp [hd0]
    rw [h', hpA, hpB, mul_assoc (p - 1), hb1, hb2]
    dsimp only [A, B, C, J, d]
    field_simp [hd0]
    ring
  have hDerivInt : IntegrableOn (f' * β) (Ioi 0) := by
    apply ((((hA.const_mul (p - 1)).add (hB.const_mul (1 + (k : ℝ)))).sub
      (hC.const_mul (p - 1))).sub (hJ.const_mul k)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hPoint s hs).symm
  have hParts := integral_Ioi_mul_deriv_eq_deriv_mul (u := f) (u' := f') (v := β)
    (v' := fun s => -BoseShape.C s) (fun s hs => hD s hs) (fun s hs => BoseShape.expTail_derivative hs)
    hCInt hDerivInt hZero hInf
  have hEq : (∫ s : ℝ in Ioi 0, f s * BoseShape.C s) = ∫ s : ℝ in Ioi 0, (f' * β) s := by
    simpa only [mul_neg, integral_neg, sub_zero, zero_sub, neg_inj, Pi.mul_apply] using hParts
  have hP (s : ℝ) :
      lineDensity p s * polyB s * Real.exp (-s * k) * BoseShape.C s =
        (Real.Gamma p)⁻¹ * (f s * BoseShape.C s) := by
    unfold lineDensity f
    ring
  simp_rw [hP]
  rw [integral_const_mul, hEq, setIntegral_congr_fun measurableSet_Ioi hPoint,
    integral_four_terms hA hB hC hJ]
  have hB' : (∫ s : ℝ in Ioi 0, B s) = Real.Gamma (p + 1) * d ^ (-(p + 1)) := by
    simpa only [B, add_sub_cancel_right, neg_mul, mul_comm d] using
      gamma_exp_integral (show 0 < p + 1 by positivity) hd
  have hC' : (∫ s : ℝ in Ioi 0, C s) = Real.Gamma p * d ^ (-p) := by
    simpa only [C, neg_mul, mul_comm d] using gamma_exp_integral hp₀ hd
  have hA' : (∫ s : ℝ in Ioi 0, A s) = Real.Gamma (p + 1) * powerTail (p + 1) m :=
    boseMoment_integral hp₀ hm
  have hJ' : (∫ s : ℝ in Ioi 0, J s) = Real.Gamma (p + 2) * powerTail (p + 2) m := by
    simpa only [show p + 1 + 1 = p + 2 by ring] using
      boseMoment_integral (show 0 < p + 1 by positivity) hm
  have hGam1 := Real.Gamma_add_one hp₀.ne'
  have hGam2 : Real.Gamma (p + 2) = (p + 1) * Real.Gamma (p + 1) := by
    simpa only [show p + 1 + 1 = p + 2 by ring] using Real.Gamma_add_one (show p + 1 ≠ 0 by positivity)
  have hRate : (1 + (k : ℝ)) * d ^ (-(p + 1)) = d ^ (-p) := by
    rw [show 1 + (k : ℝ) = d by simp [d, m, add_comm],
      show -(p + 1) = -p - 1 by ring, Real.rpow_sub_one hd.ne']
    field_simp [hd.ne']
  have hProd : (1 + (k : ℝ)) * (Real.Gamma (p + 1) * d ^ (-(p + 1))) =
      (p * Real.Gamma p) * d ^ (-p) := by
    rw [hGam1, ← hRate]
    ring
  rw [hA', hB', hC', hJ', hProd, hGam2, hGam1]
  have hdK : d = (k : ℝ) + 1 := by simp [d, m]
  rw [← hdK]
  change _ = d ^ (-p) + p * (p - 1) * powerTail (p + 1) m -
    (k : ℝ) * p * (p + 1) * powerTail (p + 2) m
  field_simp [hG.ne']
  ring

end ACS12.GammaMeasure


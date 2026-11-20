import ACS12.OuterReturnSign

/-! Signed native transforms along the same actual-to-pure law. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaDeficit (lineDensity signedDensity)

theorem middleRightDensity_eq {u s : ℝ} (hs : 0 < s) :
    middleRightDensity u s = s * rightMultiplier (middleA u) (middleZ u) s := by
  unfold middleRightDensity middleA0 rightMultiplier
  field_simp [hs.ne'] <;> ring

noncomputable def lawRightDensity (p L θ u s : ℝ) : ℝ :=
  lawDensity p L θ s * middleRightDensity u s

noncomputable def lawRightTest (p L θ u : ℝ) : ℝ → ℝ :=
  signedLaplace (lawRightDensity p L θ u)

theorem lawRightDensity_measurable {p L θ u : ℝ} (hp : 0 < p) (hL : 0 < L) :
    Measurable (lawRightDensity p L θ u) := by
  unfold lawRightDensity middleRightDensity middleA0
  exact (lawDensity_measurable hp hL).mul (by fun_prop)

theorem lawRightDensity_bound {p L θ u : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) :
    ∃ B ≥ 0, ∀ s > 0, |lawRightDensity p L θ u s| ≤ B * (s + s ^ 2) := by
  obtain ⟨B, hB, hW⟩ := lawDensity_linear_envelope hp hp₂ hL hθ
  let D := |middleZ u| + |middleA u| + 1
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨B * D, mul_nonneg hB hD, ?_⟩
  intro s hs
  rw [lawRightDensity, middleRightDensity_eq hs, abs_mul, abs_mul, abs_of_pos hs]
  calc
    _ ≤ B * (1 + s) * (s * D) :=
      mul_le_mul (hW s hs) (mul_le_mul_of_nonneg_left (rightMultiplier_bound _ _ hs) hs.le)
        (mul_nonneg hs.le (abs_nonneg _)) (by positivity)
    _ = _ := by ring

theorem lawRightDensity_integrable {p L θ u t : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (ht : 0 < t) :
    IntegrableOn (fun s => lawRightDensity p L θ u s * Real.exp (-s * t)) (Ioi 0) := by
  obtain ⟨B, _, hB⟩ := lawRightDensity_bound hp hp₂ hL hθ (u := u)
  have hM := lawRightDensity_measurable (θ := θ) (u := u) (zero_lt_one.trans_le hp) hL
  refine (((expMoment_nat_integrable 1 ht).add (expMoment_nat_integrable 2 ht)).const_mul B).mono'
    (hM.mul (by fun_prop)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs₀ : 0 < s := hs
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  refine (mul_le_mul_of_nonneg_right (hB s hs₀) (Real.exp_pos _).le).trans_eq ?_
  simp only [Pi.add_apply, pow_one]
  ring

theorem lawRightTest_one {p L u t : ℝ} (hp : 0 < p) (hL : 0 < L) (ht : 0 < t) :
    lawRightTest p L 1 u t = rightTest p L (middleA u) (middleZ u) t := by
  rw [rightTest_eq_integral hp hL ht]
  unfold lawRightTest signedLaplace
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  simp only [lawRightDensity, lawDensity, sub_self, zero_mul, one_mul, zero_add,
    middleRightDensity_eq hs, rightWeight]
  ring

theorem lawRightTail_sampling {p L θ u t q : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (ht : 0 ≤ t) (hq : 0 < q) :
    IntegrableOn (fun s => lawRightDensity p L θ u s * Real.exp (-s * t) * scaledExpTail s q) (Ioi 0) ∧
      samplingTail (lawRightTest p L θ u) t q =
        ∫ s : ℝ in Ioi 0, lawRightDensity p L θ u s * Real.exp (-s * t) * scaledExpTail s q := by
  obtain ⟨B, _, hB⟩ := lawRightDensity_bound hp hp₂ hL hθ (u := u)
  have hM := lawRightDensity_measurable (θ := θ) (u := u) (zero_lt_one.trans_le hp) hL
  exact signedTail_sampling_of_majorant hM hq (signedTail_majorant_linearQuadratic hM hB ht hq)

theorem lawRight_abs_samples_summable {p L θ u t q : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (ht : 0 ≤ t) (hq : 0 < q) :
    Summable (fun j : ℕ => |lawRightTest p L θ u (t + ((j + 1 : ℕ) : ℝ) * q)|) := by
  let g := lawRightDensity p L θ u
  let f (s : ℝ) := |g s|
  obtain ⟨B, _, hB⟩ := lawRightDensity_bound hp hp₂ hL hθ (u := u)
  have hM := lawRightDensity_measurable (θ := θ) (u := u) (zero_lt_one.trans_le hp) hL
  have hf : Measurable f := by simpa only [f, g, Real.norm_eq_abs] using hM.norm
  have hfB (s : ℝ) (hs : 0 < s) : |f s| ≤ B * (s + s ^ 2) := by
    change abs (abs (g s)) ≤ B * (s + s ^ 2)
    rw [abs_abs]
    exact hB s hs
  have hS := (hasSum_signedTail_of_majorant hf hq
    (signedTail_majorant_linearQuadratic hf hfB ht hq)).summable
  have hS' : Summable (fun j : ℕ => signedLaplace f (t + ((j + 1 : ℕ) : ℝ) * q)) := by
    apply hS.congr
    intro j
    apply congrArg (signedLaplace f)
    push_cast
    ring
  apply hS'.of_nonneg_of_le (fun _ => abs_nonneg _)
  intro j
  let x := t + ((j + 1 : ℕ) : ℝ) * q
  have h : |signedLaplace g x| ≤ ∫ s : ℝ in Ioi 0, ‖g s * Real.exp (-s * x)‖ := by
    rw [← Real.norm_eq_abs, signedLaplace]
    exact norm_integral_le_integral_norm _
  refine h.trans_eq ?_
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s _
  change ‖g s * Real.exp (-s * x)‖ = f s * Real.exp (-s * x)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]

theorem lawRightTest_difference {p L θ₁ θ₂ u t : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (ht : 0 < t) :
    let R (s : ℝ) := middleRightDensity u s * Real.exp (-s * t)
    IntegrableOn (fun s => signedDensity p L s * R s) (Ioi 0) ∧
      lawRightTest p L θ₂ u t - lawRightTest p L θ₁ u t =
        -(θ₂ - θ₁) * ∫ s : ℝ in Ioi 0, signedDensity p L s * R s := by
  let R (s : ℝ) := middleRightDensity u s * Real.exp (-s * t)
  have h0 : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  have hρ : IntegrableOn (fun s => lineDensity p s * R s) (Ioi 0) := by
    simpa only [lawRightDensity, lawDensity, sub_zero, one_mul, zero_mul, add_zero, R, mul_assoc] using
      lawRightDensity_integrable (u := u) hp hp₂ hL h0 ht
  have hw : IntegrableOn (fun s => imageDensity p L s * R s) (Ioi 0) := by
    simpa only [lawRightDensity, lawDensity, sub_self, zero_mul, one_mul, zero_add, R, mul_assoc] using
      lawRightDensity_integrable (u := u) hp hp₂ hL h1 ht
  have hP (s : ℝ) : signedDensity p L s * R s = lineDensity p s * R s - imageDensity p L s * R s := by
    unfold signedDensity
    ring
  constructor
  · exact (hρ.sub hw).congr (Eventually.of_forall fun s => (hP s).symm)
  · have hLθ (θ : ℝ) : lawRightTest p L θ u t = ∫ s : ℝ in Ioi 0, lawDensity p L θ s * R s := by
      simp only [lawRightTest, signedLaplace, lawRightDensity, R, mul_assoc]
    rw [hLθ, hLθ, lawIntegral_eq hρ hw, lawIntegral_eq hρ hw]
    change _ = -(θ₂ - θ₁) * ∫ s : ℝ in Ioi 0, signedDensity p L s * R s
    rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => hP s), integral_sub hρ hw]
    ring

end ACS12.GammaMeasure


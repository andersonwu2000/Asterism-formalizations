import ACS12.GammaSpectralOrder
import ACS12.PressureGeneralStress
import ACS12.JointGapK

/-! The full high-exponent source Laplace moment inequalities from the exact density orders. -/
namespace ACS12.GammaMeasure

open Set Filter MeasureTheory CenteredCircle.AllN
open GammaDeficit (lineDensity)

private theorem likelihood_firstMoment_gt {f g : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hF : IntegrableOn f (Ioi 0)) (hFs : IntegrableOn (fun s => s * f s) (Ioi 0))
    (hG : IntegrableOn g (Ioi 0)) (hGs : IntegrableOn (fun s => s * g s) (Ioi 0))
    (hg : ∀ s > 0, 0 < g s) (hOrder : StrictMonoOn (fun s => f s / g s) (Ioi 0))
    (hMean : (∫ s : ℝ in Ioi 0, s * g s) = c * ∫ s : ℝ in Ioi 0, g s) :
    c * (∫ s : ℝ in Ioi 0, f s) < ∫ s : ℝ in Ioi 0, s * f s := by
  let a := f c / g c
  let H (s : ℝ) := (s * f s - c * f s) - a * (s * g s - c * g s)
  have hHI : IntegrableOn H (Ioi 0) := (hFs.sub (hF.const_mul _)).sub ((hGs.sub (hG.const_mul _)).const_mul _)
  have hAe : ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)), s ≠ c := by
    apply ae_restrict_of_ae
    rw [ae_iff]
    simp
  have hPos : ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)), 0 < H s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi,hAe] with s hs hsc
    have hS : 0 < s := hs
    have hEq : H s = (s - c) * (f s - a * g s) := by unfold H; ring
    rw [hEq]
    rcases lt_or_gt_of_ne hsc with h | h
    · have hL := hOrder hs hc h
      change f s / g s < a at hL
      exact mul_pos_of_neg_of_neg (sub_neg.mpr h) (sub_neg.mpr ((div_lt_iff₀ (hg s hS)).mp hL))
    · have hL := hOrder hc hs h
      change a < f s / g s at hL
      exact mul_pos (sub_pos.mpr h) (sub_pos.mpr ((lt_div_iff₀ (hg s hS)).mp hL))
  letI : NeZero (volume.restrict (Ioi (0 : ℝ))) := ⟨positiveHalfLine_ne_zero⟩
  have h := integral_strict_of_ae_lt (volume.restrict (Ioi (0 : ℝ)))
    (integrable_zero ℝ ℝ _) hHI hPos
  rw [integral_zero] at h
  let F₁ (s : ℝ) := s * f s - c * f s
  let G₁ (s : ℝ) := s * g s - c * g s
  have hFI : IntegrableOn F₁ (Ioi 0) := hFs.sub (hF.const_mul c)
  have hGI : IntegrableOn G₁ (Ioi 0) := hGs.sub (hG.const_mul c)
  change 0 < ∫ s : ℝ in Ioi 0, F₁ s - a * G₁ s at h
  rw [integral_sub hFI (hGI.const_mul a),integral_const_mul] at h
  have hF₁ : (∫ s : ℝ in Ioi 0, F₁ s) =
      (∫ s : ℝ in Ioi 0, s * f s) - c * (∫ s : ℝ in Ioi 0, f s) := by
    unfold F₁
    rw [integral_sub hFs (hF.const_mul c),integral_const_mul]
  have hG₁ : (∫ s : ℝ in Ioi 0, G₁ s) = 0 := by
    unfold G₁
    rw [integral_sub hGs (hG.const_mul c),integral_const_mul,hMean,sub_self]
  rw [hF₁,hG₁,mul_zero,sub_zero] at h
  exact sub_pos.mp h

noncomputable def sourceLaplaceMoment (p L : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  ∫ s : ℝ in Ioi 0, imageDensity p L s * s ^ j * Real.exp (-s * t)

theorem sourceLaplaceMoment_integrable {p L t : ℝ} (hp : 0 < p) (hL : 0 < L) (ht : 0 < t) (j : ℕ) :
    IntegrableOn (fun s : ℝ => imageDensity p L s * s ^ j * Real.exp (-s * t)) (Ioi 0) := by
  obtain ⟨C,hC,hB⟩ := Pressure.imageDensity_linear_exp_bound hp hL (show 0 < t / 2 by positivity)
  apply (expMoment_nat_integrable (j + 1) (show 0 < t / 2 by positivity)).const_mul C |>.mono'
  · exact (((continuous_imageDensity hp hL).measurable.mul (measurable_id.pow_const j)).mul
      (by fun_prop)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0 < s := hs
    have hW := imageDensity_pos hp hL hs₀
    rw [Real.norm_of_nonneg (by positivity)]
    have h := mul_le_mul_of_nonneg_right (hB s hs₀) (show 0 ≤ s ^ j * Real.exp (-s * t) by positivity)
    have hExp : Real.exp (t / 2 * s) * Real.exp (-s * t) = Real.exp (-s * (t / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ ≤ (C * s * Real.exp (t / 2 * s)) * (s ^ j * Real.exp (-s * t)) := by
        rw [mul_assoc]
        exact h
      _ = _ := by
        rw [pow_succ,← hExp]
        ring

private theorem pureLaplaceMoment_mean {q t : ℝ} (hq : 0 < q) (ht : 0 < t) (j : ℕ) :
    (∫ s : ℝ in Ioi 0, s * (lineDensity q s * s ^ j * Real.exp (-s * t))) =
      ((q + (j : ℝ)) / t) * ∫ s : ℝ in Ioi 0, lineDensity q s * s ^ j * Real.exp (-s * t) := by
  have hEq (s : ℝ) : s * (lineDensity q s * s ^ j * Real.exp (-s * t)) =
      lineDensity q s * s ^ (j + 1) * Real.exp (-s * t) := by rw [pow_succ]; ring
  simp_rw [hEq]
  rw [(lineDensity_moment hq ht (j + 1)).2,(lineDensity_moment hq ht j).2,Nat.cast_succ,
    ← add_assoc,Real.Gamma_add_one (by positivity : 0 < q + (j : ℝ)).ne',
    show -(q + (j : ℝ) + 1) = -(q + (j : ℝ)) - 1 by ring,Real.rpow_sub_one ht.ne']
  ring

theorem sourceLaplaceMoment_strict_bounds {p L t : ℝ} (hp : 2 < p) (hL : 0 < L) (ht : 0 < t) (j : ℕ) :
    ((j : ℝ) + 2) * sourceLaplaceMoment p L j t < t * sourceLaplaceMoment p L (j + 1) t ∧
      t * sourceLaplaceMoment p L (j + 1) t < ((j : ℝ) + p) * sourceLaplaceMoment p L j t := by
  let f (s : ℝ) := imageDensity p L s * s ^ j * Real.exp (-s * t)
  let g (q s : ℝ) := lineDensity q s * s ^ j * Real.exp (-s * t)
  have hp₀ : 0 < p := by linarith only [hp]
  have hF : IntegrableOn f (Ioi 0) := sourceLaplaceMoment_integrable hp₀ hL ht j
  have hFs : IntegrableOn (fun s => s * f s) (Ioi 0) := by
    apply (sourceLaplaceMoment_integrable hp₀ hL ht (j + 1)).congr
    exact Eventually.of_forall fun s => by dsimp only [f]; rw [pow_succ]; ring
  have hG {q : ℝ} (hq : 0 < q) : IntegrableOn (g q) (Ioi 0) := (lineDensity_moment hq ht j).1
  have hGs {q : ℝ} (hq : 0 < q) : IntegrableOn (fun s => s * g q s) (Ioi 0) := by
    apply (lineDensity_moment hq ht (j + 1)).1.congr
    exact Eventually.of_forall fun s => by dsimp only [g]; rw [pow_succ]; ring
  have hGp {q : ℝ} (hq : 0 < q) (s : ℝ) (hs : 0 < s) : 0 < g q s :=
    mul_pos (mul_pos (lineDensity_pos hq hs) (pow_pos hs _)) (Real.exp_pos _)
  have hGq (q s : ℝ) (hs : 0 < s) : f s / g q s = imageDensity p L s / lineDensity q s := by
    unfold f g
    rw [mul_assoc,mul_assoc,mul_div_mul_right _ _ (mul_pos (pow_pos hs j) (Real.exp_pos _)).ne']
  have hOrder₂ : StrictMonoOn (fun s => f s / g 2 s) (Ioi 0) := by
    intro x hx y hy hxy
    change f x / g 2 x < f y / g 2 y
    rw [hGq 2 x hx,hGq 2 y hy]
    have hEq (s : ℝ) : lineDensity 2 s = s := by norm_num [lineDensity,Real.Gamma_nat_eq_factorial]
    rw [hEq,hEq]
    exact imageDensity_div_strictMono hp hL hx hy hxy
  have hOrderp : StrictMonoOn (fun s => (-f s) / g p s) (Ioi 0) := by
    intro x hx y hy hxy
    change (-f x) / g p x < (-f y) / g p y
    rw [neg_div,neg_div,hGq p x hx,hGq p y hy]
    exact neg_lt_neg (imageDensity_div_lineDensity_strictAnti hp hL hx hy hxy)
  have hLower := likelihood_firstMoment_gt (c := (2 + (j : ℝ)) / t) (by positivity)
    hF hFs (hG (by norm_num)) (hGs (by norm_num)) (hGp (by norm_num)) hOrder₂
    (pureLaplaceMoment_mean (by norm_num) ht j)
  have hNeg : IntegrableOn (fun s => s * (-f s)) (Ioi 0) := by
    apply hFs.neg.congr
    exact Eventually.of_forall fun s => by simp
  have hUpper := likelihood_firstMoment_gt (c := (p + (j : ℝ)) / t) (by positivity)
    hF.neg hNeg (hG hp₀) (hGs hp₀) (hGp hp₀) hOrderp (pureLaplaceMoment_mean hp₀ ht j)
  have hE : (∫ s : ℝ in Ioi 0, s * f s) = sourceLaplaceMoment p L (j + 1) t := by
    unfold sourceLaplaceMoment
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s _
    dsimp only [f]
    rw [pow_succ]
    ring
  simp only [Pi.neg_apply,mul_neg,integral_neg] at hUpper
  change ((2 + (j : ℝ)) / t) * sourceLaplaceMoment p L j t < _ at hLower
  change -(((p + (j : ℝ)) / t) * sourceLaplaceMoment p L j t) < _ at hUpper
  rw [hE] at hLower hUpper
  have hA := mul_lt_mul_of_pos_right hLower ht
  have hB := mul_lt_mul_of_pos_right (neg_lt_neg_iff.mp hUpper) ht
  rw [mul_comm ((2 + (j : ℝ)) / t),mul_assoc,div_mul_cancel₀ _ ht.ne'] at hA
  rw [mul_comm ((p + (j : ℝ)) / t),mul_assoc,div_mul_cancel₀ _ ht.ne'] at hB
  constructor <;> linarith only [hA,hB]

/-- Closed shape order. At two the image density is literally linear,
so the weak comparison is exact rather than a strict stochastic tilt. -/
theorem imageDensity_div_monotone {p L : ℝ} (hp : 2 ≤ p) (hL : 0 < L) :
    MonotoneOn (fun s => imageDensity p L s / s) (Ioi 0) := by
  rcases lt_or_eq_of_le hp with h | rfl
  · exact (imageDensity_div_strictMono h hL).monotoneOn
  · intro x hx y hy _
    dsimp only
    rw [imageDensity_two hL hx, imageDensity_two hL hy,
      div_self (show x ≠ 0 from hx.ne'), div_self (show y ≠ 0 from hy.ne')]

/-- The line likelihood order becomes equality at the literal endpoint. -/
theorem imageDensity_div_lineDensity_antitone {p L : ℝ} (hp : 2 ≤ p) (hL : 0 < L) :
    AntitoneOn (fun s => imageDensity p L s / lineDensity p s) (Ioi 0) := by
  rcases lt_or_eq_of_le hp with h | rfl
  · exact (imageDensity_div_lineDensity_strictAnti h hL).antitoneOn
  · intro x hx y hy _
    dsimp only
    have hρ (s : ℝ) : lineDensity 2 s = s := by
      norm_num [lineDensity, Real.Gamma_nat_eq_factorial]
    rw [imageDensity_two hL hx, imageDensity_two hL hy, hρ, hρ,
      div_self (show x ≠ 0 from hx.ne'), div_self (show y ≠ 0 from hy.ne')]

/-- Complete source moments on the closed band. The two bounds coincide
at two; physical occupied rows, not these weak bounds, supply strictness. -/
theorem sourceLaplaceMoment_bounds {p L t : ℝ} (hp : 2 ≤ p)
    (hL : 0 < L) (ht : 0 < t) (j : ℕ) :
    ((j : ℝ) + 2) * sourceLaplaceMoment p L j t ≤
        t * sourceLaplaceMoment p L (j + 1) t ∧
      t * sourceLaplaceMoment p L (j + 1) t ≤
        ((j : ℝ) + p) * sourceLaplaceMoment p L j t := by
  rcases lt_or_eq_of_le hp with h | rfl
  · exact ⟨(sourceLaplaceMoment_strict_bounds h hL ht j).1.le,
      (sourceLaplaceMoment_strict_bounds h hL ht j).2.le⟩
  · have hρ (s : ℝ) : lineDensity 2 s = s := by
      norm_num [lineDensity, Real.Gamma_nat_eq_factorial]
    have hE (k : ℕ) : sourceLaplaceMoment 2 L k t =
        ∫ s : ℝ in Ioi 0, lineDensity 2 s * s ^ k * Real.exp (-s * t) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      dsimp only
      rw [imageDensity_two hL hs, hρ]
    have hMean := pureLaplaceMoment_mean (by norm_num : (0 : ℝ) < 2) ht j
    have hNext : (∫ s : ℝ in Ioi 0,
        s * (lineDensity 2 s * s ^ j * Real.exp (-s * t))) =
        sourceLaplaceMoment 2 L (j + 1) t := by
      rw [hE]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s _
      dsimp only
      rw [pow_succ]
      ring
    rw [hNext, ← hE j] at hMean
    have h := congrArg (fun x : ℝ => x * t) hMean
    dsimp only at h
    rw [mul_comm ((2 + (j : ℝ)) / t), mul_assoc,
      div_mul_cancel₀ _ ht.ne'] at h
    constructor <;> linarith only [h]

end ACS12.GammaMeasure


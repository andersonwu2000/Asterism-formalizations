import ACS12.JointBoseCurvature
import ACS12.JointUnitValue

/-! Complete upper prices of the original positive source-gap curvature. -/
namespace ACS12.GammaMeasure

open Set Filter MeasureTheory CenteredCircle.AllN
open GammaDeficit (lineDensity gamma_exp_integral integrable_gamma_exp)

theorem lineDensity_moment {p t : ℝ} (hp : 0 < p) (ht : 0 < t) (k : ℕ) :
    let f (s : ℝ) := lineDensity p s * s ^ k * Real.exp (-s * t)
    IntegrableOn f (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, f s) = (Real.Gamma (p + k) / Real.Gamma p) * t ^ (-(p + k)) := by
  let f (s : ℝ) := lineDensity p s * s ^ k * Real.exp (-s * t)
  have hk : 0 < p + (k : ℝ) := by positivity
  have h (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      f s = (Real.Gamma p)⁻¹ * (s ^ (p + k - 1) * Real.exp (-t * s)) := by
    dsimp only [f,lineDensity]
    have he : s ^ (p - 1) * s ^ k = s ^ (p + k - 1) := by
      rw [← Real.rpow_natCast,← Real.rpow_add (show 0 < s from hs)]
      congr 1
      ring
    rw [show -s * t = -t * s by ring, ← he]
    ring
  constructor
  · apply ((integrable_gamma_exp hk ht).const_mul (Real.Gamma p)⁻¹).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (h s hs).symm
  · change (∫ s : ℝ in Ioi 0, f s) = _
    rw [setIntegral_congr_fun measurableSet_Ioi h,integral_const_mul,gamma_exp_integral hk ht]
    ring

theorem lineDensity_bose₂_moment {p : ℝ} (hp : 0 < p) {m : ℕ} (hm : 0 < m) :
    let f (s : ℝ) := lineDensity p s * s ^ 2 * (Real.exp (-s * (m : ℝ)) / (1 - Real.exp (-s)))
    IntegrableOn f (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, f s) = p * (p + 1) * powerTail (p + 2) m := by
  let f (s : ℝ) := lineDensity p s * s ^ 2 * (Real.exp (-s * (m : ℝ)) / (1 - Real.exp (-s)))
  have hG : Real.Gamma (p + 2) = p * (p + 1) * Real.Gamma p := by
    rw [show p + 2 = (p + 1) + 1 by ring,Real.Gamma_add_one (by positivity : 0 < p + 1).ne',Real.Gamma_add_one hp.ne']
    ring
  have h (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      f s = (Real.Gamma p)⁻¹ * (s ^ (p + 1) * (Real.exp (-s * (m : ℝ)) / (1 - Real.exp (-s)))) := by
    have hPow : s ^ (p - 1) * s ^ 2 = s ^ (p + 1) := by
      rw [← Real.rpow_two,← Real.rpow_add (show 0 < s from hs)]
      congr 1
      ring
    dsimp only [f,lineDensity]
    rw [← hPow]
    ring
  constructor
  · apply ((boseMoment_integrable (by positivity : 0 < p + 1) hm).const_mul (Real.Gamma p)⁻¹).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (h s hs).symm
  · change (∫ s : ℝ in Ioi 0, f s) = _
    rw [setIntegral_congr_fun measurableSet_Ioi h,integral_const_mul,
      boseMoment_integral (by positivity : 0 < p + 1) hm,show p + 1 + 1 = p + 2 by ring,hG]
    field_simp [(Real.Gamma_pos_of_pos hp).ne']

noncomputable def jointGapKp (p : ℝ) : ℝ :=
  ∫ s : ℝ in Ioi 0, lineDensity p s * polyA s * s * (-BoseShape.C₁ s)

noncomputable def jointGapKa (p : ℝ) : ℝ :=
  ∫ s : ℝ in Ioi 0, lineDensity p s * Real.exp (-s) * polyA s * s * (-BoseShape.C₁ s)

theorem jointGapKp_integral_bound {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun s => lineDensity p s * polyA s * s * (-BoseShape.C₁ s)) (Ioi 0) ∧
      jointGapKp p ≤ 2 * pureQ p - p * (p + 1) - 2 * p := by
  let f (s : ℝ) := lineDensity p s * polyA s * s * (-BoseShape.C₁ s)
  let A (s : ℝ) := lineDensity p s * s ^ 2 * Real.exp (-s)
  let B (s : ℝ) := lineDensity p s * s * Real.exp (-s)
  let C (s : ℝ) := lineDensity p s * s ^ 2 * (Real.exp (-s * 2) / (1 - Real.exp (-s)))
  let g (s : ℝ) := A s - 2 * B s + 2 * C s
  obtain ⟨hA,hAE⟩ := lineDensity_moment hp zero_lt_one 2
  obtain ⟨hB,hBE⟩ := lineDensity_moment hp zero_lt_one 1
  obtain ⟨hC,hCE⟩ := lineDensity_bose₂_moment hp (by decide : (0 : ℕ) < 2)
  simp only [mul_one,pow_one,Nat.cast_ofNat,Nat.cast_one] at hA hB hC hAE hBE hCE
  change IntegrableOn A (Ioi 0) at hA
  change IntegrableOn B (Ioi 0) at hB
  change IntegrableOn C (Ioi 0) at hC
  have hAB : IntegrableOn (fun s => A s - 2 * B s) (Ioi 0) := hA.sub (hB.const_mul 2)
  have hI : IntegrableOn g (Ioi 0) := hAB.add (hC.const_mul 2)
  have hM : Measurable f := by
    unfold f
    exact (by unfold lineDensity polyA; fun_prop : Measurable (fun s => lineDensity p s * polyA s * s)).mul
      BoseShape.C₁_measurable.neg
  have hPoint (s : ℝ) (hs : 0 < s) : 0 ≤ f s ∧ f s ≤ g s := by
    let X := Real.exp (-s)
    let b := 1 - X
    have hb : 0 < b := expHead_den_pos hs
    have hX : 0 < X := Real.exp_pos _
    have hA : 0 ≤ polyA s := (polyA_pos hs).le
    have hC : 0 ≤ -BoseShape.C₁ s := neg_nonneg.mpr (BoseShape.C₁_neg hs).le
    have hρ : 0 ≤ lineDensity p s := by unfold lineDensity; positivity
    have h : polyA s ≤ b ^ 2 := by
      have hE := mul_nonneg hX.le (show 0 ≤ s - 1 + X by dsimp only [X]; linarith only [Real.add_one_le_exp (-s)])
      dsimp only [b,polyA]
      change _ - (1 + s) * X ≤ _
      nlinarith only [hE]
    refine ⟨mul_nonneg (mul_nonneg (mul_nonneg hρ hA) hs.le) hC,?_⟩
    calc
      f s ≤ lineDensity p s * b ^ 2 * s * (-BoseShape.C₁ s) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hρ) hs.le) hC
      _ = g s := by
        rw [BoseShape.neg_C₁_eq hs]
        dsimp only [g,A,B,C,b,X]
        rw [show -s * 2 = -s + -s by ring,Real.exp_add]
        field_simp [(expHead_den_pos hs).ne']
        ring
  have hf : IntegrableOn f (Ioi 0) := by
    apply hI.mono' hM.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have h := hPoint s hs
    rw [Real.norm_of_nonneg h.1]
    exact h.2
  refine ⟨hf,?_⟩
  have h := integral_mono_ae hf hI (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs; exact (hPoint s hs).2)
  have hE : (∫ s : ℝ in Ioi 0, g s) = 2 * pureQ p - p * (p + 1) - 2 * p := by
    dsimp only [g]
    rw [integral_add hAB (hC.const_mul 2),integral_sub hA (hB.const_mul 2),integral_const_mul,integral_const_mul]
    dsimp only [A,B,C]
    rw [hAE,hBE,hCE,Real.one_rpow,Real.one_rpow,mul_one,mul_one]
    rw [Real.Gamma_add_one hp.ne',show p + 2 = (p + 1) + 1 by ring,
      Real.Gamma_add_one (by positivity : 0 < p + 1).ne',Real.Gamma_add_one hp.ne']
    rw [show p + 1 + 1 = p + 2 by ring,powerTail_shift (q := p + 2) (by linarith only [hp]) 1]
    simp only [Nat.cast_one,Real.one_rpow]
    unfold pureQ
    field_simp [(Real.Gamma_pos_of_pos hp).ne']
    ring
  exact h.trans_eq hE

theorem jointGapKp_lt {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    jointGapKp p < 2423 / 1000 := by
  let f (p : ℝ) := 2 * pureQ p - p * (p + 1) - 2 * p
  have hD (p : ℝ) (hp : p ∈ Icc (1 : ℝ) (9 / 5)) :
      HasDerivAt f (2 * pureQPrime p - 2 * p - 3) p := by
    have h := hasDerivAt_id p
    convert (((pureQ_derivative (by linarith only [hp.1])).const_mul 2).sub (h.mul (h.add_const 1))).sub
      (h.const_mul 2) using 1
    simp only [id_eq,mul_one,one_mul]
    ring
  have hM : MonotoneOn f (Icc 1 (9 / 5)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun p hp => (hD p hp).continuousAt.continuousWithinAt
    · exact fun p hp => (hD p (interior_subset hp)).differentiableAt.differentiableWithinAt
    · intro p hp
      have hp' : p ∈ Icc (1 : ℝ) (9 / 5) := interior_subset hp
      rw [(hD p hp').deriv]
      linarith only [(pureQPrime_bounds hp'.1 hp'.2).1,hp'.1]
  have hEnd : f (9 / 5) < 2423 / 1000 := by
    dsimp only [f]
    linarith only [jointPure_endpoint_moments.2.2.2]
  exact ((jointGapKp_integral_bound (zero_lt_one.trans_le hp)).2.trans
    (hM ⟨hp,hP⟩ (show (9 / 5 : ℝ) ∈ Icc 1 (9 / 5) by constructor <;> norm_num) hP)).trans_lt hEnd


theorem jointGapKa_integral_bound {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun s => lineDensity p s * Real.exp (-s) * polyA s * s * (-BoseShape.C₁ s)) (Ioi 0) ∧
      jointGapKa p ≤ (p / 6) * (1 - (p + 3) * (2 : ℝ) ^ (-p) / 4) := by
  let f (s : ℝ) := lineDensity p s * Real.exp (-s) * polyA s * s * (-BoseShape.C₁ s)
  let A (s : ℝ) := lineDensity p s * s * Real.exp (-s)
  let B (s : ℝ) := lineDensity p s * s * Real.exp (-s * 2)
  let C (s : ℝ) := lineDensity p s * s ^ 2 * Real.exp (-s * 2)
  let g (s : ℝ) := (1 / 6) * (A s - B s - C s)
  obtain ⟨hA,hAE⟩ := lineDensity_moment hp zero_lt_one 1
  obtain ⟨hB,hBE⟩ := lineDensity_moment hp (by norm_num : 0 < (2 : ℝ)) 1
  obtain ⟨hC,hCE⟩ := lineDensity_moment hp (by norm_num : 0 < (2 : ℝ)) 2
  simp only [mul_one,pow_one,Nat.cast_ofNat,Nat.cast_one] at hA hB hC hAE hBE hCE
  change IntegrableOn A (Ioi 0) at hA
  change IntegrableOn B (Ioi 0) at hB
  change IntegrableOn C (Ioi 0) at hC
  have hAB : IntegrableOn (fun s => A s - B s) (Ioi 0) := hA.sub hB
  have hI : IntegrableOn g (Ioi 0) := (hAB.sub hC).const_mul (1 / 6)
  have hM : Measurable f := by
    unfold f
    exact (by unfold lineDensity polyA; fun_prop : Measurable (fun s =>
      lineDensity p s * Real.exp (-s) * polyA s * s)).mul BoseShape.C₁_measurable.neg
  have hPoint (s : ℝ) (hs : 0 < s) : 0 ≤ f s ∧ f s ≤ g s := by
    have hA : 0 ≤ polyA s := (polyA_pos hs).le
    have hC : 0 ≤ -BoseShape.C₁ s := neg_nonneg.mpr (BoseShape.C₁_neg hs).le
    have hρ : 0 ≤ lineDensity p s := by unfold lineDensity; positivity
    have hP : 0 ≤ lineDensity p s * Real.exp (-s) * polyA s * s :=
      mul_nonneg (mul_nonneg (mul_nonneg hρ (Real.exp_pos _).le) hA) hs.le
    refine ⟨mul_nonneg hP hC,?_⟩
    calc
      f s ≤ lineDensity p s * Real.exp (-s) * polyA s * s * (1 / 6) :=
        mul_le_mul_of_nonneg_left (BoseShape.neg_C₁_lt_sixth hs).le hP
      _ = g s := by
        dsimp only [g,A,B,C,polyA]
        rw [show -s * 2 = -s + -s by ring,Real.exp_add]
        ring
  have hf : IntegrableOn f (Ioi 0) := by
    apply hI.mono' hM.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have h := hPoint s hs
    rw [Real.norm_of_nonneg h.1]
    exact h.2
  refine ⟨hf,?_⟩
  have h := integral_mono_ae hf hI (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs; exact (hPoint s hs).2)
  have hE : (∫ s : ℝ in Ioi 0, g s) = (p / 6) * (1 - (p + 3) * (2 : ℝ) ^ (-p) / 4) := by
    dsimp only [g]
    rw [integral_const_mul,integral_sub hAB hC,integral_sub hA hB]
    dsimp only [A,B,C]
    rw [hAE,hBE,hCE,Real.one_rpow,mul_one]
    rw [show p + 2 = (p + 1) + 1 by ring,Real.Gamma_add_one (by positivity : 0 < p + 1).ne',
      Real.Gamma_add_one hp.ne']
    rw [show -(p + 1) = -p - 1 by ring,show -(p + 1 + 1) = -p - 1 - 1 by ring]
    simp only [Real.rpow_sub_one (by norm_num : (2 : ℝ) ≠ 0)]
    field_simp [(Real.Gamma_pos_of_pos hp).ne']
    ring
  exact h.trans_eq hE

theorem jointGapKa_lt {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) : jointGapKa p < 1 / 5 := by
  let f (p : ℝ) := (p + 3) * (2 : ℝ) ^ (-p)
  have hD (p : ℝ) : HasDerivAt f ((2 : ℝ) ^ (-p) * (1 - (p + 3) * Real.log 2)) p := by
    have h := hasDerivAt_id p
    convert (h.add_const 3).mul (h.neg.const_rpow (by norm_num : (0 : ℝ) < 2)) using 1
    simp only [id_eq,Pi.neg_apply]
    ring
  have hM : AntitoneOn f (Icc 1 (9 / 5)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · exact fun p _ => (hD p).continuousAt.continuousWithinAt
    · exact fun p _ => (hD p).differentiableAt.differentiableWithinAt
    · intro p hp
      have hp' : p ∈ Icc (1 : ℝ) (9 / 5) := interior_subset hp
      rw [(hD p).deriv]
      have hL : (69 / 100 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
      have h := mul_le_mul (show (4 : ℝ) ≤ p + 3 by linarith only [hp'.1]) hL (by norm_num)
        (by linarith only [hp'.1])
      exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (by norm_num) _) (by linarith only [h])
  have h := hM ⟨hp,hP⟩ (show (9 / 5 : ℝ) ∈ Icc 1 (9 / 5) by constructor <;> norm_num) hP
  have hX : (28717 / 100000 : ℝ) < (2 : ℝ) ^ (-(9 / 5 : ℝ)) := by
    apply (Real.rpow_lt_rpow_iff (by norm_num) (Real.rpow_nonneg (by norm_num) _)
      (z := (5 : ℝ)) (by norm_num)).mp
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hB : (1 - f p / 4) ≤ 1 - ((9 / 5 : ℝ) + 3) * (28717 / 100000) / 4 := by
    dsimp only [f] at h
    linarith only [h,hX]
  have hT := mul_le_mul_of_nonneg_left hB (show 0 ≤ p / 6 by positivity)
  have hU := mul_le_mul_of_nonneg_right (show p / 6 ≤ (3 / 10 : ℝ) by linarith only [hP])
    (by norm_num : (0 : ℝ) ≤ 1 - ((9 / 5 : ℝ) + 3) * (28717 / 100000) / 4)
  exact ((jointGapKa_integral_bound (zero_lt_one.trans_le hp)).2.trans (hT.trans hU)).trans_lt (by norm_num)

noncomputable def jointGapDensity (s : ℝ) : ℝ :=
  jointCanonicalMu * polyA s + jointPureLambda * Real.exp (-s) * polyA s

noncomputable def jointGapK (p t : ℝ) : ℝ :=
  ∫ s : ℝ in Ioi 0, lineDensity p s * jointGapDensity s * s * (-BoseShape.C₁ (t * s))

theorem jointGapK_one_lt {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    jointGapK p 1 < 787 / 10000 := by
  have hp₀ := zero_lt_one.trans_le hp
  have hI := (jointGapKp_integral_bound hp₀).1
  have hJ := (jointGapKa_integral_bound hp₀).1
  unfold jointGapK jointGapDensity
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun s =>
    jointCanonicalMu * (lineDensity p s * polyA s * s * (-BoseShape.C₁ s)) +
    jointPureLambda * (lineDensity p s * Real.exp (-s) * polyA s * s * (-BoseShape.C₁ s)))
    (fun s _ => by simp only [one_mul]; ring),
    integral_add (hI.const_mul _) (hJ.const_mul _),integral_const_mul,integral_const_mul]
  change jointCanonicalMu * jointGapKp p + jointPureLambda * jointGapKa p < _
  obtain ⟨hmL,hmU⟩ := jointCanonicalMu_bounds
  have hP' := mul_le_mul_of_nonneg_left (jointGapKp_lt hp hP).le (show 0 ≤ jointCanonicalMu by linarith only [hmL])
  have hA' := mul_le_mul_of_nonneg_left (jointGapKa_lt hp hP).le (by norm_num [jointPureLambda] : 0 ≤ jointPureLambda)
  unfold jointPureLambda at hA' ⊢
  linarith only [hP',hA',hmU]

end ACS12.GammaMeasure

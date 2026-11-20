import ACS12.PureCMoments
import ACS12.PureNativeBasics
import ACS12.BosePath

/-! Exact one-source outer densities and their full-frequency scaling. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaDeficit (lineDensity)
open BoseShape (positive_of_derivative expQuad expQuad_deriv)

noncomputable def outerR (u s : ℝ) : ℝ :=
  middleRightDensity u s - (19 / 100) * polyB (u * s)

noncomputable def outerK (u s : ℝ) : ℝ :=
  u * s * (1 - (12 / 25) * (1 - Real.exp (-s))) - (1 + u) * (1 - Real.exp (-s))

theorem outerR_one_eq (s : ℝ) :
    outerR 1 s = (81 / 100) * polyB s - (6 / 25) * s * (1 - Real.exp (-s)) := by
  simp only [outerR, middleRightDensity, middleA0, middleZ, middleA, polyB, mul_one, one_mul]
  ring

theorem outerR_one_pos {s : ℝ} (hs : 0 < s) : 0 < outerR 1 s := by
  rw [outerR_one_eq]
  have h := polyB_elasticity hs.le
  linarith only [h, polyB_pos hs]

theorem outerR_scale_bound {u s : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) (hs : 0 < s) :
    outerR u s ≤ u ^ 2 * outerR 1 s + (1 - u) * outerK u s := by
  have hR : middleRightDensity u s =
      u ^ 2 * middleRightDensity 1 s + (1 - u) * outerK u s := by
    simp only [middleRightDensity, middleA0, middleZ, middleA, outerK]
    ring
  unfold outerR
  rw [hR, one_mul]
  nlinarith only [polyB_scale_lower hu hu₁ hs]

private theorem outerR_one_derivative (s : ℝ) : HasDerivAt (outerR 1)
    ((81 / 100) * (1 - Real.exp (-s)) -
      (6 / 25) * ((1 - Real.exp (-s)) + s * Real.exp (-s))) s := by
  have h := (((hasDerivAt_id s).mul ((hasDerivAt_neg s).exp.const_sub 1)).const_mul (6 / 25))
  convert ((hasDerivAt_polyB s).const_mul (81 / 100)).sub h using 1
  · funext x
    rw [outerR_one_eq]
    simp only [Pi.sub_apply, Pi.mul_apply, id_eq]
    ring
  · simp only [id_eq, mul_one, one_mul, mul_neg, neg_neg]

private theorem outerR_one_elasticity {s : ℝ} (hs : 0 < s) :
    s * deriv (outerR 1) s ≤ 2 * outerR 1 s := by
  let f (x : ℝ) := expQuad 1 0 (57 / 100) (-81 / 50) x +
    81 / 50 + (21 / 20) * x + (6 / 25) * x ^ 2
  let f₁ (x : ℝ) := expQuad 1 0 (57 / 100) (-21 / 20) x + 21 / 20 + (12 / 25) * x
  let f₂ (x : ℝ) := expQuad 1 0 (57 / 100) (-12 / 25) x + 12 / 25
  let f₃ (x : ℝ) := expQuad 1 0 (57 / 100) (9 / 100) x
  have h₁ (x : ℝ) : HasDerivAt f (f₁ x) x := by
    have h := (expQuad_deriv 1 0 (57 / 100) (-81 / 50) x).add_const (81 / 50)
    convert (h.add ((hasDerivAt_id x).const_mul (21 / 20))).add
      (((hasDerivAt_id x).pow 2).const_mul (6 / 25)) using 1
    norm_num [f₁, expQuad] <;> ring
  have h₂ (x : ℝ) : HasDerivAt f₁ (f₂ x) x := by
    convert ((expQuad_deriv 1 0 (57 / 100) (-21 / 20) x).add_const (21 / 20)).add
      ((hasDerivAt_id x).const_mul (12 / 25)) using 1
    norm_num [f₂, expQuad]
  have h₃ (x : ℝ) : HasDerivAt f₂ (f₃ x) x := by
    convert (expQuad_deriv 1 0 (57 / 100) (-12 / 25) x).add_const (12 / 25) using 1
    norm_num [f₃, expQuad]
  have hP₃ (x : ℝ) (hx : 0 < x) : 0 < f₃ x := by unfold f₃ expQuad; positivity
  have hP₂ (x : ℝ) (hx : 0 < x) : 0 < f₂ x := positive_of_derivative
    (by norm_num [f₂, expQuad]) h₃ hP₃ hx
  have hP₁ (x : ℝ) (hx : 0 < x) : 0 < f₁ x := positive_of_derivative
    (by norm_num [f₁, expQuad]) h₂ hP₂ hx
  have hP := positive_of_derivative (by norm_num [f, expQuad]) h₁ hP₁ hs
  have hE : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hF : (2 * outerR 1 s - s * deriv (outerR 1) s) * Real.exp s = f s := by
    rw [(outerR_one_derivative s).deriv, outerR_one_eq]
    simp only [f, expQuad, polyB, one_mul]
    linear_combination ((81 / 50) + (21 / 20) * s + (6 / 25) * s ^ 2) * hE
  have h := (mul_pos_iff_of_pos_right (Real.exp_pos s)).mp (hF ▸ hP)
  linarith only [h]

theorem outerR_one_scale_upper {t s : ℝ} (ht : 0 < t) (ht₁ : t ≤ 1) (hs : 0 < s) :
    outerR 1 (s / t) ≤ outerR 1 s / t ^ 2 := by
  let f (x : ℝ) := outerR 1 x / x ^ 2
  have hD (x : ℝ) (hx : 0 < x) :
      HasDerivAt f ((x * deriv (outerR 1) x - 2 * outerR 1 x) / x ^ 3) x := by
    convert (outerR_one_derivative x).div ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 hx.ne') using 1
    rw [(outerR_one_derivative x).deriv]
    simp only [id_eq, Nat.cast_ofNat, mul_one, Pi.pow_apply]
    norm_num
    field_simp [hx.ne']
  have hAnti : AntitoneOn f (Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi _)
    · exact fun x hx => (hD x hx).continuousAt.continuousWithinAt
    · exact fun x hx => (hD x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx₀ : 0 < x := interior_subset hx
      rw [(hD x hx₀).deriv]
      exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (outerR_one_elasticity hx₀)) (by positivity)
  have hArg : s ≤ s / t := (le_div_iff₀ ht).mpr (mul_le_of_le_one_right hs.le ht₁)
  have h := hAnti hs (div_pos hs ht) hArg
  change outerR 1 (s / t) / (s / t) ^ 2 ≤ outerR 1 s / s ^ 2 at h
  rw [div_pow] at h
  have h' := (div_le_div_iff₀ (by positivity : 0 < s ^ 2 / t ^ 2)
    (by positivity : 0 < s ^ 2)).mp h
  apply le_of_mul_le_mul_right _ (by positivity : 0 < s ^ 2)
  exact h'.trans_eq (by ring)

theorem outerK_scale_upper {u t s : ℝ} (hu : 0 < u) (hut : u ≤ t) (ht₁ : t ≤ 1) (hs : 0 < s) :
    outerK u (s / t) ≤ s * (1 - (12 / 25) * (1 - Real.exp (-s))) -
      (1 + u) * (1 - Real.exp (-s)) := by
  have ht := hu.trans_le hut
  have hA : u * (s / t) ≤ s := by
    rw [← mul_div_assoc]
    exact (div_le_iff₀ ht).mpr (by nlinarith [mul_le_mul_of_nonneg_right hut hs.le])
  have hB : 1 - Real.exp (-s) ≤ 1 - Real.exp (-(s / t)) := by
    apply sub_le_sub_left
    exact Real.exp_le_exp.mpr (neg_le_neg ((le_div_iff₀ ht).mpr (mul_le_of_le_one_right hs.le ht₁)))
  have hC : 0 ≤ 1 - (12 / 25) * (1 - Real.exp (-(s / t))) := by
    linarith [Real.exp_pos (-(s / t))]
  unfold outerK
  apply sub_le_sub
  · exact mul_le_mul hA (by linarith only [hB]) hC hs.le
  · exact mul_le_mul_of_nonneg_left hB (by positivity)

theorem pureLinear_envelope {p : ℝ} {f : ℝ → ℝ} {B : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hB : 0 ≤ B) (hf : ∀ s > 0, |f s| ≤ B * s) :
    ∃ C ≥ 0, ∀ s > 0, |lineDensity p s * f s| ≤ C * (s + s ^ 2) := by
  obtain ⟨C, hC, hW⟩ := lawDensity_linear_envelope hp hp₂ zero_lt_one
    (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩)
  simp only [lawDensity, sub_zero, one_mul, zero_mul, add_zero] at hW
  refine ⟨C * B, mul_nonneg hC hB, ?_⟩
  intro s hs
  rw [abs_mul]
  exact (mul_le_mul (hW s hs) (hf s hs) (abs_nonneg _) (by positivity)).trans_eq (by ring)

theorem outerR_linear_bound {u : ℝ} (hu : 0 < u) :
    ∃ B ≥ 0, ∀ s > 0, |outerR u s| ≤ B * s := by
  let B := |middleZ u| + |middleA u| + 1 + (19 / 100) * u
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro s hs
  have hB' : polyB (u * s) ≤ u * s := by
    unfold polyB
    linarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_pos hu hs).le)]
  have hR := mul_le_mul_of_nonneg_left (rightMultiplier_bound (middleA u) (middleZ u) hs) hs.le
  rw [outerR, middleRightDensity_eq hs]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_of_pos hs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 19 / 100),
    abs_of_pos (polyB_pos (mul_pos hu hs))]
  dsimp only [B]
  nlinarith only [hB', hR]

theorem outerK_linear_bound {u : ℝ} (hu : 0 < u) :
    ∃ B ≥ 0, ∀ s > 0, |outerK u s| ≤ B * s := by
  refine ⟨1 + 2 * u, by positivity, ?_⟩
  intro s hs
  have h₀ : 0 ≤ 1 - Real.exp (-s) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.le))
  have h₁ : 1 - Real.exp (-s) ≤ s := by linarith [Real.add_one_le_exp (-s)]
  have h₂ : 0 ≤ 1 - (12 / 25) * (1 - Real.exp (-s)) := by linarith [Real.exp_pos (-s)]
  have h₃ : 1 - (12 / 25) * (1 - Real.exp (-s)) ≤ 1 := by linarith only [h₀]
  unfold outerK
  apply (abs_sub _ _).trans
  rw [abs_of_nonneg (mul_nonneg (mul_pos hu hs).le h₂),
    abs_of_nonneg (mul_nonneg (by positivity : 0 ≤ 1 + u) h₀)]
  have hA := mul_le_of_le_one_right (mul_pos hu hs).le h₃
  have hB := mul_le_mul_of_nonneg_left h₁ (by positivity : 0 ≤ 1 + u)
  nlinarith only [hA, hB]

end ACS12.GammaMeasure

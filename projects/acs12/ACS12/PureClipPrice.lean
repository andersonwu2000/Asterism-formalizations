import ACS12.PureClipLower
import ACS12.UnimodalSampling

/-! The full negative tail of the pure right kernel pays one complete clipping price. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter

noncomputable def clipMajorant (p δ C t : ℝ) : ℝ :=
  p * δ * t ^ (-(p + 2)) * max 0 (t - C)

private theorem clipMajorant_integral {p δ C : ℝ} (hp : 0 < p) (hC : 0 < C) :
    IntegrableOn (clipMajorant p δ C) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, clipMajorant p δ C t) = δ * C ^ (-p) / (p + 1) := by
  let f (t : ℝ) := p * δ * (t ^ (-(p + 1)) - C * t ^ (-(p + 2)))
  have h₁ : IntegrableOn (fun t : ℝ => t ^ (-(p + 1))) (Ioi C) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hC
  have h₂ : IntegrableOn (fun t : ℝ => t ^ (-(p + 2))) (Ioi C) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hC
  have hf : IntegrableOn f (Ioi C) := (h₁.sub (h₂.const_mul C)).const_mul (p * δ)
  have hE : clipMajorant p δ C = (Ioi C).indicator f := by
    funext t
    by_cases ht : C < t
    · rw [indicator_of_mem (show t ∈ Ioi C from ht), clipMajorant, max_eq_right (sub_nonneg.mpr ht.le)]
      have ht₀ := hC.trans ht
      have hPow : t ^ (-(p + 2)) * t = t ^ (-(p + 1)) := by
        rw [show -(p + 2) = -(p + 1) - 1 by ring,
          Real.rpow_sub_one ht₀.ne', div_mul_cancel₀ _ ht₀.ne']
      dsimp only [f]
      linear_combination (p * δ) * hPow
    · rw [indicator_of_notMem (show t ∉ Ioi C from ht), clipMajorant,
        max_eq_left (sub_nonpos.mpr (le_of_not_gt ht)), mul_zero]
  have hEq : Ioi C ∩ Ioi (0 : ℝ) = Ioi C :=
    inter_eq_left.mpr (Ioi_subset_Ioi hC.le)
  rw [hE]
  constructor
  · rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioi, IntegrableOn,
      Measure.restrict_restrict measurableSet_Ioi, hEq]
    exact hf
  · rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, hEq]
    dsimp only [f]
    rw [integral_const_mul, integral_sub h₁ (h₂.const_mul C), integral_const_mul,
      integral_Ioi_rpow_of_lt (by linarith : -(p + 1) < -1) hC,
      integral_Ioi_rpow_of_lt (by linarith : -(p + 2) < -1) hC,
      show -(p + 1) + 1 = -p by ring, show -(p + 2) + 1 = -p - 1 by ring,
      Real.rpow_sub_one hC.ne', show -p - 1 = -(p + 1) by ring]
    field_simp [hC.ne', hp.ne', (add_pos hp zero_lt_one).ne']
    ring

private theorem clipMajorant_shape {p δ C : ℝ} (hp : 0 < p) (hδ : 0 ≤ δ) (hC : 0 < C) :
    let T := C * (p + 2) / (p + 1)
    MonotoneOn (clipMajorant p δ C) (Ioc 0 T) ∧ AntitoneOn (clipMajorant p δ C) (Ici T) := by
  let T := C * (p + 2) / (p + 1)
  let f (t : ℝ) := p * δ * t ^ (-(p + 2)) * (t - C)
  let D (t : ℝ) := p * δ * t ^ (-(p + 3)) * ((p + 2) * C - (p + 1) * t)
  have hp' : 0 < p + 1 := by positivity
  have hTC : C < T := (lt_div_iff₀ hp').mpr (by nlinarith)
  have hEq (t : ℝ) (ht : C ≤ t) : clipMajorant p δ C t = f t := by
    rw [clipMajorant, max_eq_right (sub_nonneg.mpr ht)]
  have hD (t : ℝ) (ht : 0 < t) : HasDerivAt f (D t) t := by
    have hPow := Real.hasDerivAt_rpow_const (p := -(p + 2)) (Or.inl ht.ne')
    convert (hPow.const_mul (p * δ)).mul ((hasDerivAt_id t).sub_const C) using 1
    · dsimp only [D, id_eq]
      rw [show -(p + 2) - 1 = -(p + 3) by ring]
      have hT : t ^ (-(p + 2)) = t ^ (-(p + 3)) * t := by
        rw [show -(p + 3) = -(p + 2) - 1 by ring,
          Real.rpow_sub_one ht.ne', div_mul_cancel₀ _ ht.ne']
      rw [hT]
      ring
  have hB : T * (p + 1) = C * (p + 2) := div_mul_cancel₀ _ hp'.ne'
  have hMono : MonotoneOn f (Icc C T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun t ht => (hD t (hC.trans_le ht.1)).continuousAt.continuousWithinAt
    · exact fun t ht => (hD t (hC.trans_le (interior_subset ht).1)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Icc C T := interior_subset ht
      have ht₀ := hC.trans_le ht'.1
      rw [(hD t ht₀).deriv]
      apply mul_nonneg (mul_nonneg (mul_nonneg hp.le hδ) (Real.rpow_nonneg ht₀.le _))
      linarith only [hB, mul_le_mul_of_nonneg_right ht'.2 hp'.le]
  have hAnti : AntitoneOn f (Ici T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · exact fun t ht => (hD t (hC.trans (hTC.trans_le ht))).continuousAt.continuousWithinAt
    · exact fun t ht => (hD t (hC.trans (hTC.trans_le (interior_subset ht)))).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : T ≤ t := interior_subset ht
      have ht₀ := hC.trans (hTC.trans_le ht')
      rw [(hD t ht₀).deriv]
      apply mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (mul_nonneg hp.le hδ) (Real.rpow_nonneg ht₀.le _))
      linarith only [hB, mul_le_mul_of_nonneg_right ht' hp'.le]
  refine ⟨?_, ?_⟩
  · intro x hx y hy hxy
    by_cases h : C ≤ x
    · rw [hEq x h, hEq y (h.trans hxy)]
      exact hMono ⟨h, hx.2⟩ ⟨h.trans hxy, hy.2⟩ hxy
    · rw [clipMajorant, max_eq_left (sub_nonpos.mpr (le_of_not_ge h)), mul_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg hp.le hδ) (Real.rpow_nonneg hy.1.le _)) (le_max_left _ _)
  · intro x hx y hy hxy
    rw [hEq x (hTC.le.trans hx), hEq y (hTC.le.trans hy)]
    exact hAnti hx hy hxy

private theorem clipMajorant_peak_le {p δ C t : ℝ} (hp : 0 < p) (hδ : 0 ≤ δ)
    (hC : 0 < C) (ht : 0 < t) :
    clipMajorant p δ C t ≤ p * δ * C ^ (-(p + 1)) / (2 * (p + 2)) := by
  let T := C * (p + 2) / (p + 1)
  have hp' : 0 < p + 1 := by positivity
  have hTC : C < T := (lt_div_iff₀ hp').mpr (by nlinarith)
  obtain ⟨hInc, hDec⟩ := clipMajorant_shape hp hδ hC
  have hPeak : clipMajorant p δ C t ≤ clipMajorant p δ C T := by
    rcases le_total t T with h | h
    · exact hInc ⟨ht, h⟩ ⟨hC.trans hTC, le_rfl⟩ h
    · exact hDec (mem_Ici.mpr (show T ≤ T from le_rfl)) (mem_Ici.mpr h) h
  refine hPeak.trans ?_
  let k := (p + 2) / (p + 1)
  have hk : 0 < k := by dsimp only [k]; positivity
  have hk' : k = 1 + (p + 1)⁻¹ := by
    dsimp only [k]
    field_simp [hp'.ne']
    ring
  have hPow : 2 ≤ k ^ (p + 1) := by
    have h := one_add_mul_self_lt_rpow_one_add (s := (p + 1)⁻¹)
      ((by norm_num : (-1 : ℝ) ≤ 0).trans (inv_nonneg.mpr hp'.le))
      (inv_ne_zero hp'.ne') (by linarith : 1 < p + 1)
    rw [mul_inv_cancel₀ hp'.ne', ← hk'] at h
    norm_num at h
    exact h.le
  have hPow' : k ^ (-(p + 1)) ≤ 1 / 2 := by
    rw [Real.rpow_neg hk.le, ← one_div]
    exact div_le_div_of_nonneg_left zero_le_one (by norm_num) hPow
  have hT : T = C * k := by dsimp only [T, k]; ring
  have hGap : T - C = C / (p + 1) := by dsimp only [T]; field_simp [hp'.ne']; ring
  have hStep : k ^ (-(p + 2)) = k ^ (-(p + 1)) / k := by
    rw [show -(p + 2) = -(p + 1) - 1 by ring, Real.rpow_sub_one hk.ne']
  have hScale : C ^ (-(p + 2)) * C = C ^ (-(p + 1)) := by
    rw [show -(p + 2) = -(p + 1) - 1 by ring, Real.rpow_sub_one hC.ne', div_mul_cancel₀ _ hC.ne']
  rw [clipMajorant, max_eq_right (sub_nonneg.mpr hTC.le), hGap, hT, Real.mul_rpow hC.le hk.le, hStep]
  calc
    _ = (p * δ * (C ^ (-(p + 2)) * C) * k ^ (-(p + 1))) / (k * (p + 1)) := by rw [div_mul_eq_div_div]; ring
    _ = (p * δ * C ^ (-(p + 1)) / (p + 2)) * k ^ (-(p + 1)) := by
      rw [hScale, show k * (p + 1) = p + 2 from div_mul_cancel₀ _ hp'.ne']
      ring
    _ ≤ (p * δ * C ^ (-(p + 1)) / (p + 2)) * (1 / 2) :=
      mul_le_mul_of_nonneg_left hPow' (by positivity)
    _ = _ := by rw [mul_comm (2 : ℝ), div_mul_eq_div_div]; ring

private theorem clipMajorant_head_summable {p δ C t q : ℝ} (hp : 1 ≤ p) (hδ : 0 ≤ δ)
    (hC : 0 < C) (ht : 0 < t) (hq : 0 < q) :
    Summable (fun j : ℕ => clipMajorant p δ C (t + j * q)) := by
  let f := clipMajorant p δ C
  have hp₀ := zero_lt_one.trans_le hp
  have hPos (x : ℝ) (hx : 0 < x) : 0 ≤ f x := by
    unfold f clipMajorant
    positivity
  have hB (x : ℝ) (hx : 0 < x) : f x ≤ (p * δ * C ^ (-(p - 1))) / x ^ 2 := by
    change clipMajorant p δ C x ≤ _
    rcases le_total x C with h | h
    · rw [clipMajorant, max_eq_left (sub_nonpos.mpr h), mul_zero]
      positivity
    · rw [clipMajorant, max_eq_right (sub_nonneg.mpr h)]
      have hX : x ^ (-(p + 2)) * x = x ^ (-(p - 1)) / x ^ 2 := by
        rw [show -(p + 2) = -(p + 1) - 1 by ring,
          Real.rpow_sub_one hx.ne', div_mul_cancel₀ _ hx.ne',
          show -(p + 1) = -(p - 1) - 2 by ring, Real.rpow_sub hx, Real.rpow_two]
      calc
        _ ≤ p * δ * x ^ (-(p + 2)) * x :=
          mul_le_mul_of_nonneg_left (sub_le_self _ hC.le) (by positivity)
        _ = p * δ * (x ^ (-(p - 1)) / x ^ 2) := by rw [mul_assoc, hX]
        _ ≤ _ := by
          rw [← mul_div_assoc]
          apply div_le_div_of_nonneg_right _ (sq_nonneg _)
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hC h (by linarith)) (by positivity)
  exact summable_of_power_decay f (p * δ * C ^ (-(p - 1))) t q 2
    (by decide) (by positivity) ht hq hPos hB

private theorem clipMajorant_summable {p δ C t q : ℝ} (hp : 1 ≤ p) (hδ : 0 ≤ δ)
    (hC : 0 < C) (ht : 0 ≤ t) (hq : 0 < q) :
    Summable (fun j : ℕ => clipMajorant p δ C (t + ((j + 1 : ℕ) : ℝ) * q)) := by
  apply (clipMajorant_head_summable hp hδ hC (add_pos_of_nonneg_of_pos ht hq) hq).congr
  intro j
  apply congrArg (clipMajorant p δ C)
  push_cast
  ring

theorem clipMajorant_tail_le {p δ C t q : ℝ} (hp : 1 ≤ p) (hδ : 0 ≤ δ)
    (hC : 0 < C) (ht : 0 ≤ t) (hq : 0 < q) :
    samplingTail (clipMajorant p δ C) t q ≤
      δ * C ^ (-p) / (p + 1) + q * (p * δ * C ^ (-(p + 1)) / (2 * (p + 2))) := by
  let f := clipMajorant p δ C
  have hp₀ := zero_lt_one.trans_le hp
  obtain ⟨hI, hInt⟩ := clipMajorant_integral (δ := δ) hp₀ hC
  obtain ⟨hInc, hDec⟩ := clipMajorant_shape hp₀ hδ hC
  have hCont : ContinuousOn f (Ioi 0) := by
    unfold f clipMajorant
    exact ((continuousOn_const.mul (continuousOn_id.rpow_const (fun x hx => Or.inl
      (mem_Ioi.mp hx).ne'))).mul (continuousOn_const.sup (continuousOn_id.sub continuousOn_const)))
  have hPos (x : ℝ) (hx : 0 < x) : 0 ≤ f x := by
    unfold f clipMajorant
    positivity
  have hSum := clipMajorant_head_summable hp hδ hC (add_pos_of_nonneg_of_pos ht hq) hq
  have hMin {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) :
      min (f a) (f c) ≤ f b := by
    rcases le_total b (C * (p + 2) / (p + 1)) with h | h
    · exact (min_le_left _ _).trans (hInc ⟨ha, hab.trans h⟩ ⟨ha.trans_le hab, h⟩ hab)
    · exact (min_le_right _ _).trans (hDec h (h.trans hbc) hbc)
  rw [samplingTail_eq_shift, ← hInt]
  exact samplingHead_le_integral_add_peak (add_pos_of_nonneg_of_pos ht hq) hq hCont hI hPos
    (fun x hx => clipMajorant_peak_le hp₀ hδ hC hx) hMin hSum

private theorem outerCut_polynomial {p u : ℝ} (hp : 1 ≤ p) (hu : 7 / 8 ≤ u) (hu₁ : u ≤ 1) :
    let δ := 1 - u
    let C := (7 / 4) * (p + 1)
    δ * C ^ 2 - (1 / 2 - middleA u) * (p + 1) * C +
      (1 / 6 - middleA u / 2) * (p + 1) * (p + 2) < 0 := by
  let δ := 1 - u
  have hδ : 0 ≤ δ := sub_nonneg.mpr hu₁
  have hδ' : δ ≤ 1 / 8 := by dsimp only [δ]; linarith
  have ha : middleA u = (6 / 25) * (1 - δ ^ 2) := by unfold middleA; dsimp only [δ]; ring
  have hCoeff : 0 ≤ (49 / 16) * (p + 1) - ((3 / 10) * p + 9 / 50) * (1 / 8 + δ) := by
    have hB := mul_le_mul_of_nonneg_left (show 1 / 8 + δ ≤ 1 / 4 by linarith)
      (show 0 ≤ (3 / 10) * p + 9 / 50 by linarith)
    linarith only [hB, hp]
  have hNeg : δ * (49 / 16) * (p + 1) - (13 / 50 + 6 / 25 * δ ^ 2) * (7 / 4) * (p + 1) +
      (7 / 150 + 3 / 25 * δ ^ 2) * (p + 2) < 0 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hδ') hCoeff, hp]
  change _ < 0
  rw [ha]
  convert mul_neg_of_neg_of_pos hNeg (show 0 < p + 1 by linarith) using 1
  ring

theorem pureRightNegative_le_majorant_of_cut {p L u t C : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hu₀ : 0 < u) (hu₁ : u ≤ 1) (ht : 0 < t) (hC : 0 < C)
    (hCut : (1 - u) * C ^ 2 - (1 / 2 - middleA u) * (p + 1) * C +
      (1 / 6 - middleA u / 2) * (p + 1) * (p + 2) < 0) :
    lawRightNegative p L 0 u t ≤ clipMajorant p (1 - u) C t := by
  let δ := 1 - u
  let A := (1 / 2 - middleA u) * (p + 1)
  let B := (1 / 6 - middleA u / 2) * (p + 1) * (p + 2)
  have hp₀ := zero_lt_one.trans_le hp
  have hδ : 0 ≤ δ := sub_nonneg.mpr hu₁
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg (mul_nonneg (by linarith [middleA_le u]) (by positivity)) (by positivity)
  change δ * C ^ 2 - A * C + B < 0 at hCut
  have hAC : δ * C + B / C < A := by
    apply (lt_of_mul_lt_mul_right _ hC.le)
    have hE : (δ * C + B / C) * C = δ * C ^ 2 + B := by
      rw [add_mul, div_mul_cancel₀ _ hC.ne']
      ring
    rw [hE]
    linarith only [hCut]
  by_cases h : t ≤ C
  · have hQ : 0 < -δ + A / C - B / C ^ 2 := by
      apply (lt_of_mul_lt_mul_right _ (sq_nonneg C))
      have hE : (-δ + A / C - B / C ^ 2) * C ^ 2 = -(δ * C ^ 2 - A * C + B) := by
        field_simp [hC.ne']
        ring
      rw [zero_mul, hE]
      exact neg_pos.mpr hCut
    have hP := (mul_pos (mul_pos hp₀ (Real.rpow_pos_of_pos hC _)) hQ).trans
      (pureRight_quadratic_lower hp hp₂ hu₀ hu₁ hC)
    have hY : 0 < lawRightTest p L 0 u C := by rw [lawRightTest_zero hp hp₂ hL hC]; exact hP
    have hClip := lawRightClip_antitone hp hp₂ hL (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩)
      (u := u) ht hC h
    unfold lawRightClip at hClip
    rw [max_eq_right hY.le] at hClip
    have hT : 0 ≤ lawRightTest p L 0 u t := by
      by_contra! hT
      rw [max_eq_left hT.le] at hClip
      exact hY.not_ge hClip
    rw [lawRightNegative, max_eq_left (neg_nonpos.mpr hT)]
    unfold clipMajorant
    positivity
  · have hCt : C ≤ t := le_of_not_ge h
    have hBC := div_le_div_of_nonneg_left hB hC hCt
    have hQ : δ - A / t + B / t ^ 2 ≤ δ * (t - C) / t := by
      have hW : (δ - A / t + B / t ^ 2) * t = δ * t - A + B / t := by
        field_simp [ht.ne']
      apply le_of_mul_le_mul_right _ ht
      rw [hW, div_mul_cancel₀ _ ht.ne']
      nlinarith only [hAC, hBC]
    have hBound := pureRight_quadratic_lower hp hp₂ hu₀ hu₁ ht
    have hS : -pureRight p u t ≤ p * t ^ (-(p + 1)) * (δ * (t - C) / t) := by
      have hB' := mul_le_mul_of_nonneg_left hQ (mul_nonneg hp₀.le (Real.rpow_nonneg ht.le (-(p + 1))))
      dsimp only [δ, A, B] at hB' ⊢
      nlinarith only [hBound, hB']
    rw [lawRightNegative, lawRightTest_zero hp hp₂ hL ht, clipMajorant,
      max_eq_right (sub_nonneg.mpr hCt)]
    apply max_le (mul_nonneg (mul_nonneg (mul_nonneg hp₀.le hδ)
      (Real.rpow_nonneg ht.le _)) (sub_nonneg.mpr hCt))
    refine hS.trans_eq ?_
    rw [show -(p + 2) = -(p + 1) - 1 by ring, Real.rpow_sub_one ht.ne']
    ring

theorem pureRightNegative_le_majorant {p L u t : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hL : 0 < L)
    (hu : 7 / 8 ≤ u) (hu₁ : u ≤ 1) (ht : 0 < t) :
    lawRightNegative p L 0 u t ≤ clipMajorant p (1 - u) ((7 / 4) * (p + 1)) t :=
  pureRightNegative_le_majorant_of_cut hp hp₂ hL ((by norm_num : (0 : ℝ) < 7 / 8).trans_le hu)
    hu₁ ht (by positivity) (outerCut_polynomial hp hu hu₁)

noncomputable def outerClipPrice (p : ℝ) : ℝ :=
  ((7 / 4) * (p + 1)) ^ (-p) / (p + 1) * (1 + 2 * p / (7 * (p + 2)))

theorem pureRightNegative_tail_le_of_cut {p L u t q C : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hu₀ : 0 < u) (hu₁ : u ≤ 1) (ht : 0 ≤ t) (hq : 0 < q) (hC : 0 < C)
    (hCut : (1 - u) * C ^ 2 - (1 / 2 - middleA u) * (p + 1) * C +
      (1 / 6 - middleA u / 2) * (p + 1) * (p + 2) < 0) :
    samplingTail (lawRightNegative p L 0 u) t q ≤
      (1 - u) * C ^ (-p) / (p + 1) + q * (p * (1 - u) * C ^ (-(p + 1)) / (2 * (p + 2))) := by
  let δ := 1 - u
  let x (j : ℕ) := t + ((j + 1 : ℕ) : ℝ) * q
  have hδ : 0 ≤ δ := sub_nonneg.mpr hu₁
  have hX (j : ℕ) : 0 < x j := add_pos_of_nonneg_of_pos ht (mul_pos (by positivity) hq)
  have hNeg := (lawRight_abs_samples_summable (u := u) hp hp₂ hL
    (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩) ht hq).of_nonneg_of_le
    (g := fun j => lawRightNegative p L 0 u (x j)) (fun _ => le_max_left _ _)
    (fun _ => max_le (abs_nonneg _) (neg_le_abs _))
  have hSumm : Summable (fun j => clipMajorant p δ C (x j)) :=
    clipMajorant_summable hp hδ hC ht hq
  have hPrice : samplingTail (lawRightNegative p L 0 u) t q ≤ samplingTail (clipMajorant p δ C) t q :=
    mul_le_mul_of_nonneg_left (hNeg.tsum_le_tsum
      (fun j => pureRightNegative_le_majorant_of_cut hp hp₂ hL hu₀ hu₁ (hX j) hC hCut) hSumm) hq.le
  exact hPrice.trans (clipMajorant_tail_le hp hδ hC ht hq)

theorem pureRightNegative_tail_le_price {p L u t q : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hL : 0 < L)
    (hu : 7 / 8 ≤ u) (hu₁ : u ≤ 1) (ht : 0 ≤ t) (hq : 0 < q) (hq₁ : q ≤ 1) :
    samplingTail (lawRightNegative p L 0 u) t q ≤ (1 - u) * outerClipPrice p := by
  let δ := 1 - u
  let C := (7 / 4) * (p + 1)
  have hδ : 0 ≤ δ := sub_nonneg.mpr hu₁
  have hC : 0 < C := by dsimp only [C]; positivity
  refine (pureRightNegative_tail_le_of_cut hp hp₂ hL ((by norm_num : (0 : ℝ) < 7 / 8).trans_le hu)
    hu₁ ht hq hC (outerCut_polynomial hp hu hu₁)).trans ?_
  refine (add_le_add_right (mul_le_of_le_one_left (by positivity : 0 ≤
      p * δ * C ^ (-(p + 1)) / (2 * (p + 2))) hq₁) _).trans_eq ?_
  unfold outerClipPrice
  change _ = δ * (C ^ (-p) / (p + 1) * (1 + 2 * p / (7 * (p + 2))))
  rw [show -(p + 1) = -p - 1 by ring, Real.rpow_sub_one hC.ne']
  dsimp only [C]
  field_simp [(show p + 1 ≠ 0 by positivity), (show p + 2 ≠ 0 by positivity)]
  ring

end ACS12.GammaMeasure

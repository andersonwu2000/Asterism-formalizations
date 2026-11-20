import ACS12.JointLowerRightResponse
import ACS12.PureCMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.SmoothSeries

/-! Dominated differentiation of all four original right-source streams. -/
namespace ACS12.GammaMeasure

open Set Filter
open scoped Topology

private noncomputable def rightSourceAtom (k : ℕ) (p j U : ℝ) : ℝ :=
  match k with
  | 0 => purePeanoA p U j
  | 1 => sourceRightD1 p j U
  | 2 => sourceRightD2 p j U
  | 3 => sourceRightD3 p j U
  | _ => sourceRightD4 p j U

private theorem rightSourceAtom_deriv {k : ℕ} (hk : k < 4) (p j U : ℝ) (h : 0 < j + U) :
    HasDerivAt (rightSourceAtom k p j) (rightSourceAtom (k + 1) p j U) U := by
  interval_cases k
  · exact sourceRight_deriv1 p j U h
  · exact sourceRight_deriv2 p j U h
  · exact sourceRight_deriv3 p j U h
  · exact sourceRight_deriv4 p j U h

private theorem rightSource_deriv_bounds {p j U : ℝ} (hp : 1 ≤ p) (hP : p ≤ 2) (hj : 1 ≤ j)
    (hU : 0 ≤ U) (hU' : U ≤ 2) :
    |sourceRightD1 p j U| ≤ 2000 * j ^ (-3 : ℝ) ∧
    |sourceRightD2 p j U| ≤ 2000 * j ^ (-3 : ℝ) ∧
    |sourceRightD3 p j U| ≤ 2000 * j ^ (-3 : ℝ) ∧
    |sourceRightD4 p j U| ≤ 2000 * j ^ (-3 : ℝ) := by
  let q := j ^ (-3 : ℝ)
  have hp₀ := zero_lt_one.trans_le hp
  have hj₀ := zero_lt_one.trans_le hj
  have hJ : j ≤ j + U := le_add_of_nonneg_right hU
  have hJ₀ : 0 < j + U := hj₀.trans_le hJ
  have hq : 0 ≤ q := Real.rpow_nonneg hj₀.le _
  have hR (k : ℝ) (hk : 0 ≤ k) : 0 ≤ (j + U) ^ (-p - 2 - k) ∧ (j + U) ^ (-p - 2 - k) ≤ q := by
    refine ⟨Real.rpow_nonneg hJ₀.le _,?_⟩
    exact (Real.rpow_le_rpow_of_nonpos hj₀ hJ (by linarith only [hp,hk])).trans
      (Real.rpow_le_rpow_of_exponent_le hj (by linarith only [hp,hk]))
  obtain ⟨h₀₀,h₀⟩ := hR 0 (by norm_num)
  obtain ⟨h₁₀,h₁⟩ := hR 1 (by norm_num)
  obtain ⟨h₂₀,h₂⟩ := hR 2 (by norm_num)
  obtain ⟨h₃₀,h₃⟩ := hR 3 (by norm_num)
  rw [sub_zero] at h₀₀ h₀
  rw [show -p - 2 - 1 = -p - 3 by ring] at h₁₀ h₁
  rw [show -p - 2 - 2 = -p - 4 by ring] at h₂₀ h₂
  rw [show -p - 2 - 3 = -p - 5 by ring] at h₃₀ h₃
  have hB : 0 ≤ p * (p + 1) := by positivity
  have hB' : p * (p + 1) ≤ 6 := by
    have h := mul_le_mul hP (show p + 1 ≤ 3 by linarith only [hP]) (by positivity) (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at h
    exact h
  have hB₂ : p * (p + 1) * (p + 2) ≤ 24 := by
    have h := mul_le_mul hB' (show p + 2 ≤ 4 by linarith only [hP]) (by positivity) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num at h
    exact h
  have hB₃ : p * (p + 1) * (p + 2) * (p + 3) ≤ 120 := by
    have h := mul_le_mul hB₂ (show p + 3 ≤ 5 by linarith only [hP]) (by positivity) (by norm_num : (0 : ℝ) ≤ 24)
    norm_num at h
    exact h
  have hP₁ (c : ℝ) (hc : 0 ≤ c) : (p + c) * U ≤ (2 + c) * 2 :=
    mul_le_mul (add_le_add hP le_rfl) hU' hU (by positivity)
  have hTri (x y : ℝ) : |x - y| ≤ |x| + |y| := by
    simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le x 0 y
  have hTri' (x y : ℝ) : |-x + y| ≤ |x| + |y| := by
    rw [← sub_eq_neg_add,abs_sub_comm]
    exact hTri x y
  change _ ≤ 2000 * q ∧ _ ≤ 2000 * q ∧ _ ≤ 2000 * q ∧ _ ≤ 2000 * q
  refine ⟨?_,?_,?_,?_⟩
  · unfold sourceRightD1
    rw [abs_of_nonneg (by positivity)]
    have h := mul_le_mul (mul_le_mul hB' hU' hU (by norm_num : (0 : ℝ) ≤ 6)) h₀ h₀₀ (by norm_num)
    nlinarith only [h,hq]
  · unfold sourceRightD2
    rw [abs_mul,abs_of_nonneg hB]
    have h₈ := mul_le_mul (hP₁ 2 (by norm_num)) h₁ h₁₀ (by norm_num)
    have h := hTri ((j + U) ^ (-p - 2)) ((p + 2) * U * (j + U) ^ (-p - 3))
    rw [abs_of_nonneg h₀₀,abs_of_nonneg (mul_nonneg (by positivity : 0 ≤ (p + 2) * U) h₁₀)] at h
    have h' : |(j + U) ^ (-p - 2) - (p + 2) * U * (j + U) ^ (-p - 3)| ≤ 9 * q :=
      h.trans (by nlinarith only [h₀,h₈])
    have h'' := mul_le_mul hB' h' (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    nlinarith only [h'',hq]
  · unfold sourceRightD3
    rw [abs_mul,abs_of_nonneg (by positivity)]
    have h₁₀' := mul_le_mul (hP₁ 3 (by norm_num)) h₂ h₂₀ (by norm_num)
    have h := hTri' (2 * (j + U) ^ (-p - 3)) ((p + 3) * U * (j + U) ^ (-p - 4))
    rw [abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) h₁₀),
      abs_of_nonneg (mul_nonneg (by positivity : 0 ≤ (p + 3) * U) h₂₀)] at h
    have h' : |-2 * (j + U) ^ (-p - 3) + (p + 3) * U * (j + U) ^ (-p - 4)| ≤ 12 * q := by
      rw [neg_mul]
      exact h.trans (by nlinarith only [h₁,h₁₀'])
    have h'' := mul_le_mul hB₂ h' (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 24)
    nlinarith only [h'',hq]
  · unfold sourceRightD4
    rw [abs_mul,abs_of_nonneg (by positivity)]
    have h₁₂ := mul_le_mul (hP₁ 4 (by norm_num)) h₃ h₃₀ (by norm_num)
    have h := hTri (3 * (j + U) ^ (-p - 4)) ((p + 4) * U * (j + U) ^ (-p - 5))
    rw [abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) h₂₀),
      abs_of_nonneg (mul_nonneg (by positivity : 0 ≤ (p + 4) * U) h₃₀)] at h
    have h' : |3 * (j + U) ^ (-p - 4) - (p + 4) * U * (j + U) ^ (-p - 5)| ≤ 15 * q :=
      h.trans (by nlinarith only [h₂,h₁₂])
    have h'' := mul_le_mul hB₃ h' (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 120)
    nlinarith only [h'',hq]

private theorem rightSourceAtom_bound {p j U : ℝ} (hp : 1 ≤ p) (hP : p ≤ 2) (hj : 1 ≤ j)
    (hU : U ∈ Ioo 0 2) {k : ℕ} (hk : k ≤ 4) :
    ‖rightSourceAtom k p j U‖ ≤ 4000 * j ^ (-3 : ℝ) := by
  rw [Real.norm_eq_abs]
  have hj₀ := zero_lt_one.trans_le hj
  have hDom := rightSource_deriv_bounds hp hP hj hU.1.le hU.2.le
  have hQ : 2000 * j ^ (-3 : ℝ) ≤ 4000 * j ^ (-3 : ℝ) :=
    mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg hj₀.le _)
  interval_cases k
  · change |purePeanoA p U j| ≤ _
    have hC : ContinuousOn (fun y => purePeanoA p y j) (Icc 0 U) := by
      intro y hy
      exact (sourceRight_deriv1 p j y (add_pos_of_pos_of_nonneg hj₀ hy.1)).continuousAt.continuousWithinAt
    have hD : DifferentiableOn ℝ (fun y => purePeanoA p y j) (Ioo 0 U) := by
      intro y hy
      exact (sourceRight_deriv1 p j y (add_pos hj₀ hy.1)).differentiableAt.differentiableWithinAt
    obtain ⟨y,hy,h⟩ := exists_deriv_eq_slope (fun y => purePeanoA p y j) hU.1 hC hD
    rw [(sourceRight_deriv1 p j y (add_pos hj₀ hy.1)).deriv,
      show purePeanoA p 0 j = 0 by simp [purePeanoA],sub_zero,sub_zero] at h
    have h' := (eq_div_iff hU.1.ne').mp h
    rw [← h',abs_mul,abs_of_pos hU.1]
    have hBound := (rightSource_deriv_bounds hp hP hj hy.1.le (hy.2.trans hU.2).le).1
    have hNon : 0 ≤ 2000 * j ^ (-3 : ℝ) := by positivity
    exact (mul_le_mul hBound hU.2.le hU.1.le hNon).trans (by ring_nf; exact le_rfl)
  · exact hDom.1.trans hQ
  · exact hDom.2.1.trans hQ
  · exact hDom.2.2.1.trans hQ
  · exact hDom.2.2.2.trans hQ

noncomputable def rightSourceSum (k : ℕ) (p U : ℝ) : ℝ :=
  ∑' j : ℕ, rightSourceAtom k p ((1 : ℝ) + j) U

private theorem rightSource_dominator : Summable (fun j : ℕ => (4000 : ℝ) * (1 + (j : ℝ)) ^ (-3 : ℝ)) := by
  have h := (powerTail_summable (q := (3 : ℝ)) (by norm_num) (1 : ℕ)).mul_left (4000 : ℝ)
  simpa only [Nat.cast_one] using h

private theorem rightSource_summable {p U : ℝ} (hp : 1 ≤ p) (hP : p ≤ 2) (hU : U ∈ Ioo 0 2)
    {k : ℕ} (hk : k ≤ 4) : Summable (fun j : ℕ => rightSourceAtom k p ((1 : ℝ) + j) U) :=
  Summable.of_norm_bounded rightSource_dominator fun j =>
    rightSourceAtom_bound hp hP (le_add_of_nonneg_right (Nat.cast_nonneg j)) hU hk

theorem rightSourceSum_hasDerivAt {p U : ℝ} (hp : 1 ≤ p) (hP : p ≤ 2) (hU : U ∈ Ioo 0 2)
    {k : ℕ} (hk : k < 4) : HasDerivAt (rightSourceSum k p) (rightSourceSum (k + 1) p U) U := by
  exact hasDerivAt_tsum_of_isPreconnected rightSource_dominator isOpen_Ioo (convex_Ioo 0 2).isPreconnected
    (fun j u hu => rightSourceAtom_deriv hk p ((1 : ℝ) + j) u (by have : 0 < u := hu.1; positivity))
    (fun j u hu => rightSourceAtom_bound hp hP (le_add_of_nonneg_right (Nat.cast_nonneg j)) hu (by omega))
    hU (rightSource_summable hp hP hU (by omega)) hU

noncomputable def lowerRightResponseTotal (p U : ℝ) : ℝ :=
  ∑' j : ℕ, lowerRightResponse p ((1 : ℝ) + j) U

private theorem lowerRightResponse_hasSum {p U : ℝ} (hp : 1 ≤ p) (hP : p ≤ 2) (hU : U ∈ Ioo 0 2) :
    HasSum (fun j : ℕ => lowerRightResponse p ((1 : ℝ) + j) U)
      (8 * (p - 1) * rightSourceSum 0 p U + 12 * (2 * U - 1) * rightSourceSum 1 p U +
        6 * (2 * U - 1) ^ 2 * rightSourceSum 2 p U / p +
        (2 * U - 1) ^ 3 * rightSourceSum 3 p U / (p * (p + 1))) := by
  have h₀ := (rightSource_summable hp hP hU (k := 0) (by decide)).hasSum.mul_left (8 * (p - 1))
  have h₁ := (rightSource_summable hp hP hU (k := 1) (by decide)).hasSum.mul_left (12 * (2 * U - 1))
  have h₂ := ((rightSource_summable hp hP hU (k := 2) (by decide)).hasSum.mul_left (6 * (2 * U - 1) ^ 2)).div_const p
  have h₃ := ((rightSource_summable hp hP hU (k := 3) (by decide)).hasSum.mul_left ((2 * U - 1) ^ 3)).div_const (p * (p + 1))
  exact ((h₀.add h₁).add h₂).add h₃

theorem lowerRightResponseTotal_eq {p U : ℝ} (hp : 1 ≤ p) (hP : p ≤ 2) (hU : U ∈ Ioo 0 2) :
    lowerRightResponseTotal p U =
      8 * (p - 1) * rightSourceSum 0 p U + 12 * (2 * U - 1) * rightSourceSum 1 p U +
        6 * (2 * U - 1) ^ 2 * rightSourceSum 2 p U / p +
        (2 * U - 1) ^ 3 * rightSourceSum 3 p U / (p * (p + 1)) :=
  (lowerRightResponse_hasSum hp hP hU).tsum_eq

theorem lowerRightResponseTotal_mono {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 2) :
    MonotoneOn (lowerRightResponseTotal p) (Icc 1 (7 / 6)) := by
  intro U hU V hV hUV
  have hA (u : ℝ) (hu : u ∈ Icc 1 (7 / 6)) : u ∈ Ioo 0 2 :=
    ⟨zero_lt_one.trans_le hu.1,hu.2.trans_lt (by norm_num)⟩
  exact (lowerRightResponse_hasSum hp hP (hA U hU)).summable.tsum_le_tsum
    (fun j : ℕ => (lowerRightResponse_strictMono hp
      (le_add_of_nonneg_right (Nat.cast_nonneg j))).monotoneOn hU hV hUV)
    (lowerRightResponse_hasSum hp hP (hA V hV)).summable

theorem rightSourceSum_zero_one {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 2) :
    rightSourceSum 0 p 1 = p + 1 - pureZ p := by
  let b (j : ℕ) := ((1 : ℝ) + j) ^ (-p)
  let c (j : ℕ) := p * ((2 : ℝ) + j) ^ (-(p + 1))
  let d (j : ℕ) := rightSourceAtom 0 p ((1 : ℝ) + j) 1
  have hp₀ := zero_lt_one.trans_le hp
  have hP' : 1 < p + 1 := by linarith only [hp]
  have hd : Summable d := rightSource_summable hp hP (by norm_num) (by decide)
  have hc : HasSum c (p * powerTail (p + 1) 2) := (powerTail_summable hP' 2).hasSum.mul_left p
  have hEq (j : ℕ) : d j = b j - b (j + 1) - c j := by
    unfold d b c
    simp only [rightSourceAtom,purePeanoA,one_mul,Nat.cast_succ]
    rw [show 1 + (j : ℝ) + 1 = 2 + (j : ℝ) by ring,
      show 1 + ((j : ℝ) + 1) = 2 + (j : ℝ) by ring]
  have hbS : Summable (fun j => b j - b (j + 1)) := (hd.add hc.summable).congr (fun j => by
    simp only [hEq,sub_add_cancel])
  have hb : HasSum (fun j => b j - b (j + 1)) 1 := by
    apply hbS.hasSum_iff_tendsto_nat.mpr
    have hL : Tendsto b atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hp₀).comp (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
    have h₀ : b 0 = 1 := by simp [b]
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hL
    simp only [sub_zero] at h
    apply h.congr
    intro j
    rw [Finset.sum_range_sub',h₀]
  have hS := hb.sub hc
  have hD : HasSum d (1 - p * powerTail (p + 1) 2) := hS.congr_fun hEq
  change (∑' j, d j) = _
  rw [hD.tsum_eq,powerTail_shift hP' 1,pureZ]
  norm_num
  ring

private theorem rightSourceSum_unit_derivatives {p : ℝ} (hp : 1 ≤ p) :
    rightSourceSum 1 p 1 = p * (p + 1) * powerTail (p + 2) 2 ∧
    rightSourceSum 2 p 1 = p * (p + 1) * (powerTail (p + 2) 2 - (p + 2) * powerTail (p + 3) 2) ∧
    rightSourceSum 3 p 1 = p * (p + 1) * (p + 2) *
      (-2 * powerTail (p + 3) 2 + (p + 3) * powerTail (p + 4) 2) := by
  have hS₂ := (powerTail_summable (q := p + 2) (by linarith only [hp]) 2).hasSum
  have hS₃ := (powerTail_summable (q := p + 3) (by linarith only [hp]) 2).hasSum
  have hS₄ := (powerTail_summable (q := p + 4) (by linarith only [hp]) 2).hasSum
  have hShift (j : ℕ) : (1 : ℝ) + (j : ℝ) + 1 = 2 + (j : ℝ) := by ring
  refine ⟨?_,?_,?_⟩
  · unfold rightSourceSum
    convert (hS₂.mul_left (p * (p + 1))).tsum_eq using 1
    apply tsum_congr
    intro j
    simp only [rightSourceAtom,sourceRightD1,mul_one,hShift,Nat.cast_ofNat,show -(p + 2) = -p - 2 by ring]
  · unfold rightSourceSum
    convert ((hS₂.sub (hS₃.mul_left (p + 2))).mul_left (p * (p + 1))).tsum_eq using 1
    apply tsum_congr
    intro j
    simp only [rightSourceAtom,sourceRightD2,mul_one,hShift,Nat.cast_ofNat,show -(p + 2) = -p - 2 by ring,
      show -(p + 3) = -p - 3 by ring]
  · unfold rightSourceSum
    convert (((hS₃.mul_left (-2 : ℝ)).add (hS₄.mul_left (p + 3))).mul_left (p * (p + 1) * (p + 2))).tsum_eq using 1
    apply tsum_congr
    intro j
    simp only [rightSourceAtom,sourceRightD3,mul_one,hShift,Nat.cast_ofNat,show -(p + 3) = -p - 3 by ring,
      show -(p + 4) = -p - 4 by ring]

theorem lowerRightResponseTotal_one {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 2) :
    lowerRightResponseTotal p 1 =
      8 * (p - 1) * (p + 1 - pureZ p) +
        6 * (2 * p + 1) * (p + 1) * powerTail (p + 2) 2 -
        (6 * p + 8) * (p + 2) * powerTail (p + 3) 2 +
        (p + 2) * (p + 3) * powerTail (p + 4) 2 := by
  obtain ⟨h₁,h₂,h₃⟩ := rightSourceSum_unit_derivatives hp
  rw [lowerRightResponseTotal_eq hp hP (by norm_num),rightSourceSum_zero_one hp hP,h₁,h₂,h₃]
  have hp₀ := zero_lt_one.trans_le hp
  field_simp [hp₀.ne',show p + 1 ≠ 0 by positivity]
  ring

theorem rightSourceSum_unit_first_two {p : ℝ} (hp : 1 ≤ p) :
    rightSourceSum 1 p 1 = p * (p + 1) * powerTail (p + 2) 2 ∧
      rightSourceSum 2 p 1 = p * (p + 1) * (powerTail (p + 2) 2 - (p + 2) * powerTail (p + 3) 2) :=
  ⟨(rightSourceSum_unit_derivatives hp).1,(rightSourceSum_unit_derivatives hp).2.1⟩

theorem rightSourceSum_zero_eq (p U : ℝ) :
    rightSourceSum 0 p U = ∑' j : ℕ, purePeanoA p U (1 + (j : ℝ)) := rfl

end ACS12.GammaMeasure

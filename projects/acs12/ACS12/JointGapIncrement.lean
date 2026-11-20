import ACS12.JointGapMoment
import ACS12.JointPureUpperDiagonal

/-! The finite gap increment with both original rows and the complete Bose return. -/
namespace ACS12.GammaMeasure

open Set Filter MeasureTheory CenteredCircle.AllN
open GammaDeficit (lineDensity)

noncomputable def jointGapRaw (u m r mu s : ℝ) : ℝ :=
  mu * ((m - r) * (1 - polyA (m * s)) + polyA (m * s) * (scaledExpTail s r - scaledExpTail s m)) -
    jointPureLambda * Real.exp (-s * m) * polyA (u * s) * adjacentBoseGap m r s

theorem jointPure_gap_eq_integral {p L u m r mu : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hu : 0 < u) (hm : 0 < m) (hr : 0 < r) :
    IntegrableOn (fun s => lineDensity p s * jointGapRaw u m r mu s) (Ioi 0) ∧
      jointPureValue p L u m r mu - jointPureValue p L u m m mu =
        ∫ s : ℝ in Ioi 0, lineDensity p s * jointGapRaw u m r mu s := by
  let hθ : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl,zero_le_one⟩
  let A (r s : ℝ) := lineDensity p s * polyA (u * s) * Real.exp (-s * m) * (r + scaledExpTail s r)
  let H (r s : ℝ) := lineDensity p s * fourthDensity u m r m s
  obtain ⟨hAr,hArE⟩ := lawPeanoHead_sampling hp hp₂ hL hθ hu hm hr .a
  obtain ⟨hAm,hAmE⟩ := lawPeanoHead_sampling hp hp₂ hL hθ hu hm hm .a
  obtain ⟨hHr,hHrE⟩ := fourthSourceRow_integral (m := m) hp hp₂ hL hθ hu hm hr
  obtain ⟨hHm,hHmE⟩ := fourthSourceRow_integral (m := m) hp hp₂ hL hθ hu hm hm
  simp only [lawPeanoDensity,densityPolynomial,lawDensity,sub_zero,one_mul,zero_mul,add_zero,lawSelf,mul_zero]
    at hAr hAm hHr hHm hArE hAmE hHrE hHmE
  change IntegrableOn (A r) (Ioi 0) at hAr
  change IntegrableOn (A m) (Ioi 0) at hAm
  change IntegrableOn (H r) (Ioi 0) at hHr
  change IntegrableOn (H m) (Ioi 0) at hHm
  have hEq (s : ℝ) :
      lineDensity p s * jointGapRaw u m r mu s =
        mu * (H r s - H m s) + jointPureLambda * (A r s - A m s) := by
    have hP : polyA (m * s) = 1 - (1 + m * s) * Real.exp (-s * m) := by
      unfold polyA
      rw [show -(m * s) = -s * m by ring]
    simp only [jointGapRaw,A,H,fourthDensity,adjacentBoseGap]
    linear_combination -mu * lineDensity p s * (m - r) * hP
  have hH : IntegrableOn (fun s => H r s - H m s) (Ioi 0) := hHr.sub hHm
  have hA : IntegrableOn (fun s => A r s - A m s) (Ioi 0) := hAr.sub hAm
  constructor
  · exact ((hH.const_mul mu).add (hA.const_mul jointPureLambda)).congr (Eventually.of_forall fun s => (hEq s).symm)
  · rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => hEq s),
      integral_add (hH.const_mul mu) (hA.const_mul jointPureLambda),integral_const_mul,integral_const_mul,
      integral_sub hHr hHm,integral_sub hAr hAm]
    unfold jointPureValue adjacentSourceLaw
    dsimp only [H,A]
    rw [hHrE,hHmE,hArE,hAmE]
    ring

noncomputable def jointGapRemainder (t s : ℝ) : ℝ :=
  scaledExpTail s t - scaledExpTail s 1 - (1 - t) * BoseShape.C s

theorem jointGapRemainder_bounds {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (ht₁ : t ≤ 1) :
    0 ≤ jointGapRemainder t s ∧
      jointGapRemainder t s ≤ (1 - t) ^ 2 / 2 * (s * (-BoseShape.C₁ (t * s))) := by
  let K := s * (-BoseShape.C₁ (t * s))
  let f (x : ℝ) := BoseShape.C (s * x) + K * x
  let g (x : ℝ) := jointGapRemainder x s
  let h (x : ℝ) := (1 - x) ^ 2 / 2 * K - g x
  have hC (x : ℝ) (hx : 0 < x) :
      HasDerivAt f (s * BoseShape.C₁ (s * x) + K) x := by
    convert ((BoseShape.C_deriv (mul_pos hs hx)).comp x ((hasDerivAt_id x).const_mul s)).add
      ((hasDerivAt_id x).const_mul K) using 1
    simp only [mul_one]
    ring
  have hF : MonotoneOn f (Icc t 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun x hx => (hC x (ht.trans_le hx.1)).continuousAt.continuousWithinAt
    · exact fun x hx => (hC x (ht.trans_le (interior_subset hx).1)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Icc t 1 := interior_subset hx
      have hx₀ := ht.trans_le hx'.1
      rw [(hC x hx₀).deriv]
      have hCmp := BoseShape.C₁_mono (mul_pos ht hs) (mul_pos hs hx₀)
        (show t * s ≤ s * x by nlinarith only [mul_le_mul_of_nonneg_left hx'.1 hs.le])
      dsimp only [K]
      linarith only [mul_le_mul_of_nonneg_left hCmp hs.le]
  have hG (x : ℝ) (hx : 0 < x) : HasDerivAt g (BoseShape.C s - BoseShape.C (s * x)) x := by
    convert ((scaledExpTail_derivative hs hx).sub_const (scaledExpTail s 1)).sub
      (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).mul_const (BoseShape.C s)) using 1
    simp only [zero_sub,one_mul,neg_mul,sub_neg_eq_add]
    ring
  have hH (x : ℝ) (hx : 0 < x) :
      HasDerivAt h (BoseShape.C (s * x) - BoseShape.C s - K * (1 - x)) x := by
    convert (((((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).pow 2).div_const 2).mul_const K).sub
      (hG x hx) using 1
    simp only [Pi.sub_apply,id_eq,zero_sub]
    ring
  have hGmono : AntitoneOn g (Icc t 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · exact fun x hx => (hG x (ht.trans_le hx.1)).continuousAt.continuousWithinAt
    · exact fun x hx => (hG x (ht.trans_le (interior_subset hx).1)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Icc t 1 := interior_subset hx
      have hx₀ := ht.trans_le hx'.1
      rw [(hG x hx₀).deriv]
      exact sub_nonpos.mpr (BoseShape.C_antitone (mul_pos hs hx₀) hs (by nlinarith only [mul_le_mul_of_nonneg_left hx'.2 hs.le]))
  have hHmono : AntitoneOn h (Icc t 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · exact fun x hx => (hH x (ht.trans_le hx.1)).continuousAt.continuousWithinAt
    · exact fun x hx => (hH x (ht.trans_le (interior_subset hx).1)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Icc t 1 := interior_subset hx
      rw [(hH x (ht.trans_le hx'.1)).deriv]
      have h := hF hx' (show (1 : ℝ) ∈ Icc t 1 from ⟨ht₁,le_rfl⟩) hx'.2
      simp only [f,mul_one] at h
      linarith only [h]
  have hA := hGmono ⟨le_rfl,ht₁⟩ ⟨ht₁,le_rfl⟩ ht₁
  have hB := hHmono ⟨le_rfl,ht₁⟩ ⟨ht₁,le_rfl⟩ ht₁
  have hg₁ : g 1 = 0 := by simp [g,jointGapRemainder]
  have hh₁ : h 1 = 0 := by simp [h,hg₁]
  rw [hg₁] at hA
  rw [hh₁] at hB
  exact ⟨hA, sub_nonneg.mp hB⟩

end ACS12.GammaMeasure

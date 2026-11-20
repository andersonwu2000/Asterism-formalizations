import ACS12.JointLogQAtoms

/-! The whole upper Q curvature bound from the same signed spatial slope. -/
namespace ACS12.GammaMeasure

open Set Filter MeasureTheory intervalIntegral
open scoped Topology

theorem zetaSlope_summable {p : ℝ} (hp : 1 ≤ p) (m : ℕ) (hm : 1 ≤ m) :
    Summable (fun j : ℕ => zetaCurvatureSlope p ((m : ℝ) + j)) := by
  have hq : 1 < p + 2 := by linarith only [hp]
  have h₀ := powerTail_summable hq m
  have h₁ := powerLogTail_summable hq 1 m hm
  have h₂ := powerLogTail_summable hq 2 m hm
  refine (((h₂.mul_left (-(p * (p + 1)))).add (h₁.mul_left (4 * p + 2))).sub (h₀.mul_left 2)).congr ?_
  intro j
  dsimp only [zetaCurvatureSlope,peanoExponentQuadratic,Pi.add_apply,Pi.sub_apply,pow_one]
  ring

theorem zetaSlope_tsum {p : ℝ} (hp : 1 ≤ p) (m : ℕ) (hm : 1 ≤ m) :
    (∑' j : ℕ, zetaCurvatureSlope p ((m : ℝ) + j)) =
      -(p * (p + 1)) * powerLogTail (p + 2) 2 m + (4 * p + 2) * powerLogTail (p + 2) 1 m -
        2 * powerTail (p + 2) m := by
  have hq : 1 < p + 2 := by linarith only [hp]
  have h₀ := (powerTail_summable hq m).hasSum.mul_left 2
  have h₁ := (powerLogTail_summable hq 1 m hm).hasSum.mul_left (4 * p + 2)
  have h₂ := (powerLogTail_summable hq 2 m hm).hasSum.mul_left (-(p * (p + 1)))
  have h := (h₂.add h₁).sub h₀
  unfold powerLogTail powerTail
  rw [← h.tsum_eq]
  apply tsum_congr
  intro j
  dsimp only [zetaCurvatureSlope,peanoExponentQuadratic,Pi.add_apply,Pi.sub_apply,pow_one]
  ring

noncomputable def pureQPrime (p : ℝ) : ℝ :=
  (2 * p + 1) * powerTail (p + 2) 1 - p * (p + 1) * powerLogTail (p + 2) 1 1

noncomputable def pureQSecond (p : ℝ) : ℝ :=
  2 * powerTail (p + 2) 1 - 2 * (2 * p + 1) * powerLogTail (p + 2) 1 1 +
    p * (p + 1) * powerLogTail (p + 2) 2 1

theorem pureQPrime_derivative {p : ℝ} (hp : -1 < p) : HasDerivAt pureQPrime (pureQSecond p) p :=
  pureQ_second_hasDerivAt hp

theorem pureQ_derivative {p : ℝ} (hp : -1 < p) : HasDerivAt pureQ (pureQPrime p) p :=
  pureQ_hasDerivAt hp

theorem pureQPrime_one_bounds : (16 / 5 : ℝ) < pureQPrime 1 ∧ pureQPrime 1 < 3211 / 1000 := by
  obtain ⟨h₁,h₂⟩ := powerTail_three_bounds
  obtain ⟨h₃,h₄⟩ := logMoment_three_bounds
  norm_num [pureQPrime]
  exact ⟨by linarith only [h₁,h₄],by linarith only [h₂,h₃]⟩

theorem pureQSecond_eq_tail {p : ℝ} (hp : 1 ≤ p) (k : ℕ) :
    pureQSecond p =
      -(∑ j ∈ Finset.range k, zetaCurvatureSlope p (1 + (j : ℝ))) -
        ∑' j : ℕ, zetaCurvatureSlope p ((1 + (k : ℝ)) + j) := by
  have h := (zetaSlope_summable hp 1 le_rfl).sum_add_tsum_nat_add k
  have hEq : (∑' j : ℕ, zetaCurvatureSlope p (((1 : ℕ) : ℝ) + ((j + k : ℕ) : ℝ))) =
      ∑' j : ℕ, zetaCurvatureSlope p ((1 + (k : ℝ)) + j) := by
    apply tsum_congr
    intro j
    push_cast
    congr 1
    ring
  rw [hEq,zetaSlope_tsum hp 1 le_rfl] at h
  simp only [Nat.cast_one] at h
  unfold pureQSecond
  linarith only [h]

private theorem zetaCurvature_four_lt {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    zetaCurvature p 4 < 3 / 200 := by
  let l := Real.log 4
  have hE : l = 2 * Real.log 2 := by
    dsimp only [l]
    rw [show (4 : ℝ) = 2 * 2 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hl : (1386 / 1000 : ℝ) < l := by linarith only [hE,Real.log_two_gt_d9]
  have hl' : l < 1387 / 1000 := by linarith only [hE,Real.log_two_lt_d9]
  have hD (x : ℝ) : HasDerivAt (fun p => zetaCurvature p 4)
      ((4 : ℝ) ^ (-(x + 1)) * l ^ 2 * (3 - x * l)) x := by
    have h := hasDerivAt_id x
    have hPow : HasDerivAt (fun q : ℝ => (4 : ℝ) ^ (-(q + 1))) ((4 : ℝ) ^ (-(x + 1)) * (-l)) x := by
      convert (h.add_const 1).neg.const_rpow (by norm_num : (0 : ℝ) < 4) using 1
      simp only [id_eq,Pi.neg_apply,l]
      ring
    have hLin : HasDerivAt (fun q : ℝ => q * l - 2) l x := by
      simpa only [one_mul] using (h.mul_const l).sub_const 2
    convert (hPow.mul_const l).mul hLin using 1
    ring
  have hM : MonotoneOn (fun p => zetaCurvature p 4) (Icc 1 (9 / 5)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun x _ => (hD x).continuousAt.continuousWithinAt
    · exact fun x _ => (hD x).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Icc (1 : ℝ) (9 / 5) := interior_subset hx
      rw [(hD x).deriv]
      have h := mul_le_mul hx'.2 hl'.le (by linarith only [hl]) (by linarith only [hx'.1])
      exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (sq_nonneg l)) (by linarith only [h])
  have h := hM ⟨hp,hP⟩ (show (9 / 5 : ℝ) ∈ Icc 1 (9 / 5) by constructor <;> norm_num) hP
  apply h.trans_lt
  have hW : (4 : ℝ) ^ (-(14 : ℝ) / 5) < 20618 / 1000000 :=
    fifth_rpow_upper (k := 14) (by norm_num) (by norm_num) (by norm_num)
  have hl₀ : 0 ≤ l := by linarith only [hl]
  have hB₀ : 0 ≤ (9 / 5) * l - 2 := by linarith only [hl]
  have hA := mul_le_mul hW.le hl'.le hl₀ (by norm_num)
  have hB := mul_le_mul hA (show (9 / 5) * l - 2 ≤ (9 / 5) * (1387 / 1000) - 2 by linarith only [hl'])
    hB₀ (by norm_num)
  change (4 : ℝ) ^ (-(9 / 5 + 1)) * l * ((9 / 5) * l - 2) < _
  rw [show -(9 / 5 + 1 : ℝ) = -(14 : ℝ) / 5 by norm_num]
  exact hB.trans_lt (by norm_num)

theorem negSlope_tail_le {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    (∑' j : ℕ, -zetaCurvatureSlope p (4 + (j : ℝ))) ≤ zetaCurvature p 4 + 3 / 1000 := by
  let g (x : ℝ) := -zetaCurvatureSlope p x
  let D (x : ℝ) := -zetaCurvatureSpatial p x
  let F (x : ℝ) := -zetaCurvature p x
  have hFin (N : ℕ) : (∑ j ∈ Finset.range N, g (4 + j)) ≤ F (4 + (N : ℝ)) - F 4 + 3 / 1000 := by
    have hI {a b : ℝ} (ha : 4 ≤ a) (hab : a ≤ b) :
        IntervalIntegrable g volume a b ∧ IntervalIntegrable (fun x => max 0 (-D x)) volume a b := by
      have hg : ContinuousOn g (Icc a b) := by
        intro x hx
        exact ((zetaCurvatureSlope_hasDerivAt p ((by norm_num : (0 : ℝ) < 4).trans_le (ha.trans hx.1))).neg).continuousAt.continuousWithinAt
      have hD : ContinuousOn D (Icc a b) :=
        (zetaCurvatureSpatial_continuousOn p).neg.mono
          (fun x hx => (by norm_num : (0 : ℝ) < 4).trans_le (ha.trans hx.1))
      exact ⟨hg.intervalIntegrable_of_Icc hab,
        (continuous_max.comp_continuousOn (continuousOn_const.prodMk hD.neg)).intervalIntegrable_of_Icc hab⟩
    have hCell (j : ℕ) : g (4 + (j : ℝ)) - (∫ x in (4 + j : ℝ)..(4 + (j + 1 : ℕ)), g x) ≤
        ∫ x in (4 + j : ℝ)..(4 + (j + 1 : ℕ)), max 0 (-D x) := by
      rw [Nat.cast_add,Nat.cast_one,← add_assoc]
      have hA : (0 : ℝ) < 4 + j := by positivity
      exact ACS12.leftSample_error_le
        (fun x hx => (zetaCurvatureSlope_hasDerivAt p (hA.trans_le hx.1)).neg)
        ((zetaCurvatureSpatial_continuousOn p).neg.mono (fun x hx => hA.trans_le hx.1))
    have hCellI (j : ℕ) := hI (a := 4 + (j : ℝ)) (b := 4 + ((j + 1 : ℕ) : ℝ))
      (le_add_of_nonneg_right (Nat.cast_nonneg _)) (add_le_add_right (Nat.cast_le.mpr (Nat.le_succ j)) _)
    have h := Finset.sum_le_sum (s := Finset.range N) (fun j _ => hCell j)
    rw [Finset.sum_sub_distrib,intervalIntegral.sum_integral_adjacent_intervals (a := fun j => 4 + (j : ℝ))
      (fun j _ => (hCellI j).1),intervalIntegral.sum_integral_adjacent_intervals (a := fun j => 4 + (j : ℝ))
      (fun j _ => (hCellI j).2),Nat.cast_zero,add_zero] at h
    let b : ℝ := 4 + (N : ℝ)
    have hb : 4 ≤ b := le_add_of_nonneg_right (Nat.cast_nonneg N)
    have hF : (∫ x in (4 : ℝ)..b, g x) = F b - F 4 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx =>
        (zetaCurvature_hasDerivAt p ((by norm_num : (0 : ℝ) < 4).trans_le (by
          rw [uIcc_of_le hb] at hx
          exact hx.1))).neg) (hI le_rfl hb).1
    rw [hF] at h
    have hV := zetaCurvature_positiveVariation_le_of_slope hp hP hb (by norm_num : (0 : ℝ) ≤ 3 / 1000)
      (fun _ hx => (zetaCurvatureSlope_gt_neg_three hp hP hx).le)
    simp only [D,neg_neg] at h
    linarith only [h,hV]
  have hT := ((zetaSlope_summable hp 4 (by decide)).neg.hasSum.tendsto_sum_nat)
  change Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, g (4 + j)) atTop
    (𝓝 (∑' j : ℕ, -zetaCurvatureSlope p (4 + (j : ℝ)))) at hT
  have hF : Tendsto F atTop (𝓝 0) := by
    have h := ((logPower_decay (show 0 < p + 1 by positivity) 2).const_mul p).sub
      ((logPower_decay (show 0 < p + 1 by positivity) 1).const_mul 2)
    have hN := h.neg
    simp only [mul_zero,sub_zero,neg_zero] at hN
    apply hN.congr'
    filter_upwards [] with x
    simp only [F,zetaCurvature,pow_one]
    ring
  have hb : Tendsto (fun N : ℕ => (4 : ℝ) + N) atTop atTop :=
    tendsto_atTop_mono (f := fun N : ℕ => (N : ℝ)) (fun N => by linarith) tendsto_natCast_atTop_atTop
  have hV := (((hF.comp hb).sub_const (F 4)).const_add (3 / 1000))
  have hV' : Tendsto (fun N : ℕ => F (4 + (N : ℝ)) - F 4 + 3 / 1000) atTop
      (𝓝 (zetaCurvature p 4 + 3 / 1000)) := by
    convert hV using 2 <;> simp only [Function.comp_apply,F,zero_sub,neg_neg] <;> ring
  exact le_of_tendsto_of_tendsto hT hV' (Eventually.of_forall hFin)

theorem pureQSecond_lt {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    pureQSecond p < 231 / 125 := by
  have h := pureQSecond_eq_tail hp 3
  have h1 : zetaCurvatureSlope p 1 = -2 := by simp [zetaCurvatureSlope,peanoExponentQuadratic]
  norm_num [Finset.sum_range_succ,h1] at h
  have hT := negSlope_tail_le hp hP
  rw [tsum_neg] at hT
  linarith only [h,hT,zetaSlope_two_gt hp hP,zetaSlope_three_gt hp hP,zetaCurvature_four_lt hp hP]

end ACS12.GammaMeasure

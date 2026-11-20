import ACS12.PureRightOrder
import ACS12.PowerConvex
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! A primitive for the complete following tail of the power kernel. -/
namespace ACS12.GammaMeasure

open CenteredCircle.AllN Set MeasureTheory Filter
open scoped Topology

noncomputable def pureRightPrimitive (p u x : ℝ) : ℝ :=
  middleZ u * x ^ (-p) + middleA u * (x + 1) ^ (-p) +
    ((x + 1) ^ (1 - p) - x ^ (1 - p)) / (p - 1)

theorem pureRightPrimitive_hasDerivAt {p u x : ℝ} (hp : 1 < p) (hx : 0 < x) :
    HasDerivAt (pureRightPrimitive p u) (-pureRight p u x) x := by
  have hx' : 0 < x + 1 := by positivity
  have h₁ (a : ℝ) := Real.hasDerivAt_rpow_const (p := a) (Or.inl hx.ne')
  have h₂ (a : ℝ) := ((hasDerivAt_id x).add_const 1).rpow_const (p := a) (Or.inl hx'.ne')
  have h := (((h₁ (-p)).const_mul (middleZ u)).add ((h₂ (-p)).const_mul (middleA u))).add
    (((h₂ (1 - p)).sub (h₁ (1 - p))).div_const (p - 1))
  convert h using 1
  simp only [id_eq,mul_one,one_mul,pureRight,show -p - 1 = -(p + 1) by ring,
    show 1 - p - 1 = -p by ring]
  field_simp [(sub_pos.mpr hp).ne']
  ring

theorem pureRight_tail_integral {p u x : ℝ} (hp : 1 < p) (hx : 0 < x) :
    IntegrableOn (pureRight p u) (Ioi x) ∧
      (∫ y : ℝ in Ioi x, pureRight p u y) = pureRightPrimitive p u x := by
  let F (q y : ℝ) := y ^ q
  let S (q y : ℝ) := (y + 1) ^ q
  have hF (q : ℝ) (hq : q < -1) : IntegrableOn (F q) (Ioi x) :=
    integrableOn_Ioi_rpow_of_lt hq hx
  have hS (q : ℝ) (hq : q < -1) : IntegrableOn (S q) (Ioi x) := by
    exact integrableOn_add_rpow_Ioi_of_lt hq (by linarith only [hx] : -(1 : ℝ) < x)
  have h₁ : -(p + 1) < -1 := by linarith only [hp]
  have h₂ : -p < -1 := neg_lt_neg hp
  have hI : IntegrableOn (pureRight p u) (Ioi x) :=
    ((((hF _ h₁).const_mul (middleZ u * p)).add ((hS _ h₁).const_mul
      (middleA u * p))).sub (hF _ h₂)).add (hS _ h₂)
  have hAt : Tendsto (fun y : ℝ => y + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  have hP : Tendsto (F (-p)) atTop (𝓝 0) := tendsto_rpow_neg_atTop (zero_lt_one.trans hp)
  have hQ : Tendsto (F (1 - p)) atTop (𝓝 0) := by
    simpa only [neg_sub] using tendsto_rpow_neg_atTop (sub_pos.mpr hp)
  have hEnd : Tendsto (pureRightPrimitive p u) atTop (𝓝 0) := by
    simpa only [mul_zero,sub_self,zero_div,add_zero] using
      ((hP.const_mul (middleZ u)).add ((hP.comp hAt).const_mul (middleA u))).add
        (((hQ.comp hAt).sub hQ).div_const (p - 1))
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun y hy => pureRightPrimitive_hasDerivAt (u := u) hp (hx.trans_le hy)) hI.neg hEnd
  exact ⟨hI, by simpa only [integral_neg,zero_sub,neg_inj] using hFTC⟩

private theorem midpoint_integral_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ConvexOn ℝ (Icc a b) f) (hC : ContinuousOn f (Icc a b)) :
    (b - a) * f ((a + b) / 2) ≤ ∫ x : ℝ in a..b, f x := by
  have hR : (∫ x : ℝ in a..b, f (a + b - x)) = ∫ x : ℝ in a..b, f x := by
    rw [intervalIntegral.integral_comp_sub_left,show a + b - b = a by ring,
      show a + b - a = b by ring]
  have hIR : IntervalIntegrable (fun x => f (a + b - x)) volume a b := by
    have hRCont : ContinuousOn (fun x : ℝ => f (a + b - x)) (Icc a b) :=
      hC.comp (by fun_prop) (fun x hx =>
        ⟨by linarith only [hx.2],by linarith only [hx.1]⟩)
    exact hRCont.intervalIntegrable_of_Icc hab
  have hI : IntervalIntegrable f volume a b := hC.intervalIntegrable_of_Icc hab
  have hCmp := intervalIntegral.integral_mono_on hab (intervalIntegrable_const (c := 2 * f ((a + b) / 2)))
    (hI.add hIR) (fun x hx => by
      have hy : a + b - x ∈ Icc a b := ⟨by linarith only [hx.2],by linarith only [hx.1]⟩
      have h := hF.2 hx hy (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num)
      simp only [smul_eq_mul,show (1 / 2 : ℝ) * x + 1 / 2 * (a + b - x) = (a + b) / 2 by ring] at h
      linarith only [h])
  rw [intervalIntegral.integral_const,smul_eq_mul,intervalIntegral.integral_add hI hIR,hR] at hCmp
  linarith only [hCmp]

theorem followingTail_le_integral {p L u m : ℝ} (hp : 1 < p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hu : 0 < u) (hm : 0 < m) :
    samplingTail (lawRightClip p L 0 u) (u + m) m ≤
      ∫ x : ℝ in Ioi (u + 3 * m / 2), lawRightClip p L 0 u x := by
  let f := lawRightClip p L 0 u
  let t := u + 3 * m / 2
  let a (n : ℕ) := t + (n : ℝ) * m
  have hθ : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have hC := lawRightClip_convex (u := u) hp.le hp₂ hL hθ
  have hA (n : ℕ) : 0 < a n := by unfold a t; positivity
  have hStep (n : ℕ) : a n ≤ a (n + 1) := by unfold a; push_cast; linarith only [hm]
  have hCOn (n : ℕ) : ContinuousOn f (Icc (a n) (a (n + 1))) := by
    have h := hC.continuousOn_interior
    rw [interior_Ioi] at h
    exact h.mono (fun x hx => (hA n).trans_le hx.1)
  have hI (n : ℕ) : IntervalIntegrable f volume (a n) (a (n + 1)) :=
    (hCOn n).intervalIntegrable_of_Icc (hStep n)
  have hEach (n : ℕ) :
      m * f (u + m + ((n : ℝ) + 1) * m) ≤ ∫ x : ℝ in a n..a (n + 1), f x := by
    have hC' : ConvexOn ℝ (Icc (a n) (a (n + 1))) f :=
      hC.subset (fun x hx => (hA n).trans_le hx.1) (convex_Icc _ _)
    convert midpoint_integral_le (hStep n) hC' (hCOn n) using 2
    · unfold a
      push_cast
      ring
    · congr 1
      unfold a t
      push_cast
      ring
  have hTailI : IntegrableOn f (Ioi t) := by
    have ht : 0 < t := by unfold t; positivity
    apply (pureRight_tail_integral (u := u) hp ht).1.pos_part.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change max (pureRight p u x) 0 = lawRightClip p L 0 u x
    rw [lawRightClip,lawRightTest_zero hp.le hp₂ hL (ht.trans hx),max_comm]
  have hTa (N : ℕ) : t ≤ a N :=
    le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hm.le)
  have hFinite (N : ℕ) : (∑ n ∈ Finset.range N, ∫ x : ℝ in a n..a (n + 1), f x) =
      ∫ x : ℝ in t..a N, f x := by
    induction N with
    | zero => simp [a]
    | succ N ih =>
      rw [Finset.sum_range_succ,ih]
      have hL : IntervalIntegrable f volume t (a N) := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (hTa N)]
        exact hTailI.mono_set (fun x hx => hx.1)
      exact intervalIntegral.integral_add_adjacent_intervals hL (hI N)
  unfold samplingTail
  rw [← tsum_mul_left]
  apply Real.tsum_le_of_sum_range_le (fun n => mul_nonneg hm.le (le_max_left _ _))
  intro N
  have hSum := Finset.sum_le_sum (s := Finset.range N) (fun n _ => hEach n)
  rw [hFinite,intervalIntegral.integral_of_le (hTa N)] at hSum
  simpa only [f,t,Nat.cast_succ] using hSum.trans (setIntegral_mono_set hTailI (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact le_max_left _ _) (Filter.Eventually.of_forall (fun x hx => hx.1)))

end ACS12.GammaMeasure


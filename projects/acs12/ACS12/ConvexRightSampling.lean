import CenteredCircle.KernelQuadratureData
import Mathlib.Analysis.Convex.Continuous

/-! Complete convex quadrature with right derivatives at clipping contacts. -/

namespace CenteredCircle.AllN

open Set Filter
open scoped BigOperators Topology

private theorem convex_right_derivative {K : ℝ → ℝ}
    (hK : ConvexOn ℝ (Ioi 0) K) {t : ℝ} (ht : 0 < t) :
    HasDerivWithinAt K (derivWithin K (Ioi t) t) (Ici t) t := by
  have h := hK.hasDerivWithinAt_rightDeriv_of_mem_interior
    (show t ∈ interior (Ioi (0 : ℝ)) by simpa only [interior_Ioi] using ht)
  have he : insert t (Ioi t) = Ici t := by
    ext x
    simp only [mem_insert_iff, mem_Ioi, mem_Ici, le_iff_eq_or_lt, eq_comm]
  have hd := h.hasFDerivWithinAt.insert.hasDerivWithinAt
  rw [he] at hd
  simpa using hd

private theorem right_increment_le {f f' : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hD : ∀ s ∈ Ico a b, HasDerivWithinAt f (f' s) (Ici s) s)
    (hB : ∀ s ∈ Ico a b, f' s ≤ C) :
    f b ≤ f a + C * (b - a) := by
  let B (s : ℝ) := f a + C * (s - a)
  have hB' (s : ℝ) : HasDerivAt B C s := by
    simpa only [mul_one] using
      (((hasDerivAt_id s).sub_const a).const_mul C).const_add (f a)
  exact image_le_of_deriv_right_le_deriv_boundary hf hD (by simp [B])
    (fun s _ => (hB' s).continuousAt.continuousWithinAt)
    (fun s _ => (hB' s).hasDerivWithinAt) hB ⟨hab, le_rfl⟩

private theorem hasDerivWithinAt_weightedSamples {K : ℝ → ℝ}
    (hK : ConvexOn ℝ (Ioi 0) K) (t s : ℝ) {N : ℕ} (c : ℕ → ℝ)
    (hc : ∀ j, 0 ≤ c j) (ht : ∀ j ∈ Finset.range N, 0 < t + c j * s) :
    HasDerivWithinAt (fun r : ℝ => r * ∑ j ∈ Finset.range N, K (t + c j * r))
      (∑ j ∈ Finset.range N, (K (t + c j * s) +
        c j * s * derivWithin K (Ioi (t + c j * s)) (t + c j * s))) (Ici s) s := by
  have h : HasDerivWithinAt (fun r : ℝ => ∑ j ∈ Finset.range N, r * K (t + c j * r))
      (∑ j ∈ Finset.range N, (K (t + c j * s) +
        c j * s * derivWithin K (Ioi (t + c j * s)) (t + c j * s))) (Ici s) s := by
    apply HasDerivWithinAt.fun_sum
    intro j hj
    have hIn : HasDerivAt (fun r : ℝ => t + c j * r) (c j) s := by
      simpa only [mul_one] using (((hasDerivAt_id s).const_mul (c j)).const_add t)
    have hMap : MapsTo (fun r : ℝ => t + c j * r) (Ici s) (Ici (t + c j * s)) :=
      fun r hr => add_le_add le_rfl (mul_le_mul_of_nonneg_left hr (hc j))
    have hC := (convex_right_derivative hK (ht j hj)).comp s hIn.hasDerivWithinAt hMap
    convert (hasDerivAt_id s).hasDerivWithinAt.mul hC using 1 <;> dsimp <;> ring
  simpa only [Finset.mul_sum] using h

private theorem head_right_monotone {K : ℝ → ℝ} (hK : ConvexOn ℝ (Ioi 0) K)
    (hP : ∀ t > 0, 0 ≤ K t) {t : ℝ} (ht : 0 < t) (N : ℕ) :
    MonotoneOn (finiteSamplingHead K t N) (Ioi 0) := by
  intro a ha b hb hab
  have ha₀ : 0 < a := ha
  let f := finiteSamplingHead K t N
  let f' (s : ℝ) := ∑ j ∈ Finset.range (N + 1), (K (t + j * s) +
    (j : ℝ) * s * derivWithin K (Ioi (t + j * s)) (t + j * s))
  have hCont : ContinuousOn f (Icc a b) := by
    have hC : ContinuousOn K (Ioi (0 : ℝ)) := by
      simpa only [interior_Ioi] using hK.continuousOn_interior
    unfold f finiteSamplingHead
    apply continuousOn_id.mul
    apply continuousOn_finsetSum
    intro j _
    exact hC.comp (by fun_prop) (fun s hs =>
      add_pos_of_pos_of_nonneg ht (mul_nonneg (Nat.cast_nonneg j) (ha₀.trans_le hs.1).le))
  have hD (s : ℝ) (hs : s ∈ Ico a b) : HasDerivWithinAt f (f' s) (Ici s) s :=
    hasDerivWithinAt_weightedSamples hK t s (fun j => (j : ℝ)) Nat.cast_nonneg
      (fun j _ => add_pos_of_pos_of_nonneg ht (mul_nonneg (Nat.cast_nonneg j) (ha₀.trans_le hs.1).le))
  have hB (s : ℝ) (hs : s ∈ Ico a b) : 0 ≤ f' s := by
    have hs₀ : 0 < s := ha₀.trans_le hs.1
    let x (j : ℕ) := t + (j : ℝ) * s
    have hx (j : ℕ) : 0 < x j := add_pos_of_pos_of_nonneg ht (mul_nonneg (Nat.cast_nonneg j) hs₀.le)
    have hStep (j : ℕ) : K (x (j + 1)) - K (x j) ≤
        s * derivWithin K (Ioi (x (j + 1))) (x (j + 1)) := by
      have hEq : x (j + 1) = x j + s := by simp [x, Nat.cast_add]; ring
      have hlt : x j < x (j + 1) := by rw [hEq]; linarith
      have hIn : x (j + 1) ∈ interior (Ioi (0 : ℝ)) := by
        simpa only [interior_Ioi] using hx (j + 1)
      have h := (hK.slope_le_leftDeriv_of_mem_interior (hx j) hIn hlt).trans
        (hK.leftDeriv_le_rightDeriv_of_mem_interior hIn)
      rw [slope_def_field, show x (j + 1) - x j = s by rw [hEq]; ring] at h
      exact (div_le_iff₀ hs₀).mp h |>.trans_eq (mul_comm _ _)
    exact (mul_nonneg (by positivity : 0 ≤ (N : ℝ) + 1) (hP _ (hx N))).trans
      (finite_head_slope_bound (K ∘ x) (fun j => derivWithin K (Ioi (x j)) (x j)) s hStep N)
  have h := right_increment_le (f := -f) (f' := -f') hab hCont.neg
    (fun s hs => (hD s hs).neg) (fun s hs => neg_nonpos.mpr (hB s hs))
  change -f b ≤ -f a + 0 * (b - a) at h
  exact (neg_le_neg_iff.mp (by simpa only [zero_mul, add_zero] using h))

private theorem tail_right_increment {K : ℝ → ℝ} (hK : ConvexOn ℝ (Ioi 0) K)
    {t a b ε : ℝ} (ht : 0 ≤ t) (ha : 0 < a) (hab : a ≤ b) (N : ℕ)
    (hB : ∀ s ≥ a, (N : ℝ) * K (t + ((N : ℝ) + 1) * s) ≤ ε) :
    finiteSamplingTail K t N b ≤ finiteSamplingTail K t N a + ε * (b - a) := by
  let f := finiteSamplingTail K t N
  let x (s : ℝ) (j : ℕ) := t + (j : ℝ) * s
  let f' (s : ℝ) := ∑ j ∈ Finset.range N, (K (x s (j + 1)) +
    ((j : ℝ) + 1) * s * derivWithin K (Ioi (x s (j + 1))) (x s (j + 1)))
  have hx (s : ℝ) (hs : 0 < s) (j : ℕ) : 0 < x s (j + 1) :=
    add_pos_of_nonneg_of_pos ht (mul_pos (by positivity) hs)
  have hCont : ContinuousOn f (Icc a b) := by
    have hCts : ContinuousOn K (Ioi (0 : ℝ)) := by simpa only [interior_Ioi] using hK.continuousOn_interior
    unfold f finiteSamplingTail
    apply continuousOn_id.mul
    apply continuousOn_finsetSum
    intro j _
    apply hCts.comp (by fun_prop)
    intro s hs
    simpa only [x, Nat.cast_add, Nat.cast_one] using hx s (ha.trans_le hs.1) j
  have hD (s : ℝ) (hs : s ∈ Ico a b) : HasDerivWithinAt f (f' s) (Ici s) s := by
    simpa only [f, f', x, Nat.cast_add, Nat.cast_one] using
      hasDerivWithinAt_weightedSamples hK t s (fun j => (j : ℝ) + 1) (fun _ => by positivity)
        (N := N) (fun j _ => by
          simpa only [x, Nat.cast_add, Nat.cast_one] using hx s (ha.trans_le hs.1) j)
  apply right_increment_le hab hCont hD
  intro s hs
  have hs₀ : 0 < s := ha.trans_le hs.1
  have hStep (j : ℕ) : s * derivWithin K (Ioi (x s (j + 1))) (x s (j + 1)) ≤
      K (x s (j + 2)) - K (x s (j + 1)) := by
    have hEq : x s (j + 2) = x s (j + 1) + s := by simp [x, Nat.cast_add]; ring
    have hlt : x s (j + 1) < x s (j + 2) := by rw [hEq]; linarith
    have hIn : x s (j + 1) ∈ interior (Ioi (0 : ℝ)) := by
      simpa only [interior_Ioi] using hx s hs₀ j
    have h := hK.rightDeriv_le_slope_of_mem_interior hIn (hx s hs₀ (j + 1)) hlt
    rw [slope_def_field, show x s (j + 2) - x s (j + 1) = s by rw [hEq]; ring] at h
    exact (mul_comm _ _).le.trans ((le_div_iff₀ hs₀).mp h)
  have hF : f' s ≤ (N : ℝ) * K (x s (N + 1)) := by
    simpa only [f', Nat.cast_add, Nat.cast_one] using
      finite_tail_slope_bound (K ∘ x s) (fun j => derivWithin K (Ioi (x s j)) (x s j)) s hStep N
  exact hF.trans (by simpa only [x, Nat.cast_add, Nat.cast_one] using hB s hs.1)

private theorem quadratic_sampling_remainder {C t a s : ℝ} (hC : 0 ≤ C)
    (ht : 0 ≤ t) (ha : 0 < a) (has : a ≤ s) (N : ℕ) :
    (N : ℝ) * (C / (t + ((N : ℝ) + 1) * s) ^ 2) ≤
      (C / a ^ 2) / ((N : ℝ) + 1) := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hN' : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hX : ((N : ℝ) + 1) * a ≤ t + ((N : ℝ) + 1) * s :=
    (mul_le_mul_of_nonneg_left has hN'.le).trans (le_add_of_nonneg_left ht)
  have hPos := mul_pos hN' ha
  calc
    _ ≤ (N : ℝ) * (C / (((N : ℝ) + 1) * a) ^ 2) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hC (sq_pos_of_pos hPos)
        (pow_le_pow_left₀ hPos.le hX 2)) hN
    _ ≤ ((N : ℝ) + 1) * (C / (((N : ℝ) + 1) * a) ^ 2) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (by positivity)
    _ = _ := by field_simp

theorem convex_right_quadratureData_of_quadratic_decay {K : ℝ → ℝ} {d : ℝ}
    (hK : ConvexOn ℝ (Ioi 0) K) (hP : ∀ t > 0, 0 ≤ K t)
    (hdecay : ∀ a > 0, ∃ C ≥ 0, ∀ x ≥ a, K x ≤ C / x ^ 2) (hd : 0 < d) :
    QuadratureData K d := by
  have hSum (t s : ℝ) (ht : 0 < t) (hs : 0 < s) : Summable (fun j : ℕ => K (t + j * s)) := by
    obtain ⟨C, hC, hB⟩ := hdecay t ht
    have hMaj := summable_of_power_decay (fun x : ℝ => C / x ^ 2) C t s 2 (by decide)
      hC ht hs (fun x hx => div_nonneg hC (sq_nonneg x)) (fun _ _ => le_rfl)
    apply hMaj.of_nonneg_of_le
    · intro j
      exact hP _ (add_pos_of_pos_of_nonneg ht (mul_nonneg (Nat.cast_nonneg j) hs.le))
    · intro j
      exact hB _ (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg j) hs.le))
  have hTail (t a b : ℝ) (ht : 0 ≤ t) (ha : 0 < a) (hab : a ≤ b) :
      samplingTail K t b ≤ samplingTail K t a := by
    obtain ⟨C, hC, hB⟩ := hdecay a ha
    have hlim (s : ℝ) (hs : 0 < s) :
        Tendsto (fun N : ℕ => finiteSamplingTail K t N s) atTop (𝓝 (samplingTail K t s)) := by
      have h := (hSum (t + s) s (add_pos_of_nonneg_of_pos ht hs) hs).hasSum.tendsto_sum_nat.const_mul s
      rw [samplingTail_eq_shift]
      simpa only [finiteSamplingTail, samplingHead,
        show ∀ j : ℕ, t + s + j * s = t + ((j : ℝ) + 1) * s from fun _ => by ring] using h
    have hε : Tendsto (fun N : ℕ => ((C / a ^ 2) / ((N : ℝ) + 1)) * (b - a)) atTop (𝓝 0) := by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (C / a ^ 2)
      simpa only [mul_one_div, mul_zero, zero_mul] using h.mul_const (b - a)
    have h := le_of_tendsto_of_tendsto (hlim b (ha.trans_le hab)) ((hlim a ha).add hε)
      (Eventually.of_forall fun N => tail_right_increment hK ht ha hab N (by
        intro s hs
        have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        have hS := ha.le.trans hs
        have hx : a ≤ t + ((N : ℝ) + 1) * s := by
          nlinarith [mul_nonneg hN hS]
        exact (mul_le_mul_of_nonneg_left (hB _ hx) hN).trans
          (quadratic_sampling_remainder hC ht ha hs N)))
    simpa only [add_zero] using h
  refine ⟨fun x hx => hP x (hd.trans_le hx), fun x s hx hs => hSum x s (hd.trans_le hx) hs, ?_, ?_, ?_⟩
  · intro x hx a ha b hb hab
    have hlim (s : ℝ) (hs : 0 < s) :
        Tendsto (fun N : ℕ => finiteSamplingHead K x N s) atTop (𝓝 (samplingHead K x s)) := by
      have h := (hSum x s (hd.trans_le hx) hs).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
      simpa only [finiteSamplingHead, samplingHead] using h.const_mul s
    exact le_of_tendsto_of_tendsto (hlim a ha) (hlim b hb)
      (Eventually.of_forall fun N => head_right_monotone hK hP (hd.trans_le hx) N ha hb hab)
  · intro x hx a ha b _ hab
    exact hTail x a b (hd.le.trans hx) ha hab
  · intro a ha b _ hab
    exact hTail 0 a b le_rfl (hd.trans_le ha) hab

theorem convex_right_quadratureData {K : ℝ → ℝ} {C d : ℝ}
    (hK : ConvexOn ℝ (Ioi 0) K) (hP : ∀ t > 0, 0 ≤ K t)
    (hC : 0 ≤ C) (hdecay : ∀ x > 0, K x ≤ C / x ^ 3) (hd : 0 < d) :
    QuadratureData K d := by
  apply convex_right_quadratureData_of_quadratic_decay hK hP _ hd
  intro a ha
  refine ⟨C / a, div_nonneg hC ha.le, ?_⟩
  intro x hx
  have hx₀ := ha.trans_le hx
  calc
    K x ≤ C / x ^ 3 := hdecay x hx₀
    _ = (C / x) / x ^ 2 := by ring
    _ ≤ (C / a) / x ^ 2 :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_left hC ha hx) (sq_nonneg x)

end CenteredCircle.AllN

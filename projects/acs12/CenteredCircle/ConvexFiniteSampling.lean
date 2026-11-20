import CenteredCircle.MixedKernelShape

/-!
Finite sampling derivatives telescope against convex secants. The infinite
head monotonicity follows by taking limits of finite monotone sums.
-/

namespace CenteredCircle.AllN

open Set Filter
open scoped BigOperators Topology

theorem convex_secant_lower {φ : ℝ → ℝ} {d x s : ℝ}
    (hc : ConvexOn ℝ (Ici d) φ) (hx : d ≤ x) (hs : 0 < s)
    (hd : DifferentiableAt ℝ φ (x + s)) :
    φ (x + s) - φ x ≤ s * deriv φ (x + s) := by
  have h := hc.slope_le_deriv hx (show d ≤ x + s by linarith) (by linarith) hd
  simp only [slope_def_field, add_sub_cancel_left] at h
  simpa only [mul_comm] using (div_le_iff₀ hs).mp h

theorem convex_secant_upper {φ : ℝ → ℝ} {d x s : ℝ}
    (hc : ConvexOn ℝ (Ici d) φ) (hx : d ≤ x) (hs : 0 < s)
    (hd : DifferentiableAt ℝ φ x) :
    s * deriv φ x ≤ φ (x + s) - φ x := by
  have h := hc.deriv_le_slope hx (show d ≤ x + s by linarith) (by linarith) hd
  simp only [slope_def_field, add_sub_cancel_left] at h
  simpa only [mul_comm] using (le_div_iff₀ hs).mp h

theorem finite_head_slope_bound (v z : ℕ → ℝ) (s : ℝ)
    (hstep : ∀ j, v (j + 1) - v j ≤ s * z (j + 1)) (N : ℕ) :
    ((N : ℝ) + 1) * v N ≤ ∑ j ∈ Finset.range (N + 1), (v j + (j : ℝ) * s * z j) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have h := mul_le_mul_of_nonneg_left (hstep N) (by positivity : (0 : ℝ) ≤ (N : ℝ) + 1)
    push_cast
    nlinarith

theorem finite_tail_slope_bound (v z : ℕ → ℝ) (s : ℝ)
    (hstep : ∀ j, s * z (j + 1) ≤ v (j + 2) - v (j + 1)) (N : ℕ) :
    (∑ j ∈ Finset.range N, (v (j + 1) + ((j : ℝ) + 1) * s * z (j + 1))) ≤
      (N : ℝ) * v (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have h := mul_le_mul_of_nonneg_left (hstep N) (by positivity : (0 : ℝ) ≤ (N : ℝ) + 1)
    push_cast
    nlinarith

noncomputable def finiteSamplingHead (φ : ℝ → ℝ) (t : ℝ) (N : ℕ) (s : ℝ) : ℝ :=
  s * ∑ j ∈ Finset.range (N + 1), φ (t + j * s)

noncomputable def finiteSamplingTail (φ : ℝ → ℝ) (t : ℝ) (N : ℕ) (s : ℝ) : ℝ :=
  s * ∑ j ∈ Finset.range N, φ (t + ((j : ℝ) + 1) * s)

theorem hasDerivAt_finiteSamplingHead (φ : ℝ → ℝ) (t : ℝ) (N : ℕ) (s : ℝ)
    (hd : ∀ j ∈ Finset.range (N + 1), DifferentiableAt ℝ φ (t + j * s)) :
    HasDerivAt (finiteSamplingHead φ t N)
      (∑ j ∈ Finset.range (N + 1), (φ (t + j * s) + (j : ℝ) * s * deriv φ (t + j * s))) s := by
  have h : HasDerivAt (fun y : ℝ => ∑ j ∈ Finset.range (N + 1), y * φ (t + j * y))
      (∑ j ∈ Finset.range (N + 1), (φ (t + j * s) + (j : ℝ) * s * deriv φ (t + j * s))) s := by
    apply HasDerivAt.fun_sum
    intro j hj
    have hi := (hd j hj).hasDerivAt.comp s (((hasDerivAt_id s).const_mul (j : ℝ)).const_add t)
    convert (hasDerivAt_id s).mul hi using 1 <;> dsimp <;> ring
  unfold finiteSamplingHead
  simpa only [Finset.mul_sum] using h

theorem hasDerivAt_finiteSamplingTail (φ : ℝ → ℝ) (t : ℝ) (N : ℕ) (s : ℝ)
    (hd : ∀ j ∈ Finset.range N, DifferentiableAt ℝ φ (t + ((j : ℝ) + 1) * s)) :
    HasDerivAt (finiteSamplingTail φ t N)
      (∑ j ∈ Finset.range N, (φ (t + ((j : ℝ) + 1) * s) +
        ((j : ℝ) + 1) * s * deriv φ (t + ((j : ℝ) + 1) * s))) s := by
  have h : HasDerivAt (fun y : ℝ => ∑ j ∈ Finset.range N, y * φ (t + ((j : ℝ) + 1) * y))
      (∑ j ∈ Finset.range N, (φ (t + ((j : ℝ) + 1) * s) +
        ((j : ℝ) + 1) * s * deriv φ (t + ((j : ℝ) + 1) * s))) s := by
    apply HasDerivAt.fun_sum
    intro j hj
    have hi := (hd j hj).hasDerivAt.comp s
      (((hasDerivAt_id s).const_mul ((j : ℝ) + 1)).const_add t)
    convert (hasDerivAt_id s).mul hi using 1 <;> dsimp <;> ring
  unfold finiteSamplingTail
  simpa only [Finset.mul_sum] using h

theorem finiteSamplingHead_deriv_nonneg {φ : ℝ → ℝ} {d t s : ℝ}
    (hc : ConvexOn ℝ (Ici d) φ) (hp : ∀ x, d ≤ x → 0 ≤ φ x)
    (hd : ∀ x, d ≤ x → DifferentiableAt ℝ φ x) (ht : d ≤ t) (hs : 0 < s) (N : ℕ) :
    0 ≤ deriv (finiteSamplingHead φ t N) s := by
  have harg (j : ℕ) : d ≤ t + (j : ℝ) * s := by
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith
  rw [(hasDerivAt_finiteSamplingHead φ t N s (fun j _ => hd _ (harg j))).deriv]
  have hstep : ∀ j : ℕ, φ (t + (j + 1 : ℕ) * s) - φ (t + j * s) ≤
      s * deriv φ (t + (j + 1 : ℕ) * s) := by
    intro j
    have he : t + ((j + 1 : ℕ) : ℝ) * s = (t + (j : ℝ) * s) + s := by push_cast; ring
    rw [he]
    exact convex_secant_lower hc (harg j) hs (hd _ (by linarith [harg j]))
  have hb := finite_head_slope_bound (fun j => φ (t + j * s))
    (fun j => deriv φ (t + j * s)) s hstep N
  exact le_trans (mul_nonneg (by positivity) (hp _ (harg N))) hb

theorem finiteSamplingHead_monotone {φ : ℝ → ℝ} {d t : ℝ}
    (hc : ConvexOn ℝ (Ici d) φ) (hp : ∀ x, d ≤ x → 0 ≤ φ x)
    (hd : ∀ x, d ≤ x → DifferentiableAt ℝ φ x) (ht : d ≤ t) (N : ℕ) :
    MonotoneOn (finiteSamplingHead φ t N) (Ioi 0) := by
  have hf (s : ℝ) (hs : 0 < s) := hasDerivAt_finiteSamplingHead φ t N s
    (fun j _ => hd _ (by have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j; nlinarith))
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · intro s hs
    exact (hf s hs).continuousAt.continuousWithinAt
  · intro s hs
    exact (hf s (by simpa using hs)).differentiableAt.differentiableWithinAt
  · intro s hs
    exact finiteSamplingHead_deriv_nonneg hc hp hd ht (by simpa using hs) N

theorem samplingHead_monotone_of_convex {φ : ℝ → ℝ} {d t : ℝ}
    (hc : ConvexOn ℝ (Ici d) φ) (hp : ∀ x, d ≤ x → 0 ≤ φ x)
    (hd : ∀ x, d ≤ x → DifferentiableAt ℝ φ x) (ht : d ≤ t)
    (hsum : ∀ s, 0 < s → Summable (fun j : ℕ => φ (t + j * s))) :
    MonotoneOn (samplingHead φ t) (Ioi 0) := by
  intro a ha b hb hab
  have hlim (s : ℝ) (hs : 0 < s) :
      Tendsto (fun N : ℕ => finiteSamplingHead φ t N s) atTop (𝓝 (samplingHead φ t s)) := by
    have hh := (hsum s hs).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    simpa only [finiteSamplingHead, samplingHead] using hh.const_mul s
  exact le_of_tendsto_of_tendsto (hlim a ha) (hlim b hb)
    (Eventually.of_forall (fun N => finiteSamplingHead_monotone hc hp hd ht N ha hb hab))

end CenteredCircle.AllN

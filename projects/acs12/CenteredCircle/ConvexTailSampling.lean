import CenteredCircle.ConvexFiniteSampling

/-!
Tail sampling for smooth convex kernels with cubic decay. Finite tails have a
vanishing upper bound on their derivative; no sign condition on a Laplace
density, and no unproved interchange of differentiation and summation, is used.
-/

namespace CenteredCircle.AllN

open Set Filter
open scoped BigOperators Topology

theorem finiteSamplingTail_deriv_bound {φ : ℝ → ℝ} {d t s : ℝ}
    (hc : ConvexOn ℝ (Ici d) φ)
    (hd : ∀ x, d ≤ x → DifferentiableAt ℝ φ x)
    (ht : d ≤ t + s) (hs : 0 < s) (N : ℕ) :
    deriv (finiteSamplingTail φ t N) s ≤ (N : ℝ) * φ (t + ((N : ℝ) + 1) * s) := by
  have harg (j : ℕ) : d ≤ t + ((j : ℝ) + 1) * s := by
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith
  rw [(hasDerivAt_finiteSamplingTail φ t N s (fun j _ => hd _ (harg j))).deriv]
  have hstep : ∀ j : ℕ,
      s * deriv φ (t + (j + 1 : ℕ) * s) ≤
        φ (t + (j + 2 : ℕ) * s) - φ (t + (j + 1 : ℕ) * s) := by
    intro j
    have he : t + ((j + 2 : ℕ) : ℝ) * s = (t + ((j : ℝ) + 1) * s) + s := by
      push_cast
      ring
    rw [he]
    simpa only [Nat.cast_add, Nat.cast_one] using
      convex_secant_upper hc (harg j) hs (hd _ (harg j))
  simpa only [Nat.cast_add, Nat.cast_one] using
    finite_tail_slope_bound (fun j => φ (t + j * s))
      (fun j => deriv φ (t + j * s)) s hstep N

theorem cubic_sampling_remainder_bound {C t a s : ℝ} (hC : 0 ≤ C)
    (ht : 0 ≤ t) (ha : 0 < a) (has : a ≤ s) (N : ℕ) :
    (N : ℝ) * (C / (t + ((N : ℝ) + 1) * s) ^ 3) ≤
      (C / a ^ 3) / ((N : ℝ) + 1) := by
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hn1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hsmall : 0 < ((N : ℝ) + 1) * a := mul_pos hn1 ha
  have harg : ((N : ℝ) + 1) * a ≤ t + ((N : ℝ) + 1) * s := by nlinarith
  have hcub : (((N : ℝ) + 1) * a) ^ 3 ≤ (t + ((N : ℝ) + 1) * s) ^ 3 :=
    pow_le_pow_left₀ hsmall.le harg 3
  have hdiv := div_le_div_of_nonneg_left hC (pow_pos hsmall 3) hcub
  apply le_trans (mul_le_mul_of_nonneg_left hdiv hn)
  apply (le_div_iff₀ hn1).mpr
  apply (le_div_iff₀ (pow_pos ha 3)).mpr
  have he : ((N : ℝ) * (C / (((N : ℝ) + 1) * a) ^ 3) * ((N : ℝ) + 1)) * a ^ 3 =
      C * (N : ℝ) / ((N : ℝ) + 1) ^ 2 := by
    field_simp
    <;> ring
  rw [he]
  apply (div_le_iff₀ (pow_pos hn1 2)).mpr
  have hpoly : (N : ℝ) ≤ ((N : ℝ) + 1) ^ 2 := by nlinarith [sq_nonneg (N : ℝ)]
  exact mul_le_mul_of_nonneg_left hpoly hC

theorem finiteSamplingTail_increment_bound {φ : ℝ → ℝ} {d C t a b : ℝ}
    (hc : ConvexOn ℝ (Ici d) φ)
    (hd : ∀ x, d ≤ x → DifferentiableAt ℝ φ x)
    (hC : 0 ≤ C) (hdecay : ∀ x, d ≤ x → 0 < x → φ x ≤ C / x ^ 3)
    (ht : 0 ≤ t) (ha : 0 < a) (hstart : d ≤ t + a) (hab : a ≤ b) (N : ℕ) :
    finiteSamplingTail φ t N b - finiteSamplingTail φ t N a ≤
      ((C / a ^ 3) / ((N : ℝ) + 1)) * (b - a) := by
  have hdiff (s : ℝ) (hs : s ∈ Icc a b) :=
    hasDerivAt_finiteSamplingTail φ t N s (fun j _ => hd _ (by
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have hsp : 0 < s := lt_of_lt_of_le ha hs.1
      nlinarith [hs.1]))
  apply (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le
    (fun s hs => (hdiff s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hdiff s (interior_subset hs)).differentiableAt.differentiableWithinAt)
    _ a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩ hab
  intro s hs
  have hs' : s ∈ Icc a b := interior_subset hs
  have hsp : 0 < s := lt_of_lt_of_le ha hs'.1
  have hta : d ≤ t + s := by linarith [hs'.1]
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hdom : d ≤ t + ((N : ℝ) + 1) * s := by nlinarith
  have hpos : 0 < t + ((N : ℝ) + 1) * s := by positivity
  exact le_trans (finiteSamplingTail_deriv_bound hc hd hta hsp N)
    (le_trans (mul_le_mul_of_nonneg_left (hdecay _ hdom hpos) hn)
      (cubic_sampling_remainder_bound hC ht ha hs'.1 N))

theorem samplingTail_le_of_convex {φ : ℝ → ℝ} {d C t a b : ℝ}
    (hc : ConvexOn ℝ (Ici d) φ)
    (hd : ∀ x, d ≤ x → DifferentiableAt ℝ φ x)
    (hC : 0 ≤ C) (hdecay : ∀ x, d ≤ x → 0 < x → φ x ≤ C / x ^ 3)
    (ht : 0 ≤ t) (ha : 0 < a) (hstart : d ≤ t + a) (hab : a ≤ b)
    (hsa : Summable (fun j : ℕ => φ (t + (j + 1 : ℕ) * a)))
    (hsb : Summable (fun j : ℕ => φ (t + (j + 1 : ℕ) * b))) :
    samplingTail φ t b ≤ samplingTail φ t a := by
  have hlim (s : ℝ) (hs : Summable (fun j : ℕ => φ (t + (j + 1 : ℕ) * s))) :
      Tendsto (fun N : ℕ => finiteSamplingTail φ t N s) atTop (𝓝 (samplingTail φ t s)) := by
    simpa only [finiteSamplingTail, samplingTail, Nat.cast_add, Nat.cast_one] using
      hs.hasSum.tendsto_sum_nat.const_mul s
  have heps : Tendsto (fun N : ℕ => ((C / a ^ 3) / ((N : ℝ) + 1)) * (b - a)) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (C / a ^ 3)
    simpa only [mul_one_div, mul_zero, zero_mul] using h.mul_const (b - a)
  have hbound := le_of_tendsto_of_tendsto ((hlim b hsb).sub (hlim a hsa)) heps
    (Eventually.of_forall (fun N =>
      finiteSamplingTail_increment_bound hc hd hC hdecay ht ha hstart hab N))
  linarith

theorem samplingTail_antitone_of_convex {φ : ℝ → ℝ} {d C t : ℝ}
    (hc : ConvexOn ℝ (Ici d) φ)
    (hd : ∀ x, d ≤ x → DifferentiableAt ℝ φ x)
    (hC : 0 ≤ C) (hdecay : ∀ x, d ≤ x → 0 < x → φ x ≤ C / x ^ 3)
    (ht : 0 ≤ t) (hdom : d ≤ t)
    (hsum : ∀ s, 0 < s → Summable (fun j : ℕ => φ (t + (j + 1 : ℕ) * s))) :
    AntitoneOn (samplingTail φ t) (Ioi 0) := by
  intro a ha b hb hab
  have hap : 0 < a := ha
  exact samplingTail_le_of_convex hc hd hC hdecay ht ha (by linarith) hab
    (hsum a ha) (hsum b hb)

theorem samplingTail_boundary_antitone_of_convex {φ : ℝ → ℝ} {d C : ℝ}
    (hc : ConvexOn ℝ (Ici d) φ)
    (hd : ∀ x, d ≤ x → DifferentiableAt ℝ φ x)
    (hC : 0 ≤ C) (hdecay : ∀ x, d ≤ x → 0 < x → φ x ≤ C / x ^ 3)
    (hdpos : 0 < d)
    (hsum : ∀ s, d ≤ s → Summable (fun j : ℕ => φ ((j + 1 : ℕ) * s))) :
    AntitoneOn (samplingTail φ 0) (Ici d) := by
  intro a ha b hb hab
  apply samplingTail_le_of_convex hc hd hC hdecay (by norm_num)
    (lt_of_lt_of_le hdpos ha) (by simpa using ha) hab
  · simpa only [zero_add] using hsum a ha
  · simpa only [zero_add] using hsum b hb

end CenteredCircle.AllN

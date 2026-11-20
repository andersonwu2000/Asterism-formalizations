import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Sampling sums and the exact one-step quadrature mechanism. Monotonicity of
sampling with respect to step size is an explicit input here. The analytic
kernel modules must establish that input; it is not a new axiom.
-/

namespace CenteredCircle.AllN

open scoped BigOperators

noncomputable def samplingHead (φ : ℝ → ℝ) (t s : ℝ) : ℝ :=
  s * ∑' j : ℕ, φ (t + j * s)

noncomputable def samplingTail (φ : ℝ → ℝ) (t s : ℝ) : ℝ :=
  s * ∑' j : ℕ, φ (t + (j + 1 : ℕ) * s)

theorem samplingHead_split (φ : ℝ → ℝ) (t s : ℝ)
    (hsum : Summable (fun j : ℕ => φ (t + j * s))) :
    samplingHead φ t s = s * φ t + samplingTail φ t s := by
  unfold samplingHead samplingTail
  rw [hsum.tsum_eq_zero_add, mul_add]
  simp

theorem samplingTail_eq_shift (φ : ℝ → ℝ) (t s : ℝ) :
    samplingTail φ t s = samplingHead φ (t + s) s := by
  unfold samplingTail samplingHead
  congr 1
  apply tsum_congr
  intro j
  congr 1
  push_cast
  ring

theorem samplingHead_nonneg (φ : ℝ → ℝ) (t s : ℝ) (hs : 0 ≤ s)
    (hφ : ∀ j : ℕ, 0 ≤ φ (t + j * s)) : 0 ≤ samplingHead φ t s :=
  mul_nonneg hs (tsum_nonneg hφ)

theorem sampling_one_step (φ : ℝ → ℝ) (t s h : ℝ)
    (hs : 0 < s) (hh : 0 < h)
    (hsum_s : Summable (fun j : ℕ => φ (t + j * s)))
    (hsum_h : Summable (fun j : ℕ => φ (t + j * h)))
    (hhead : MonotoneOn (samplingHead φ t) (Set.Ioi 0))
    (htail : AntitoneOn (samplingTail φ t) (Set.Ioi 0)) :
    min s h * φ t + samplingHead φ (t + h) h ≤ samplingHead φ t s := by
  rcases le_total s h with hsh | hhs
  · rw [min_eq_left hsh, ← samplingTail_eq_shift]
    have hle := htail hs hh hsh
    rw [samplingHead_split φ t s hsum_s]
    linarith
  · rw [min_eq_right hhs, ← samplingTail_eq_shift,
      ← samplingHead_split φ t h hsum_h]
    exact hhead hh hs hhs

theorem sampling_one_step_eq_iff (φ : ℝ → ℝ) (t s h : ℝ)
    (hs : 0 < s) (hh : 0 < h)
    (hsum_s : Summable (fun j : ℕ => φ (t + j * s)))
    (hsum_h : Summable (fun j : ℕ => φ (t + j * h)))
    (hhead : StrictMonoOn (samplingHead φ t) (Set.Ioi 0))
    (htail : StrictAntiOn (samplingTail φ t) (Set.Ioi 0)) :
    min s h * φ t + samplingHead φ (t + h) h = samplingHead φ t s ↔ s = h := by
  constructor
  · intro heq
    rcases lt_trichotomy s h with hsh | hequal | hhs
    · rw [min_eq_left hsh.le, ← samplingTail_eq_shift,
        samplingHead_split φ t s hsum_s] at heq
      have hlt := htail hs hh hsh
      linarith
    · exact hequal
    · rw [min_eq_right hhs.le, ← samplingTail_eq_shift,
        ← samplingHead_split φ t h hsum_h] at heq
      have hlt := hhead hh hs hhs
      linarith
  · intro heq
    subst h
    rw [min_self, ← samplingTail_eq_shift, ← samplingHead_split φ t s hsum_s]

end CenteredCircle.AllN

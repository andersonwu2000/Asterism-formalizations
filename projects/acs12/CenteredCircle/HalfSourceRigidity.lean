import CenteredCircle.FiniteDefects
import CenteredCircle.Quadrature
import Mathlib.Tactic.Positivity

/-!
The equality mechanism for one ordered half-source. Its kernel hypotheses are
spelled out: summability and strict sampling monotonicity remain to be verified
for the manuscript's kernels A and B. No periodicity or vanishing remainder is
required by the equality argument itself.
-/

namespace CenteredCircle.AllN

open scoped BigOperators

/-- Quadrature on the domain actually sampled. The kernel need not have any
shape, or even be nonnegative, below `d`. Monotonicity at the origin is only
needed for step sizes at least `d`. -/
theorem half_source_bound (K : ℝ → ℝ) (d total : ℝ) (t s q : ℕ → ℝ)
    (hK : ∀ x, d ≤ x → 0 ≤ K x)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, d ≤ t i)
    (hstart : d ≤ s 0) (hstart_eq : t 0 = s 0)
    (hnext : ∀ i, t (i + 1) = t i + s (i + 1))
    (hmass : ∀ i, q i ≤ min (s i) (s (i + 1)))
    (hsummable : ∀ x step, d ≤ x → 0 < step →
      Summable (fun j : ℕ => K (x + j * step)))
    (hhead : ∀ x, d ≤ x → MonotoneOn (samplingHead K x) (Set.Ioi 0))
    (htail : ∀ x, d ≤ x → AntitoneOn (samplingTail K x) (Set.Ioi 0))
    (hboundary_mono : AntitoneOn (samplingTail K 0) (Set.Ici d))
    (hsum : HasSum (fun i => q i * K (t i)) total) :
    total ≤ samplingTail K 0 d := by
  let capital : ℕ → ℝ := fun i => samplingHead K (t i) (s i)
  have hcapital : ∀ i, 0 ≤ capital i := by
    intro i
    apply samplingHead_nonneg K (t i) (s i) (hs i).le
    intro j
    apply hK
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith [hs i, ht i]
  have hstep : ∀ i, q i * K (t i) + capital (i + 1) ≤ capital i := by
    intro i
    have htransition := sampling_one_step K (t i) (s i) (s (i + 1))
      (hs i) (hs (i + 1))
      (hsummable _ _ (ht i) (hs i)) (hsummable _ _ (ht i) (hs (i + 1)))
      (hhead _ (ht i)) (htail _ (ht i))
    rw [← hnext i] at htransition
    have hpaid := mul_le_mul_of_nonneg_right (hmass i) (hK _ (ht i))
    dsimp [capital]
    linarith
  have hfirst : capital 0 = samplingTail K 0 (s 0) := by
    rw [samplingTail_eq_shift]
    simp [capital, hstart_eq]
  have hprefix : total ≤ capital 0 :=
    le_of_tendsto' hsum.tendsto_sum_nat
      (prefix_mass_le (fun i => q i * K (t i)) capital hcapital hstep)
  apply hprefix.trans
  rw [hfirst]
  exact hboundary_mono (by simp) hstart hstart

theorem half_source_rigid (K : ℝ → ℝ) (t s q : ℕ → ℝ)
    (hK : ∀ x, 0 < x → 0 < K x)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i)
    (hstart : 1 ≤ s 0) (hstart_eq : t 0 = s 0)
    (hnext : ∀ i, t (i + 1) = t i + s (i + 1))
    (hmass : ∀ i, q i ≤ min (s i) (s (i + 1)))
    (hsummable : ∀ x step, 0 < x → 0 < step →
      Summable (fun j : ℕ => K (x + j * step)))
    (hhead : ∀ x, 0 < x → StrictMonoOn (samplingHead K x) (Set.Ioi 0))
    (htail : ∀ x, 0 ≤ x → StrictAntiOn (samplingTail K x) (Set.Ioi 0))
    (hsum : HasSum (fun i => q i * K (t i)) (samplingTail K 0 1)) :
    ∀ i, s i = 1 ∧ t i = (i : ℝ) + 1 ∧ q i = 1 := by
  let capital : ℕ → ℝ := fun i => samplingHead K (t i) (s i)
  have hcapital : ∀ i, 0 ≤ capital i := by
    intro i
    apply samplingHead_nonneg K (t i) (s i) (hs i).le
    intro j
    apply (hK _ ?_).le
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith [hs i, ht i]
  have htransition : ∀ i,
      min (s i) (s (i + 1)) * K (t i) + capital (i + 1) ≤ capital i := by
    intro i
    dsimp [capital]
    rw [hnext i]
    exact sampling_one_step K (t i) (s i) (s (i + 1)) (hs i) (hs (i + 1))
      (hsummable _ _ (ht i) (hs i)) (hsummable _ _ (ht i) (hs (i + 1)))
      (hhead _ (ht i)).monotoneOn (htail _ (ht i).le).antitoneOn
  have hstep : ∀ i, q i * K (t i) + capital (i + 1) ≤ capital i := by
    intro i
    have hm := mul_le_mul_of_nonneg_right (hmass i) (hK _ (ht i)).le
    linarith [htransition i]
  have hfirst : capital 0 = samplingTail K 0 (s 0) := by
    rw [samplingTail_eq_shift]
    simp [capital, hstart_eq]
  have hboundary : capital 0 ≤ samplingTail K 0 1 := by
    rw [hfirst]
    exact (htail 0 (by norm_num)).antitoneOn (by norm_num) (hs 0) hstart
  have hzero := zero_defects_of_hasSum (samplingTail K 0 1)
    (fun i => q i * K (t i)) capital hcapital hstep hboundary hsum
  have hs0 : s 0 = 1 := by
    by_contra hne
    have hlt : 1 < s 0 := lt_of_le_of_ne hstart (Ne.symm hne)
    have hstrict := htail 0 (by norm_num) (by norm_num) (hs 0) hlt
    rw [← hfirst] at hstrict
    linarith [hzero.1]
  have hsplit : ∀ i,
      (capital i - min (s i) (s (i + 1)) * K (t i) - capital (i + 1) = 0) ∧
      q i = min (s i) (s (i + 1)) := by
    intro i
    exact transition_and_mass_zero (hK _ (ht i)) (hmass i) (htransition i) (hzero.2 i)
  have hsame : ∀ i, s i = s (i + 1) := by
    intro i
    apply (sampling_one_step_eq_iff K (t i) (s i) (s (i + 1)) (hs i) (hs (i + 1))
      (hsummable _ _ (ht i) (hs i)) (hsummable _ _ (ht i) (hs (i + 1)))
      (hhead _ (ht i)) (htail _ (ht i).le)).mp
    have hz := (hsplit i).1
    dsimp [capital] at hz
    rw [hnext i] at hz
    linarith
  have hsall : ∀ i, s i = 1 := by
    intro i
    induction i with
    | zero => exact hs0
    | succ i ih => exact (hsame i).symm.trans ih
  have htall : ∀ i, t i = (i : ℝ) + 1 := by
    intro i
    induction i with
    | zero => simpa [hstart_eq] using hs0
    | succ i ih => rw [hnext, ih, hsall]; push_cast; ring
  intro i
  refine ⟨hsall i, htall i, ?_⟩
  simpa only [hsall, min_self] using (hsplit i).2

end CenteredCircle.AllN

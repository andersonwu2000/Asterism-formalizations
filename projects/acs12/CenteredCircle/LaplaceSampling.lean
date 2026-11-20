import CenteredCircle.ExponentialSampling
import CenteredCircle.HalfSourceRigidity
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Positive Laplace mixtures inherit strict sampling monotonicity and the full
half-source equality theorem. All convergence conditions are explicit, and
the series/integral interchange is proved, not assumed.
-/

namespace CenteredCircle.AllN

open MeasureTheory Filter Set
open scoped BigOperators

noncomputable def laplaceKernel (μ : Measure ℝ) (t : ℝ) : ℝ :=
  ∫ u, Real.exp (-u * t) ∂μ

theorem integral_strict_of_ae_lt {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [NeZero μ] {f g : α → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hfg : ∀ᵐ a ∂μ, f a < g a) :
    (∫ a, f a ∂μ) < ∫ a, g a ∂μ := by
  have hle : f ≤ᵐ[μ] g := hfg.mono (fun _ h => h.le)
  refine lt_of_le_of_ne (integral_mono_ae hf hg hle) ?_
  intro heq
  have hae := (integral_eq_iff_of_ae_le hf hg hle).mp heq
  obtain ⟨a, hlt, hequal⟩ := (hfg.and hae).exists
  exact hlt.ne hequal

variable (μ : Measure ℝ)

theorem samplingHead_laplace (t s : ℝ) (ht : 0 < t) (hs : 0 < s)
    (hint : ∀ x, 0 < x → Integrable (fun u => Real.exp (-u * x)) μ)
    (hsum : Summable (fun j : ℕ => laplaceKernel μ (t + j * s))) :
    samplingHead (laplaceKernel μ) t s =
      ∫ u, samplingHead (fun x => Real.exp (-u * x)) t s ∂μ := by
  have hInt : ∀ j : ℕ, Integrable (fun u => Real.exp (-u * (t + j * s))) μ := by
    intro j
    apply hint
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith
  have hNorm : Summable (fun j : ℕ => ∫ u, ‖Real.exp (-u * (t + j * s))‖ ∂μ) := by
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), laplaceKernel] using hsum
  have hswap := integral_tsum_of_summable_integral_norm hInt hNorm
  unfold samplingHead laplaceKernel
  rw [hswap, integral_const_mul]

theorem samplingTail_laplace (t s : ℝ) (ht : 0 ≤ t) (hs : 0 < s)
    (hint : ∀ x, 0 < x → Integrable (fun u => Real.exp (-u * x)) μ)
    (hsum : Summable (fun j : ℕ => laplaceKernel μ (t + s + j * s))) :
    samplingTail (laplaceKernel μ) t s =
      ∫ u, samplingTail (fun x => Real.exp (-u * x)) t s ∂μ := by
  simp_rw [samplingTail_eq_shift]
  exact samplingHead_laplace μ (t + s) s (by linarith) hs hint hsum

variable [NeZero μ]

theorem laplaceKernel_pos (t : ℝ)
    (hint : Integrable (fun u => Real.exp (-u * t)) μ) :
    0 < laplaceKernel μ t := integral_exp_pos hint

theorem samplingHead_laplace_pos (t s : ℝ) (ht : 0 < t) (hs : 0 < s)
    (hint : ∀ x, 0 < x → Integrable (fun u => Real.exp (-u * x)) μ)
    (hsum : Summable (fun j : ℕ => laplaceKernel μ (t + j * s))) :
    0 < samplingHead (laplaceKernel μ) t s := by
  have hnonneg : ∀ j : ℕ, 0 ≤ laplaceKernel μ (t + j * s) := by
    intro j
    apply (laplaceKernel_pos μ _ (hint _ ?_)).le
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith
  have hlead := hsum.le_tsum 0 (fun j _ => hnonneg j)
  simp only [Nat.cast_zero, zero_mul, add_zero] at hlead
  exact mul_pos hs ((laplaceKernel_pos μ t (hint t ht)).trans_le hlead)

theorem integrable_samplingHead_exponential (t s : ℝ) (ht : 0 < t) (hs : 0 < s)
    (hint : ∀ x, 0 < x → Integrable (fun u => Real.exp (-u * x)) μ)
    (hsum : Summable (fun j : ℕ => laplaceKernel μ (t + j * s))) :
    Integrable (fun u => samplingHead (fun x => Real.exp (-u * x)) t s) μ := by
  apply Integrable.of_integral_ne_zero
  rw [← samplingHead_laplace μ t s ht hs hint hsum]
  exact ne_of_gt (samplingHead_laplace_pos μ t s ht hs hint hsum)

theorem integrable_samplingTail_exponential (t s : ℝ) (ht : 0 ≤ t) (hs : 0 < s)
    (hint : ∀ x, 0 < x → Integrable (fun u => Real.exp (-u * x)) μ)
    (hsum : Summable (fun j : ℕ => laplaceKernel μ (t + s + j * s))) :
    Integrable (fun u => samplingTail (fun x => Real.exp (-u * x)) t s) μ := by
  simp_rw [samplingTail_eq_shift]
  exact integrable_samplingHead_exponential μ (t + s) s (by linarith) hs hint hsum

theorem strictMonoOn_samplingHead_laplace (t : ℝ) (ht : 0 < t)
    (hpositive : ∀ᵐ u ∂μ, 0 < u)
    (hint : ∀ x, 0 < x → Integrable (fun u => Real.exp (-u * x)) μ)
    (hsum : ∀ s, 0 < s → Summable (fun j : ℕ => laplaceKernel μ (t + j * s))) :
    StrictMonoOn (samplingHead (laplaceKernel μ) t) (Ioi 0) := by
  intro s hs h hh hsh
  rw [samplingHead_laplace μ t s ht hs hint (hsum s hs),
      samplingHead_laplace μ t h ht hh hint (hsum h hh)]
  apply integral_strict_of_ae_lt μ
    (integrable_samplingHead_exponential μ t s ht hs hint (hsum s hs))
    (integrable_samplingHead_exponential μ t h ht hh hint (hsum h hh))
  exact hpositive.mono (fun u hu => strictMonoOn_samplingHead_exponential u t hu hs hh hsh)

theorem strictAntiOn_samplingTail_laplace (t : ℝ) (ht : 0 ≤ t)
    (hpositive : ∀ᵐ u ∂μ, 0 < u)
    (hint : ∀ x, 0 < x → Integrable (fun u => Real.exp (-u * x)) μ)
    (hsum : ∀ x s, 0 < x → 0 < s →
      Summable (fun j : ℕ => laplaceKernel μ (x + j * s))) :
    StrictAntiOn (samplingTail (laplaceKernel μ) t) (Ioi 0) := by
  intro s hs h hh hsh
  have hts : 0 < t + s := add_pos_of_nonneg_of_pos ht hs
  have hth : 0 < t + h := add_pos_of_nonneg_of_pos ht hh
  rw [samplingTail_laplace μ t s ht hs hint (hsum _ _ hts hs),
      samplingTail_laplace μ t h ht hh hint (hsum _ _ hth hh)]
  apply integral_strict_of_ae_lt μ
    (integrable_samplingTail_exponential μ t h ht hh hint (hsum _ _ hth hh))
    (integrable_samplingTail_exponential μ t s ht hs hint (hsum _ _ hts hs))
  exact hpositive.mono (fun u hu => strictAntiOn_samplingTail_exponential u t hu hs hh hsh)

theorem half_source_rigid_laplace (t s q : ℕ → ℝ)
    (hpositive : ∀ᵐ u ∂μ, 0 < u)
    (hint : ∀ x, 0 < x → Integrable (fun u => Real.exp (-u * x)) μ)
    (hsummable : ∀ x step, 0 < x → 0 < step →
      Summable (fun j : ℕ => laplaceKernel μ (x + j * step)))
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i)
    (hstart : 1 ≤ s 0) (hstart_eq : t 0 = s 0)
    (hnext : ∀ i, t (i + 1) = t i + s (i + 1))
    (hmass : ∀ i, q i ≤ min (s i) (s (i + 1)))
    (hsum : HasSum (fun i => q i * laplaceKernel μ (t i))
      (samplingTail (laplaceKernel μ) 0 1)) :
    ∀ i, s i = 1 ∧ t i = (i : ℝ) + 1 ∧ q i = 1 := by
  apply half_source_rigid (laplaceKernel μ) t s q
    (fun x hx => laplaceKernel_pos μ x (hint x hx))
    hs ht hstart hstart_eq hnext hmass hsummable
  · intro x hx
    exact strictMonoOn_samplingHead_laplace μ x hx hpositive hint
      (fun step hstep => hsummable x step hx hstep)
  · intro x hx
    exact strictAntiOn_samplingTail_laplace μ x hx hpositive hint hsummable
  · exact hsum

end CenteredCircle.AllN

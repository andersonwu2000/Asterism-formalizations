import ACS12.GammaLowSource
import CenteredCircle.PeriodicEnumeration

/-! Undivided equality in the actual exterior packing. -/

namespace ACS12.GammaMeasure

open MeasureTheory Set
open scoped BigOperators
open CenteredCircle.AllN (CircleKernelKind densityPolynomial densityPolynomial_pos
  continuous_densityPolynomial polyA polyB polyA_lt_polyB
  densityMeasure densityMeasure_ne_zero densityMeasure_positive_support laplaceKernel
  laplace_density_integral integrable_exp_density samplingHead samplingTail
  strictMonoOn_samplingHead_laplace strictAntiOn_samplingTail_laplace QuadratureData
  imageTail NormalizedCircleChart AnchoredCircleSource)

private theorem imageMoment_strict_sampling {p L : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (kind : CircleKernelKind) :
    (∀ t, 0 < t → StrictMonoOn (samplingHead (imageMoment p L kind 0) t) (Ioi 0)) ∧
      (∀ t, 0 ≤ t → StrictAntiOn (samplingTail (imageMoment p L kind 0) t) (Ioi 0)) := by
  let g (s : ℝ) := imageDensity p L s * densityPolynomial kind s
  let μ := densityMeasure g
  have hg : Measurable g := ((continuous_imageDensity hp hL).mul
    (continuous_densityPolynomial kind)).measurable
  have hpos (s : ℝ) (hs : 0 < s) : 0 < g s :=
    mul_pos (imageDensity_pos hp hL hs) (densityPolynomial_pos kind hs)
  letI : NeZero μ := ⟨densityMeasure_ne_zero g hg hpos⟩
  have hae := densityMeasure_positive_support g hg
  have heq : laplaceKernel μ = imageMoment p L kind 0 := by
    funext t
    rw [laplace_density_integral g hg (fun s hs => (hpos s hs).le)]
    simp only [imageMoment, imageMomentWeight, pow_zero, one_mul, g]
  obtain ⟨C, _, hC⟩ := imageDensity_linear_bound hp hp₂ hL
  have hb (s : ℝ) (hs : 0 < s) : g s ≤ C * s ^ 2 := by
    have he : Real.exp (-s) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hs)
    have hB : polyB s < s := by unfold polyB; linarith
    have hpoly : densityPolynomial kind s ≤ s := by
      cases kind
      · exact ((polyA_lt_polyB hs).trans hB).le
      · exact hB.le
    have h := mul_le_mul (hC s hs) hpoly (densityPolynomial_pos kind hs).le
      ((imageDensity_pos hp hL hs).le.trans (hC s hs))
    dsimp only [g]
    convert h using 1
    ring
  have hi (t : ℝ) (ht : 0 < t) : Integrable (fun u : ℝ => Real.exp (-u * t)) μ :=
    integrable_exp_density g C t hg (fun s hs => (hpos s hs).le) hb ht
  have hsum (t s : ℝ) (ht : 0 < t) (hs : 0 < s) :
      Summable (fun j : ℕ => laplaceKernel μ (t + (j : ℝ) * s)) := by
    simp_rw [heq]
    exact imageMoment_samples_summable hp hp₂ hL ht hs kind
  constructor
  · intro t ht
    rw [← heq]
    exact strictMonoOn_samplingHead_laplace μ t ht hae hi (fun s hs => hsum t s ht hs)
  · intro t ht
    rw [← heq]
    exact strictAntiOn_samplingTail_laplace μ t ht hae hi hsum

theorem imageMoment_quadratureData {p L d : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hd : 0 < d) (kind : CircleKernelKind) :
    QuadratureData (imageMoment p L kind 0) d := by
  obtain ⟨hh, ht⟩ := imageMoment_strict_sampling hp hp₂ hL kind
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun x hx => (imageMoment_pos hp hp₂ hL (hd.trans_le hx) kind 0).le
  · exact fun x s hx hs => imageMoment_samples_summable hp hp₂ hL (hd.trans_le hx) hs kind
  · exact fun x hx => (hh x (hd.trans_le hx)).monotoneOn
  · exact fun x hx => (ht x (hd.le.trans hx)).antitoneOn
  · exact (ht 0 le_rfl).antitoneOn.mono (fun x hx => hd.trans_le hx)

private theorem periodic_kernel_hasSum {n : ℕ} [NeZero n] {L : ℝ} (hL : 0 < L)
    (K : ℝ → ℝ) (a q : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hq : ∀ i, 0 ≤ q i)
    (hK : ∀ x, 0 < x → 0 ≤ K x)
    (hsum : ∀ t, 0 < t → Summable (fun j : ℕ => K (t + (j : ℝ) * L))) :
    HasSum (fun j => CenteredCircle.AllN.periodicMass q j *
      K (CenteredCircle.AllN.periodicPosition L a j)) (∑ i, q i * imageTail K L (a i)) := by
  let f : Fin n × ℕ → ℝ := fun p => q p.1 * K (a p.1 + (p.2 : ℝ) * L)
  have hs : Summable f := by
    apply (summable_prod_of_nonneg (fun p => mul_nonneg (hq p.1)
      (hK _ (add_pos_of_pos_of_nonneg (ha p.1) (mul_nonneg (Nat.cast_nonneg p.2) hL.le))))).mpr
    exact ⟨fun i => (hsum (a i) (ha i)).mul_left (q i), (hasSum_fintype _).summable⟩
  have he : (∑' p, f p) = ∑ i, q i * imageTail K L (a i) := by
    rw [hs.tsum_prod]
    simp only [f, tsum_fintype, tsum_mul_left, imageTail]
  have h := (CenteredCircle.AllN.periodicEnumeration n).hasSum_iff.mpr hs.hasSum
  rw [he] at h
  exact h

private theorem imageMoment_left_saturated {ι : Type*} [Fintype ι] [Nonempty ι]
    [DecidableEq ι] (S : AnchoredCircleSource ι) {p : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (hcaps : S.HasCircularMassCaps)
    (hSat : S.leftExterior (imageMoment p S.period .a 0) =
      samplingTail (imageMoment p S.period .a 0) 0 1) :
    ∀ i, S.mass i = 1 := by
  letI : NeZero (Fintype.card ι) := ⟨Fintype.card_ne_zero⟩
  obtain ⟨e, he⟩ := CenteredCircle.AllN.exists_sorted_equiv S.leftDistance S.leftDistance_injective
  let L := S.period
  let K := imageMoment p L .a 0
  let a := S.leftDistance ∘ e
  let q := S.mass ∘ e
  let t := CenteredCircle.AllN.periodicPosition L a
  let s := CenteredCircle.AllN.orderedGap t
  have hL : 0 < L := S.period_pos
  have ha (i : Fin (Fintype.card ι)) : 0 < a i := S.leftDistance_pos (e i)
  have haL (i : Fin (Fintype.card ι)) : a i ≤ L := S.leftDistance_le_period (e i)
  have hfirst : 1 ≤ t 0 := by
    dsimp only [t]
    rw [CenteredCircle.AllN.periodicPosition_zero]
    exact S.leftDistance_ge_one hcaps (e 0)
  obtain ⟨hs, ht, hs₀, hs₁, hnext⟩ := CenteredCircle.AllN.orderedGap_geometry
    (CenteredCircle.AllN.strictMono_periodicPosition hL ha haL he) hfirst
  have hcap := CenteredCircle.AllN.periodicMass_gap_caps hL ha haL he
    (fun i => S.leftDistance_mass_le hcaps (e i))
    (fun i j hij => S.leftDistance_circular_caps hcaps (e i) (e j) (e.injective.ne hij))
  have hsum := periodic_kernel_hasSum hL K a q ha (fun i => (S.mass_pos (e i)).le)
    (fun t ht => (imageMoment_pos hp hp₂ hL ht .a 0).le)
    (fun t ht => imageMoment_samples_summable hp hp₂ hL ht hL .a)
  have hrewrite : (∑ i, q i * imageTail K L (a i)) = S.leftExterior K := by
    unfold AnchoredCircleSource.leftExterior
    exact Equiv.sum_comp e (fun i => S.mass i * imageTail K L (S.leftDistance i))
  rw [hrewrite, hSat] at hsum
  obtain ⟨hh, htail⟩ := imageMoment_strict_sampling hp hp₂ hL .a
  have hr := CenteredCircle.AllN.half_source_rigid K t s (CenteredCircle.AllN.periodicMass q)
    (fun x hx => imageMoment_pos hp hp₂ hL hx .a 0) hs ht hs₀ hs₁ hnext hcap
    (fun x step hx hstep => imageMoment_samples_summable hp hp₂ hL hx hstep .a) hh htail hsum
  intro i
  let j := e.symm i
  have hj := (hr j.val).2.2
  rw [CenteredCircle.AllN.periodicMass_first_period q j] at hj
  simpa [q, j] using hj

private theorem imageSlope_unit_summable {p L : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (hL : 0 < L) : Summable (fun j : ℕ => imageSlope p L ((j : ℝ) + 1)) := by
  obtain ⟨C, hC₀, hC⟩ := imageDensity_linear_bound hp hp₂ hL
  have hnonneg (t : ℝ) (_ : 0 < t) : 0 ≤ imageSlope p L t := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_nonneg (mul_nonneg (imageDensity_pos hp hL hs).le hs.le) (Real.exp_pos _).le
  have hbound (t : ℝ) (ht : 0 < t) : imageSlope p L t ≤ 2 * C / t ^ 3 := by
    calc
      imageSlope p L t ≤ ∫ s : ℝ in Ioi 0, C * (s ^ (2 : ℕ) * Real.exp (-s * t)) := by
        apply integral_mono_ae (imageSlope_integrable hp hL ht)
          ((CenteredCircle.AllN.integrable_power_exponential 2 t ht).const_mul C)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        change 0 < s at hs
        calc
          _ ≤ ((C * s) * s) * Real.exp (-s * t) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hC s hs) hs.le)
              (Real.exp_pos _).le
          _ = _ := by ring
      _ = _ := by
        rw [integral_const_mul, CenteredCircle.AllN.integral_power_exponential 2 t ht]
        norm_num
        ring
  simpa only [mul_one, add_comm] using CenteredCircle.AllN.summable_of_cubic_decay
    (imageSlope p L) (2 * C) 1 1 (by positivity) zero_lt_one zero_lt_one hnonneg hbound

theorem imageMoment_unit_tail_sum {p L : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (hL : 0 < L) :
    samplingTail (imageMoment p L .a 0) 0 1 + samplingTail (imageMoment p L .b 0) 0 1 =
      imageSlope p L 1 := by
  have hOne : 0 < (1 : ℝ) := by norm_num
  have ha : Summable (fun j : ℕ => imageMoment p L .a 0 ((j : ℝ) + 1)) := by
    simpa only [mul_one, add_comm] using imageMoment_samples_summable hp hp₂ hL hOne hOne .a
  have hb : Summable (fun j : ℕ => imageMoment p L .b 0 ((j : ℝ) + 1)) := by
    simpa only [mul_one, add_comm] using imageMoment_samples_summable hp hp₂ hL hOne hOne .b
  have hu := imageSlope_unit_summable hp hp₂ hL
  have hpair (j : ℕ) :
      imageMoment p L .a 0 ((j : ℝ) + 1) + imageMoment p L .b 0 ((j : ℝ) + 1) =
        imageSlope p L ((j : ℝ) + 1) - imageSlope p L ((j : ℝ) + 1 + 1) := by
    rw [imageMoment_zero_a hp hL (by positivity), imageMoment_zero_b hp hL (by positivity),
      imageA, imageB]
    ring
  have hu' : Summable (fun j : ℕ => imageSlope p L ((j : ℝ) + 1 + 1)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hu
  have htel := hu.tsum_eq_zero_add
  simp only [Nat.cast_zero, zero_add, Nat.cast_add, Nat.cast_one] at htel
  simp only [samplingTail, zero_add, mul_one, one_mul, Nat.cast_add, Nat.cast_one]
  rw [← ha.tsum_add hb]
  simp_rw [hpair]
  rw [hu.tsum_sub hu']
  linarith

/-- Equality of the two anchor masses forces all the original masses equal.
The proof uses the undivided exterior balances and strict packing. -/
theorem _root_.ACS12.Configuration.regular_of_anchor_mass_one {n : ℕ} {p : ℝ}
    (F : Configuration n p) (hn : 2 ≤ n) (hp : 0 < p) (hp₂ : p ≤ 2)
    (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi))
    (hb : C.source.mass C.source.neighbor = 1) :
    IsEqualMassRegular F := by
  let S := C.source
  let L := S.period
  letI : Nonempty (Fin n) := ⟨S.root⟩
  have hL : 0 < L := S.period_pos
  have hLeft : S.leftExterior (imageMoment p L .a 0) = S.leftExterior (imageA p L) := by
    unfold AnchoredCircleSource.leftExterior
    apply Finset.sum_congr rfl
    intro i _
    rw [imageTail_moment_zero_a hp hL (S.leftDistance_pos i)]
  have hRight : S.rightExterior (imageMoment p L .b 0) = S.rightExterior (imageB p L) := by
    unfold AnchoredCircleSource.rightExterior
    apply Finset.sum_congr rfl
    intro i _
    rw [imageTail_moment_zero_b hp hL (S.rightDistance_pos i)]
  obtain ⟨hA, _⟩ := F.anchored_image_balances hp C
  change S.leftExterior (imageA p L) + S.rightExterior (imageB p L) =
    imageSlope p L 1 + (1 - S.mass S.neighbor) * (imagePotential p L 1 + imageSelf p L) at hA
  rw [← hLeft, ← hRight, hb, sub_self, zero_mul, add_zero] at hA
  have hqL := S.leftExterior_quadrature (imageMoment_quadratureData hp hp₂ hL (by norm_num) .a)
    C.circular_caps
  have hqR := S.rightExterior_quadrature (imageMoment_quadratureData hp hp₂ hL (S.mass_pos _) .b)
    C.circular_caps
  rw [hb] at hqR
  have hsum := imageMoment_unit_tail_sum hp hp₂ hL
  have hSat : S.leftExterior (imageMoment p L .a 0) = samplingTail (imageMoment p L .a 0) 0 1 := by
    linarith
  have hmass := imageMoment_left_saturated S hp hp₂ C.circular_caps hSat
  apply F.equal_mass_regular hn hp.le (F.mass_pos S.root)
  intro i
  have hi := C.mass_eq i
  rw [hmass i] at hi
  simpa only [one_mul] using (div_eq_iff (F.mass_pos S.root).ne').mp hi.symm

end ACS12.GammaMeasure

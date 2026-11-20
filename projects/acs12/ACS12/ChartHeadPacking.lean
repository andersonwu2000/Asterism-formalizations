import ACS12.ChartExterior

/-! Full periodic packing while retaining the actual first atom. -/

namespace CenteredCircle.AllN

open Set Filter
open scoped BigOperators

theorem countable_source_head_bound {ι : Type*} [Countable ι]
    {K : ℝ → ℝ} {d : ℝ} (hK : QuadratureData K d)
    (t q : ι → ℝ) (hdom : ∀ i, d ≤ t i) (hinj : Function.Injective t)
    (hpairs : ∀ i j, t i < t j → q i ≤ t j - t i ∧ q j ≤ t j - t i)
    (hsum : Summable (fun i => q i * K (t i))) (i : ι) {s : ℝ} (hs : 0 < s)
    (hfirst : ∀ j, t i ≤ t j) (hqi : q i ≤ s) :
    (∑' j, q j * K (t j)) ≤ samplingHead K (t i) s := by
  classical
  apply le_of_tendsto hsum.hasSum
  filter_upwards [eventually_ge_atTop ({i} : Finset ι)] with W hW
  exact finite_source_head_bound hK t q W (fun j _ => hdom j) hinj.injOn
    (fun j _ k _ => hpairs j k) i (hW (Finset.mem_singleton_self _)) s hs
    (fun j _ => hfirst j) hqi

theorem periodic_source_head_bound {ι : Type*} [Fintype ι]
    {K : ℝ → ℝ} {L d : ℝ} (hK : QuadratureData K d) (hd : 0 < d) (hL : 0 < L)
    (a q : ι → ℝ) (haL : ∀ i, a i ≤ L) (hdom : ∀ i, d ≤ a i)
    (hinj : Function.Injective a) (hq : ∀ i, 0 ≤ q i) (hmass : ∀ i, q i ≤ a i)
    (hcaps : ∀ i j, i ≠ j → q i ≤ |a j - a i| ∧ q i ≤ L - |a j - a i|)
    (i : ι) {s : ℝ} (hs : 0 < s) (hfirst : ∀ j, a i ≤ a j) (hqi : q i ≤ s) :
    (∑ j, q j * imageTail K L (a j)) ≤ samplingHead K (a i) s := by
  classical
  let t (p : ι × ℕ) := a p.1 + p.2 * L
  have ha (j : ι) : 0 < a j := hd.trans_le (hdom j)
  have ht (p : ι × ℕ) : d ≤ t p :=
    le_trans (hdom p.1) (le_add_of_nonneg_right (by positivity))
  have hsum : Summable (fun p : ι × ℕ => q p.1 * K (t p)) := by
    apply (summable_prod_of_nonneg (fun p => mul_nonneg (hq p.1) (hK.nonneg _ (ht p)))).mpr
    exact ⟨fun j => (hK.summable _ _ (hdom j) hL).mul_left (q j), (hasSum_fintype _).summable⟩
  have hmin (p : ι × ℕ) : t (i, 0) ≤ t p := by
    simp only [t, Nat.cast_zero, zero_mul, add_zero]
    exact (hfirst p.1).trans (le_add_of_nonneg_right (by positivity))
  have hb := countable_source_head_bound hK t (fun p : ι × ℕ => q p.1) ht
    (periodic_lift_injective hL ha haL hinj)
    (periodic_lift_exclusion hL ha haL hmass hcaps) hsum (i, 0) hs hmin hqi
  have he : (∑' p : ι × ℕ, q p.1 * K (t p)) = ∑ j, q j * imageTail K L (a j) := by
    rw [hsum.tsum_prod]
    simp only [t, tsum_fintype, tsum_mul_left, imageTail]
  simpa only [he, t, Nat.cast_zero, zero_mul, add_zero] using hb

end CenteredCircle.AllN

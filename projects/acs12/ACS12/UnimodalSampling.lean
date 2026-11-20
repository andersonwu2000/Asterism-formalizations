import CenteredCircle.Quadrature
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! A whole arithmetic mesh of a one-peak function costs its integral and one height. -/

namespace CenteredCircle.AllN

open MeasureTheory Set Filter
open scoped BigOperators Topology

private theorem sum_min_adjacent {g : ℕ → ℝ} {n i : ℕ} (hi : i ≤ n)
    (hLeft : ∀ j < i, g j ≤ g (j + 1))
    (hRight : ∀ j, i ≤ j → j < n → g (j + 1) ≤ g j) :
    (∑ j ∈ Finset.range n, min (g j) (g (j + 1))) + g i =
      ∑ j ∈ Finset.range (n + 1), g j := by
  let k := n - i
  have hN : n = i + k := (Nat.add_sub_of_le hi).symm
  have hN₁ : n + 1 = i + (1 + k) := by omega
  calc
    _ = (∑ j ∈ Finset.range i, min (g j) (g (j + 1))) +
        (∑ j ∈ Finset.range k, min (g (i + j)) (g (i + j + 1))) + g i := by
      congr 1
      nth_rw 1 [hN]
      rw [Finset.sum_range_add]
    _ = (∑ j ∈ Finset.range i, g j) + (∑ j ∈ Finset.range k, g (i + j + 1)) + g i := by
      congr 2
      · apply Finset.sum_congr rfl
        intro j hj
        exact min_eq_left (hLeft j (Finset.mem_range.mp hj))
      · apply Finset.sum_congr rfl
        intro j hj
        have hj' : i + j < n := by
          have := Finset.mem_range.mp hj
          omega
        exact min_eq_right (hRight (i + j) (Nat.le_add_right _ _) hj')
    _ = ∑ j ∈ Finset.range (n + 1), g j := by
      rw [hN₁, Finset.sum_range_add, Finset.sum_range_add]
      simp only [Finset.sum_range_one]
      simp_rw [show ∀ j : ℕ, i + (1 + j) = i + j + 1 by intro j; omega]
      ring

theorem samplingHead_le_integral_add_peak_from {f : ℝ → ℝ} {x q M : ℝ}
    (hx : 0 < x) (hq : 0 < q) (hCont : ContinuousOn f (Ioi 0))
    (hInt : IntegrableOn f (Ioi 0)) (hPos : ∀ s > 0, 0 ≤ f s)
    (hPeak : ∀ s ≥ x, f s ≤ M)
    (hMin : ∀ {a b c : ℝ}, 0 < a → a ≤ b → b ≤ c → min (f a) (f c) ≤ f b)
    (hSum : Summable (fun j : ℕ => f (x + j * q))) :
    samplingHead f x q ≤ (∫ s : ℝ in Ioi 0, f s) + q * M := by
  let X (j : ℕ) := x + j * q
  let g (j : ℕ) := f (X j)
  have hX (j : ℕ) : 0 < X j := add_pos_of_pos_of_nonneg hx (mul_nonneg (Nat.cast_nonneg j) hq.le)
  have hM : Monotone X := fun i j hij =>
    add_le_add_right (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) hq.le) x
  have hC (i j : ℕ) (hij : i ≤ j) : ContinuousOn f (Icc (X i) (X j)) :=
    hCont.mono (fun _ ht => (hX i).trans_le ht.1)
  have hI (i j : ℕ) (hij : i ≤ j) : IntervalIntegrable f volume (X i) (X j) :=
    (hC i j hij).intervalIntegrable_of_Icc (hM hij)
  have hStep (j : ℕ) : q * min (g j) (g (j + 1)) ≤ ∫ t in X j..X (j + 1), f t := by
    have hX' := hM (Nat.le_succ j)
    have h := intervalIntegral.integral_mono_on hX' intervalIntegrable_const
      (hI j (j + 1) (Nat.le_succ j)) (fun s hs => hMin (hX j) hs.1 hs.2)
    have hΔ : X (j + 1) - X j = q := by simp only [X, Nat.cast_add, Nat.cast_one]; ring
    rwa [intervalIntegral.integral_const, smul_eq_mul, hΔ] at h
  have hFin (n : ℕ) : q * (∑ j ∈ Finset.range (n + 1), g j) ≤
      (∫ s : ℝ in Ioi 0, f s) + q * M := by
    obtain ⟨i, hi, hmax⟩ := (Finset.range (n + 1)).exists_max_image g
      ⟨0, Finset.mem_range.mpr (by omega)⟩
    have hi' : i ≤ n := by have := Finset.mem_range.mp hi; omega
    have hLeft (j : ℕ) (hj : j < i) : g j ≤ g (j + 1) := by
      have h := hMin (hX j) (hM (Nat.le_succ j)) (hM (by omega : j + 1 ≤ i))
      have hMax := hmax j (Finset.mem_range.mpr (by omega))
      exact (min_eq_left hMax).symm.le.trans h
    have hRight (j : ℕ) (hj : i ≤ j) (hjn : j < n) : g (j + 1) ≤ g j := by
      have h := hMin (hX i) (hM hj) (hM (Nat.le_succ j))
      have hMax := hmax (j + 1) (Finset.mem_range.mpr (by omega))
      exact (min_eq_right hMax).symm.le.trans h
    have hCells := Finset.sum_le_sum (s := Finset.range n) (fun j _ => hStep j)
    rw [← Finset.mul_sum, intervalIntegral.sum_integral_adjacent_intervals
      (fun k _ => hI k (k + 1) (Nat.le_succ k)), intervalIntegral.integral_of_le (hM (Nat.zero_le n))] at hCells
    have hDomain : Ioc (X 0) (X n) ⊆ Ioi (0 : ℝ) := fun t ht => (hX 0).trans ht.1
    have hToTotal : (∫ s : ℝ in Ioc (X 0) (X n), f s) ≤ ∫ s : ℝ in Ioi 0, f s := by
      apply setIntegral_mono_set hInt _ (Eventually.of_forall hDomain)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact hPos s hs
    rw [← sum_min_adjacent hi' hLeft hRight, mul_add]
    exact add_le_add (hCells.trans hToTotal) (mul_le_mul_of_nonneg_left (hPeak _ (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg i) hq.le))) hq.le)
  have hLim := (hSum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).const_mul q
  exact le_of_tendsto hLim (Eventually.of_forall hFin)

theorem samplingHead_le_integral_add_peak {f : ℝ → ℝ} {x q M : ℝ}
    (hx : 0 < x) (hq : 0 < q) (hCont : ContinuousOn f (Ioi 0))
    (hInt : IntegrableOn f (Ioi 0)) (hPos : ∀ s > 0, 0 ≤ f s)
    (hPeak : ∀ s > 0, f s ≤ M)
    (hMin : ∀ {a b c : ℝ}, 0 < a → a ≤ b → b ≤ c → min (f a) (f c) ≤ f b)
    (hSum : Summable (fun j : ℕ => f (x + j * q))) :
    samplingHead f x q ≤ (∫ s : ℝ in Ioi 0, f s) + q * M :=
  samplingHead_le_integral_add_peak_from hx hq hCont hInt hPos (fun s hs => hPeak s (hx.trans_le hs)) hMin hSum

end CenteredCircle.AllN

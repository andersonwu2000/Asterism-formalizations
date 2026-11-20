import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Linarith

/-!
Exact finite-prefix bookkeeping and equality rigidity for nonnegative defects.
These lemmas use ordinary real sums and HasSum, without any circle assumptions.
-/

namespace CenteredCircle.AllN

open Filter
open scoped BigOperators Topology

theorem prefix_balance (B : ℝ) (mass capital : ℕ → ℝ) (n : ℕ) :
    B - ∑ i ∈ Finset.range n, mass i =
      (B - capital 0) +
        (∑ i ∈ Finset.range n, (capital i - mass i - capital (i + 1))) +
        capital n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    linarith

theorem prefix_mass_le (mass capital : ℕ → ℝ)
    (hcapital : ∀ n, 0 ≤ capital n)
    (hstep : ∀ n, mass n + capital (n + 1) ≤ capital n) (n : ℕ) :
    (∑ i ∈ Finset.range n, mass i) ≤ capital 0 := by
  have hd : 0 ≤ ∑ i ∈ Finset.range n, (capital i - mass i - capital (i + 1)) :=
    Finset.sum_nonneg (fun i _ => by linarith [hstep i])
  have hp := prefix_balance (capital 0) mass capital n
  linarith [hcapital n]

/-- Equality in the total bound kills the boundary defect and every local defect.
The remainder is only required to be nonnegative; its convergence is not assumed. -/
theorem zero_defects_of_hasSum (B : ℝ) (mass capital : ℕ → ℝ)
    (hcapital : ∀ n, 0 ≤ capital n)
    (hstep : ∀ n, mass n + capital (n + 1) ≤ capital n)
    (hboundary : capital 0 ≤ B) (hsum : HasSum mass B) :
    B = capital 0 ∧ ∀ i, capital i - mass i - capital (i + 1) = 0 := by
  have hb : B ≤ capital 0 :=
    le_of_tendsto' hsum.tendsto_sum_nat (prefix_mass_le mass capital hcapital hstep)
  have hB : B = capital 0 := le_antisymm hb hboundary
  refine ⟨hB, fun i => ?_⟩
  have hres : Tendsto (fun n => B - ∑ j ∈ Finset.range n, mass j) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => B) atTop (𝓝 B) := tendsto_const_nhds
    simpa using hc.sub hsum.tendsto_sum_nat
  have hupper : capital i - mass i - capital (i + 1) ≤ 0 := by
    apply ge_of_tendsto hres
    filter_upwards [eventually_ge_atTop (i + 1)] with n hn
    have hi : i ∈ Finset.range n := Finset.mem_range.mpr (by omega)
    have hd := Finset.single_le_sum
      (fun j (_ : j ∈ Finset.range n) =>
        (show 0 ≤ capital j - mass j - capital (j + 1) by linarith [hstep j])) hi
    have hp := prefix_balance B mass capital n
    linarith [hcapital n]
  exact le_antisymm hupper (by linarith [hstep i])

/-- The transition and the mass deficits vanish separately. -/
theorem transition_and_mass_zero {v next q allowance kernel : ℝ}
    (hkernel : 0 < kernel) (hmass : q ≤ allowance)
    (htransition : allowance * kernel + next ≤ v)
    (htotal : v - q * kernel - next = 0) :
    v - allowance * kernel - next = 0 ∧ q = allowance := by
  have hpaid : q * kernel ≤ allowance * kernel :=
    mul_le_mul_of_nonneg_right hmass hkernel.le
  have heq : q * kernel = allowance * kernel := by linarith
  have hq : q = allowance := (mul_right_cancel₀ (ne_of_gt hkernel)) heq
  constructor
  · rw [← hq]
    exact htotal
  · exact hq

end CenteredCircle.AllN

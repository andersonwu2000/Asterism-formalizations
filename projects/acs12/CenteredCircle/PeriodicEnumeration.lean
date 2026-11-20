import CenteredCircle.PeriodicSourceQuadrature
import Mathlib.Data.Fintype.Sort
import Mathlib.Logic.Equiv.Fin.Basic

/-! Exact enumeration of a sorted finite source and every positive image. -/

namespace CenteredCircle.AllN

open scoped BigOperators

def periodicEnumeration (n : ℕ) [NeZero n] : ℕ ≃ Fin n × ℕ :=
  (Nat.divModEquiv n).trans (Equiv.prodComm ℕ (Fin n))

noncomputable def periodicPosition {n : ℕ} [NeZero n] (L : ℝ) (a : Fin n → ℝ) (j : ℕ) : ℝ :=
  a (Fin.ofNat n j) + (j / n : ℕ) * L

noncomputable def periodicMass {n : ℕ} [NeZero n] (q : Fin n → ℝ) (j : ℕ) : ℝ :=
  q (Fin.ofNat n j)

theorem periodicPosition_first_period {n : ℕ} [NeZero n] (L : ℝ) (a : Fin n → ℝ) (i : Fin n) :
    periodicPosition L a i = a i := by
  have he : Fin.ofNat n i.val = i := by ext; simp [Fin.ofNat, Nat.mod_eq_of_lt i.isLt]
  simp only [periodicPosition, he, Nat.div_eq_of_lt i.isLt, Nat.cast_zero, zero_mul, add_zero]

theorem periodicMass_first_period {n : ℕ} [NeZero n] (q : Fin n → ℝ) (i : Fin n) :
    periodicMass q i = q i := by
  have he : Fin.ofNat n i.val = i := by ext; simp [Fin.ofNat, Nat.mod_eq_of_lt i.isLt]
  exact congrArg q he

theorem periodicPosition_zero {n : ℕ} [NeZero n] (L : ℝ) (a : Fin n → ℝ) :
    periodicPosition L a 0 = a 0 := by
  simpa only [Fin.val_zero] using periodicPosition_first_period L a (0 : Fin n)

theorem periodicPosition_period {n : ℕ} [NeZero n] (L : ℝ) (a : Fin n → ℝ) :
    periodicPosition L a n = a 0 + L := by
  simp [periodicPosition, Fin.ofNat, Nat.ne_zero_of_lt (NeZero.pos n)]

theorem strictMono_periodicPosition {n : ℕ} [NeZero n] {L : ℝ} {a : Fin n → ℝ}
    (hL : 0 < L) (ha : ∀ i, 0 < a i) (haL : ∀ i, a i ≤ L) (hm : StrictMono a) :
    StrictMono (periodicPosition L a) := by
  intro j k hjk
  have hquot : j / n ≤ k / n := Nat.div_le_div_right hjk.le
  rcases eq_or_lt_of_le hquot with hq | hq
  · have hr : j % n < k % n := by
      have hj := Nat.div_add_mod j n
      have hk := Nat.div_add_mod k n
      rw [hq] at hj
      omega
    have he : Fin.ofNat n j < Fin.ofNat n k := by exact hr
    have hh := hm he
    simp only [periodicPosition, hq]
    linarith
  · change a (Fin.ofNat n j) + (j / n : ℕ) * L < a (Fin.ofNat n k) + (k / n : ℕ) * L
    have hreal : ((j / n : ℕ) : ℝ) + 1 ≤ ((k / n : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hq
    nlinarith [ha (Fin.ofNat n k), haL (Fin.ofNat n j)]

noncomputable def orderedGap (t : ℕ → ℝ) : ℕ → ℝ
  | 0 => t 0
  | j + 1 => t (j + 1) - t j

theorem orderedGap_geometry {t : ℕ → ℝ} (ht : StrictMono t) (hstart : 1 ≤ t 0) :
    (∀ i, 0 < orderedGap t i) ∧ (∀ i, 0 < t i) ∧
    1 ≤ orderedGap t 0 ∧ t 0 = orderedGap t 0 ∧
    ∀ i, t (i + 1) = t i + orderedGap t (i + 1) := by
  have hp : 0 < t 0 := by linarith
  refine ⟨?_, ?_, hstart, rfl, ?_⟩
  · intro i
    cases i with
    | zero => exact hp
    | succ i => exact sub_pos.mpr (ht (Nat.lt_succ_self i))
  · intro i
    exact lt_of_lt_of_le hp (ht.monotone (Nat.zero_le i))
  · intro i
    dsimp [orderedGap]
    ring

theorem periodicMass_gap_caps {n : ℕ} [NeZero n] {L : ℝ} {a q : Fin n → ℝ}
    (hL : 0 < L) (ha : ∀ i, 0 < a i) (haL : ∀ i, a i ≤ L) (hmono : StrictMono a)
    (hmass : ∀ i, q i ≤ a i)
    (hcaps : ∀ i j, i ≠ j → q i ≤ |a j - a i| ∧ q i ≤ L - |a j - a i|) :
    ∀ j, periodicMass q j ≤ min (orderedGap (periodicPosition L a) j)
      (orderedGap (periodicPosition L a) (j + 1)) := by
  have ht := strictMono_periodicPosition hL ha haL hmono
  have hp (j k : ℕ) (hjk : j < k) :
      periodicMass q j ≤ periodicPosition L a k - periodicPosition L a j ∧
      periodicMass q k ≤ periodicPosition L a k - periodicPosition L a j := by
    exact periodic_lift_exclusion hL ha haL hmass hcaps
      (periodicEnumeration n j) (periodicEnumeration n k) (ht hjk)
  intro j
  apply le_min
  · cases j with
    | zero =>
      simpa only [orderedGap, periodicPosition, periodicMass, Nat.zero_div,
        Nat.cast_zero, zero_mul, add_zero] using hmass (Fin.ofNat n 0)
    | succ j => exact (hp j (j + 1) (Nat.lt_succ_self j)).2
  · exact (hp j (j + 1) (Nat.lt_succ_self j)).1

theorem periodic_circle_hasSum {n : ℕ} [NeZero n] {L : ℝ} (hL : 0 < L)
    (kind : CircleKernelKind) (a q : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hq : ∀ i, 0 ≤ q i) :
    HasSum (fun j => periodicMass q j * circleKernel L kind (periodicPosition L a j))
      (∑ i, q i * imageTail (circleKernel L kind) L (a i)) := by
  let f : Fin n × ℕ → ℝ := fun p => q p.1 * circleKernel L kind (a p.1 + p.2 * L)
  have hs : Summable f := by
    apply (summable_prod_of_nonneg (fun p =>
      mul_nonneg (hq p.1) (circleKernel_pos hL kind _
        (add_pos_of_pos_of_nonneg (ha p.1) (mul_nonneg (Nat.cast_nonneg p.2) hL.le))).le)).mpr
    exact ⟨fun i => (circleKernel_summable hL kind _ _ (ha i) hL).mul_left (q i),
      (hasSum_fintype _).summable⟩
  have he : (∑' p, f p) = ∑ i, q i * imageTail (circleKernel L kind) L (a i) := by
    rw [hs.tsum_prod]
    simp only [f, tsum_fintype, tsum_mul_left, imageTail]
  have hh := (periodicEnumeration n).hasSum_iff.mpr hs.hasSum
  rw [he] at hh
  exact hh

theorem exists_sorted_equiv {ι : Type*} [Fintype ι] (a : ι → ℝ) (hinj : Function.Injective a) :
    ∃ e : Fin (Fintype.card ι) ≃ ι, StrictMono (a ∘ e) := by
  letI : LinearOrder ι := LinearOrder.lift' a hinj
  let e := monoEquivOfFin ι rfl
  exact ⟨e.toEquiv, e.strictMono⟩

end CenteredCircle.AllN

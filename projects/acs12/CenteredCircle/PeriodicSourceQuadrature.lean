import CenteredCircle.FiniteSourceQuadrature
import CenteredCircle.AnchoredSource

/-! The actual finite periodic image sum inherits finite-source quadrature. -/

namespace CenteredCircle.AllN

open Set
open scoped BigOperators

theorem periodic_lift_index_le {ι : Type*} {L : ℝ} {a : ι → ℝ}
    (hL : 0 < L) (ha : ∀ i, 0 < a i) (haL : ∀ i, a i ≤ L)
    {i j : ι} {k l : ℕ}
    (h : a i + k * L ≤ a j + l * L) : k ≤ l := by
  by_contra hn
  have hnat : l + 1 ≤ k := by omega
  have hreal : (l : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hnat
  nlinarith [ha i, haL j]

theorem periodic_lift_injective {ι : Type*} {L : ℝ} {a : ι → ℝ}
    (hL : 0 < L) (ha : ∀ i, 0 < a i) (haL : ∀ i, a i ≤ L)
    (hinj : Function.Injective a) :
    Function.Injective (fun p : ι × ℕ => a p.1 + p.2 * L) := by
  intro p r he
  dsimp only at he
  have hkl := periodic_lift_index_le hL ha haL he.le
  have hlk := periodic_lift_index_le hL ha haL he.ge
  have hnat : p.2 = r.2 := le_antisymm hkl hlk
  have hi : p.1 = r.1 := hinj (by rw [hnat] at he; linarith)
  exact Prod.ext hi hnat

theorem periodic_lift_exclusion {ι : Type*} {L : ℝ} {a q : ι → ℝ}
    (hL : 0 < L) (ha : ∀ i, 0 < a i) (haL : ∀ i, a i ≤ L)
    (hmass : ∀ i, q i ≤ a i)
    (hcaps : ∀ i j, i ≠ j → q i ≤ |a j - a i| ∧ q i ≤ L - |a j - a i|)
    (p r : ι × ℕ) (hpr : a p.1 + p.2 * L < a r.1 + r.2 * L) :
    q p.1 ≤ (a r.1 + r.2 * L) - (a p.1 + p.2 * L) ∧
    q r.1 ≤ (a r.1 + r.2 * L) - (a p.1 + p.2 * L) := by
  have hkl := periodic_lift_index_le hL ha haL hpr.le
  by_cases he : p.1 = r.1
  · have hne : p.2 ≠ r.2 := by intro h; rw [he, h] at hpr; exact lt_irrefl _ hpr
    have hstep : p.2 + 1 ≤ r.2 := by omega
    have hr : (p.2 : ℝ) + 1 ≤ (r.2 : ℝ) := by exact_mod_cast hstep
    have hp : q p.1 ≤ L := (hmass p.1).trans (haL p.1)
    rw [← he]
    constructor <;> nlinarith
  · have hp := hcaps p.1 r.1 he
    have hr := hcaps r.1 p.1 (Ne.symm he)
    rw [abs_sub_comm (a p.1) (a r.1)] at hr
    rcases eq_or_lt_of_le hkl with hk | hk
    · have had : 0 ≤ a r.1 - a p.1 := by rw [hk] at hpr; linarith
      rw [abs_of_nonneg had] at hp hr
      rw [hk]
      constructor <;> linarith
    · have hstep : (p.2 : ℝ) + 1 ≤ (r.2 : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hk
      have habs : a p.1 - a r.1 ≤ |a r.1 - a p.1| := by
        simpa only [neg_sub] using neg_le_abs (a r.1 - a p.1)
      constructor <;> nlinarith [hp.2, hr.2]

theorem periodic_source_quadrature {ι : Type*} [Fintype ι]
    {K : ℝ → ℝ} {L d : ℝ} (hK : QuadratureData K d) (hd : 0 < d) (hL : 0 < L)
    (a q : ι → ℝ) (haL : ∀ i, a i ≤ L) (hdom : ∀ i, d ≤ a i)
    (hinj : Function.Injective a) (hq : ∀ i, 0 ≤ q i) (hmass : ∀ i, q i ≤ a i)
    (hcaps : ∀ i j, i ≠ j → q i ≤ |a j - a i| ∧ q i ≤ L - |a j - a i|) :
    (∑ i, q i * imageTail K L (a i)) ≤ samplingTail K 0 d := by
  classical
  have ha (i : ι) : 0 < a i := lt_of_lt_of_le hd (hdom i)
  have hlift (p : ι × ℕ) : d ≤ a p.1 + p.2 * L :=
    le_trans (hdom p.1) (le_add_of_nonneg_right (by positivity))
  have hsum : Summable (fun p : ι × ℕ => q p.1 * K (a p.1 + p.2 * L)) := by
    apply (summable_prod_of_nonneg (fun p => mul_nonneg (hq p.1) (hK.nonneg _ (hlift p)))).mpr
    exact ⟨fun i => (hK.summable _ _ (hdom i) hL).mul_left (q i), (hasSum_fintype _).summable⟩
  have hb := countable_source_quadrature hK hd
    (fun p : ι × ℕ => a p.1 + p.2 * L) (fun p => q p.1) hlift
    (periodic_lift_injective hL ha haL hinj)
    (fun p => le_trans (hmass p.1) (le_add_of_nonneg_right (by positivity)))
    (periodic_lift_exclusion hL ha haL hmass hcaps) hsum
  have he : (∑' p : ι × ℕ, q p.1 * K (a p.1 + p.2 * L)) =
      ∑ i, q i * imageTail K L (a i) := by
    rw [hsum.tsum_prod]
    simp only [tsum_fintype, tsum_mul_left, imageTail]
  rw [he] at hb
  exact hb

end CenteredCircle.AllN

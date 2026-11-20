import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Tactic

/-! A polynomial certificate on the closed unit interval. -/
namespace ACS12

open Set Finset

theorem bernsteinCertificate_pos {n : ℕ} {v c : ℝ} {f : ℕ → ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) (hc : 0 < c) (hf : ∀ j ∈ range (n + 1), c ≤ f j) :
    0 < ∑ j ∈ range (n + 1), f j * ((n.choose j : ℝ) * v ^ j * (1 - v) ^ (n - j)) := by
  have hS : (∑ j ∈ range (n + 1), (n.choose j : ℝ) * v ^ j * (1 - v) ^ (n - j)) = 1 := by
    simpa only [show v + (1 - v) = 1 by ring,one_pow,mul_comm,mul_left_comm,mul_assoc] using
      ((add_pow v (1 - v) n).symm)
  have h := Finset.sum_le_sum (s := range (n + 1)) fun j hj =>
    mul_le_mul_of_nonneg_right (hf j hj) (show 0 ≤ (n.choose j : ℝ) * v ^ j * (1 - v) ^ (n - j) by
      have hv₀ := hv.1
      have hv₁ := sub_nonneg.mpr hv.2
      positivity)
  rw [← Finset.mul_sum,hS,mul_one] at h
  exact hc.trans_le h

theorem bernsteinFinCertificate_pos {n : ℕ} {v c : ℝ} {f : Fin (n + 1) → ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) (hc : 0 < c) (hf : ∀ j, c ≤ f j) :
    0 < ∑ j : Fin (n + 1), f j * ((n.choose j : ℝ) * v ^ (j : ℕ) * (1 - v) ^ (n - j)) := by
  have hS : (∑ j : Fin (n + 1), (n.choose j : ℝ) * v ^ (j : ℕ) * (1 - v) ^ (n - j)) = 1 := by
    let B (j : ℕ) := (n.choose j : ℝ) * v ^ j * (1 - v) ^ (n - j)
    change (∑ j : Fin (n + 1), B j.val) = 1
    rw [Fin.sum_univ_eq_sum_range]
    simpa only [B,show v + (1 - v) = 1 by ring,one_pow,mul_comm,mul_left_comm,mul_assoc] using
      ((add_pow v (1 - v) n).symm)
  have h := Finset.sum_le_sum (s := Finset.univ) fun j (_ : j ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_right (hf j) (show 0 ≤ (n.choose j : ℝ) * v ^ (j : ℕ) * (1 - v) ^ (n - j) by
      have hv₀ := hv.1
      have hv₁ := sub_nonneg.mpr hv.2
      positivity)
  rw [← Finset.mul_sum,hS,mul_one] at h
  exact hc.trans_le h

theorem bernsteinScaledFinCertificate_pos {n d : ℕ} {v : ℝ} {f : Fin (n + 1) → ℕ}
    (hv : v ∈ Icc (0 : ℝ) 1) (hd : 0 < d) (hf : ∀ j, n.choose j.val ≤ f j) :
    0 < (∑ j : Fin (n + 1), (f j : ℝ) * v ^ j.val * (1 - v) ^ (n - j.val)) / (d : ℝ) := by
  have hD : 0 < (d : ℝ) := by exact_mod_cast hd
  apply div_pos _ hD
  have h := bernsteinFinCertificate_pos (n := n) (f := fun j => (f j : ℝ) / n.choose j.val) hv
    zero_lt_one (fun j => by
      apply (one_le_div (by exact_mod_cast Nat.choose_pos (Nat.lt_succ_iff.mp j.isLt))).mpr
      exact_mod_cast hf j)
  convert h using 1
  apply Finset.sum_congr rfl
  intro j _
  have hC : (n.choose j.val : ℝ) ≠ 0 := by
    exact (show (0 : ℝ) < n.choose j.val by exact_mod_cast Nat.choose_pos (Nat.lt_succ_iff.mp j.isLt)).ne'
  field_simp [hC]

end ACS12

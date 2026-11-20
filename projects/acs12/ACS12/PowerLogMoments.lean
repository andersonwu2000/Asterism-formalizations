import ACS12.PureCMoments
import Mathlib.Analysis.Calculus.SmoothSeries

/-! Termwise exponent derivatives of complete power and log-power tails. -/
namespace ACS12.GammaMeasure

open Set

noncomputable def powerLogTail (q : ℝ) (k m : ℕ) : ℝ :=
  ∑' j : ℕ, ((m : ℝ) + j) ^ (-q) * Real.log ((m : ℝ) + j) ^ k

private theorem powerLogTerm_le {q a e x : ℝ} (he : 0 < e) (hqa : a ≤ q) (hx : 1 ≤ x) (k : ℕ) :
    x ^ (-q) * Real.log x ^ k ≤ (k.factorial : ℝ) * e⁻¹ ^ k * x ^ (-(a - e)) := by
  have hLog := Real.log_nonneg hx
  have hx₀ := zero_lt_one.trans_le hx
  have hE := Real.pow_div_factorial_le_exp (e * Real.log x) (mul_nonneg he.le hLog) k
  have hF : (0 : ℝ) < k.factorial := Nat.cast_pos.mpr (Nat.factorial_pos k)
  have hX : (e * Real.log x) ^ k ≤ x ^ e * k.factorial := by
    rw [Real.rpow_def_of_pos hx₀, mul_comm (Real.log x) e]
    exact (div_le_iff₀ hF).mp hE
  have hP : 0 < e ^ k := pow_pos he k
  have hB : Real.log x ^ k ≤ (k.factorial : ℝ) * e⁻¹ ^ k * x ^ e := by
    calc
      _ ≤ x ^ e * k.factorial / e ^ k := by
        apply (le_div_iff₀ hP).mpr
        rw [mul_comm (Real.log x ^ k), ← mul_pow]
        exact hX
      _ = _ := by rw [div_eq_mul_inv, inv_pow]; ring
  have hQ : x ^ (-q) ≤ x ^ (-a) :=
    Real.rpow_le_rpow_of_exponent_le hx (neg_le_neg hqa)
  calc
    _ ≤ x ^ (-a) * ((k.factorial : ℝ) * e⁻¹ ^ k * x ^ e) :=
      mul_le_mul hQ hB (pow_nonneg hLog _) (Real.rpow_nonneg hx₀.le _)
    _ = _ := by
      have h := (Real.rpow_add hx₀ (-a) e).symm
      rw [show -(a - e) = -a + e by ring, ← h]
      ring

private theorem powerLogTerm_hasDerivAt {x : ℝ} (hx : 0 < x) (q : ℝ) (k : ℕ) :
    HasDerivAt (fun y : ℝ => x ^ (-y) * Real.log x ^ k)
      (-(x ^ (-q) * Real.log x ^ (k + 1))) q := by
  convert (((hasDerivAt_id q).neg.const_rpow hx).mul_const (Real.log x ^ k)) using 1
  simp only [pow_succ, id_eq, Pi.neg_apply]
  ring

theorem powerLogTail_summable {q : ℝ} (hq : 1 < q) (k m : ℕ) (hm : 1 ≤ m) :
    Summable (fun j : ℕ => ((m : ℝ) + j) ^ (-q) * Real.log ((m : ℝ) + j) ^ k) := by
  let e := (q - 1) / 2
  have he : 0 < e := by dsimp only [e]; linarith only [hq]
  have hqe : 1 < q - e := by dsimp only [e]; linarith only [hq]
  have hS := (powerTail_summable hqe m).mul_left ((k.factorial : ℝ) * e⁻¹ ^ k)
  apply Summable.of_nonneg_of_le _ _ hS
  · intro j
    have hx : 1 ≤ (m : ℝ) + j := (show (1 : ℝ) ≤ m by exact_mod_cast hm).trans (le_add_of_nonneg_right (Nat.cast_nonneg _))
    exact mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hx) _) (pow_nonneg (Real.log_nonneg hx) _)
  · intro j
    have hx : 1 ≤ (m : ℝ) + j := (show (1 : ℝ) ≤ m by exact_mod_cast hm).trans (le_add_of_nonneg_right (Nat.cast_nonneg _))
    exact powerLogTerm_le he le_rfl hx k

theorem powerLogTail_zero (q : ℝ) (m : ℕ) : powerLogTail q 0 m = powerTail q m := by
  simp only [powerLogTail, powerTail, pow_zero, mul_one]

theorem powerLogTail_hasDerivAt {q : ℝ} (hq : 1 < q) (k m : ℕ) (hm : 1 ≤ m) :
    HasDerivAt (fun y : ℝ => powerLogTail y k m) (-powerLogTail q (k + 1) m) q := by
  let a := (q + 1) / 2
  let e := (a - 1) / 2
  let c : ℝ := ((k + 1).factorial : ℝ) * e⁻¹ ^ (k + 1)
  let x (j : ℕ) : ℝ := (m : ℝ) + j
  have hx (j : ℕ) : 1 ≤ x j := (show (1 : ℝ) ≤ m by exact_mod_cast hm).trans (le_add_of_nonneg_right (Nat.cast_nonneg _))
  have ha : a < q := by dsimp only [a]; linarith only [hq]
  have ha₁ : 1 < a := by dsimp only [a]; linarith only [hq]
  have he : 0 < e := by dsimp only [e]; linarith only [ha₁]
  have hae : 1 < a - e := by dsimp only [e]; linarith only [ha₁]
  have hS : Summable (fun j : ℕ => c * x j ^ (-(a - e))) :=
    (powerTail_summable hae m).mul_left c
  have hPoint (j : ℕ) (y : ℝ) (hy : y ∈ Ioi a) :
      ‖-(x j ^ (-y) * Real.log (x j) ^ (k + 1))‖ ≤ c * x j ^ (-(a - e)) := by
    rw [norm_neg, Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (hx j)) _)
      (pow_nonneg (Real.log_nonneg (hx j)) _))]
    exact powerLogTerm_le he (mem_Ioi.mp hy).le (hx j) (k + 1)
  have h := hasDerivAt_tsum_of_isPreconnected hS isOpen_Ioi (convex_Ioi a).isPreconnected
    (fun j y _ => powerLogTerm_hasDerivAt (zero_lt_one.trans_le (hx j)) y k)
    hPoint (show q ∈ Ioi a from ha) (powerLogTail_summable hq k m hm) (show q ∈ Ioi a from ha)
  simpa only [powerLogTail, tsum_neg, x] using h

theorem pureZ_hasDerivAt {p : ℝ} (hp : 0 < p) :
    HasDerivAt pureZ (powerTail (p + 1) 1 - p * powerLogTail (p + 1) 1 1) p := by
  have h := (powerLogTail_hasDerivAt (show 1 < p + 1 by linarith only [hp]) 0 1 le_rfl).comp p
    ((hasDerivAt_id p).add_const 1)
  have hh := (hasDerivAt_id p).mul h
  convert hh using 1
  · funext q
    simp only [Pi.mul_apply, Function.comp_apply, id_eq, pureZ, powerLogTail_zero]
  · change _ = 1 * powerLogTail (p + 1) 0 1 + p * (-powerLogTail (p + 1) (0 + 1) 1 * 1)
    rw [powerLogTail_zero]
    norm_num
    ring

theorem pureQ_hasDerivAt {p : ℝ} (hp : -1 < p) :
    HasDerivAt pureQ ((2 * p + 1) * powerTail (p + 2) 1 -
      p * (p + 1) * powerLogTail (p + 2) 1 1) p := by
  have h := (powerLogTail_hasDerivAt (show 1 < p + 2 by linarith only [hp]) 0 1 le_rfl).comp p
    ((hasDerivAt_id p).add_const 2)
  have hh := ((hasDerivAt_id p).mul ((hasDerivAt_id p).add_const 1)).mul h
  convert hh using 1
  · funext q
    simp only [Pi.mul_apply, Function.comp_apply, id_eq, pureQ, powerLogTail_zero]
  · change _ = (1 * (p + 1) + p * 1) * powerLogTail (p + 2) 0 1 +
      (p * (p + 1)) * (-powerLogTail (p + 2) (0 + 1) 1 * 1)
    rw [powerLogTail_zero]
    norm_num
    ring


theorem pureZ_second_hasDerivAt {p : ℝ} (hp : 0 < p) :
    HasDerivAt (fun q => powerTail (q + 1) 1 - q * powerLogTail (q + 1) 1 1)
      (p * powerLogTail (p + 1) 2 1 - 2 * powerLogTail (p + 1) 1 1) p := by
  have h₀ := (powerLogTail_hasDerivAt (show 1 < p + 1 by linarith only [hp]) 0 1 le_rfl).comp p
    ((hasDerivAt_id p).add_const 1)
  have h₁ := (powerLogTail_hasDerivAt (show 1 < p + 1 by linarith only [hp]) 1 1 le_rfl).comp p
    ((hasDerivAt_id p).add_const 1)
  convert h₀.sub ((hasDerivAt_id p).mul h₁) using 1
  · funext q
    simp only [Pi.mul_apply, Pi.sub_apply, Function.comp_apply, id_eq, powerLogTail_zero]
  · norm_num
    ring

theorem pureQ_second_hasDerivAt {p : ℝ} (hp : -1 < p) :
    HasDerivAt (fun q => (2 * q + 1) * powerTail (q + 2) 1 -
      q * (q + 1) * powerLogTail (q + 2) 1 1)
      (2 * powerTail (p + 2) 1 - 2 * (2 * p + 1) * powerLogTail (p + 2) 1 1 +
        p * (p + 1) * powerLogTail (p + 2) 2 1) p := by
  have h₀ := (powerLogTail_hasDerivAt (show 1 < p + 2 by linarith only [hp]) 0 1 le_rfl).comp p
    ((hasDerivAt_id p).add_const 2)
  have h₁ := (powerLogTail_hasDerivAt (show 1 < p + 2 by linarith only [hp]) 1 1 le_rfl).comp p
    ((hasDerivAt_id p).add_const 2)
  have h := hasDerivAt_id p
  convert (((h.const_mul 2).const_add 1).mul h₀).sub ((h.mul (h.add_const 1)).mul h₁) using 1
  · funext q
    simp only [Pi.mul_apply, Pi.sub_apply, Function.comp_apply, id_eq, powerLogTail_zero]
    ring
  · simp only [id_eq, mul_one, one_mul, powerLogTail_zero]
    norm_num
    ring

end ACS12.GammaMeasure

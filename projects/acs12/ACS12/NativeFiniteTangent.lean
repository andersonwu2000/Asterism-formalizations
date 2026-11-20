import ACS12.NativeSelfTangent
import ACS12.NativeNormalization

/-! Averaging the adapted tangent in the original mass-weighted finite law. -/
namespace ACS12.NativeCells

open Finset
open Pressure (massTotal massTotal_pos massWeight massWeight_sum_one)

noncomputable def nativeMassEntropy {n : ℕ} (h : ℝ) (m : Fin n → ℝ) : ℝ :=
  ∑ i, massWeight m i * ((1 + 2 * h) * Real.log (relativeMass m i) -
    h * Real.log ((1 + (relativeMass m i) ^ 2) / 2))

theorem logRowMean_adapted_lt {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 2 ≤ p) (hp₄ : p ≤ 4)
    {m : Fin n → ℝ} (hm : ∀ i, 0 < m i) (hne : ∃ i, relativeMass m i ≠ 1) :
    let h := (p - 2) / 2
    let K := (massTotal m / (n : ℝ)) * analyticRow p (n : ℝ)
    Real.log (logRowMean p m) < Real.log K - nativeMassEntropy h m := by
  classical
  let w := massWeight m
  let u (i : Fin n) := (n : ℝ) * w i
  let h := (p - 2) / 2
  let n₀ : ℝ := n
  let C := massTotal m / n₀
  let S := analyticRow p
  let A := n₀ * deriv (fun x => Real.log (S x)) n₀ - (2 + h)
  let t (i : Fin n) := (u i)⁻¹
  let G (i : Fin n) := (1 + 2 * h) * Real.log (u i) - h * Real.log ((1 + (u i) ^ 2) / 2)
  let R (i : Fin n) := Real.log (m i * S (w i)⁻¹)
  have hnR : 2 ≤ n₀ := by unfold n₀; exact_mod_cast hn
  have hn₁ : 1 < n₀ := by linarith only [hnR]
  have hn₀ := zero_lt_one.trans hn₁
  have hM := massTotal_pos (show 0 < n by omega) hm
  have hC : 0 < C := div_pos hM hn₀
  have hp₀ : 0 < p := by linarith only [hp]
  have hS : 0 < S n₀ := analyticRow_pos hp₀ hn₁
  have hRel (i : Fin n) : u i = relativeMass m i := by
    unfold u w relativeMass meanMass massWeight
    field_simp [hM.ne',hn₀.ne']
  have hw (i : Fin n) : 0 < w i := div_pos (hm i) hM
  have hu (i : Fin n) : 0 < u i := mul_pos hn₀ (hw i)
  have ht (i : Fin n) : 0 < t i := inv_pos.mpr (hu i)
  have hw₁ (i : Fin n) : w i < 1 := by
    have hi : (univ.erase i : Finset (Fin n)).Nonempty := by
      apply card_pos.mp
      rw [card_erase_of_mem (mem_univ i),card_univ,Fintype.card_fin]
      omega
    have he := sum_pos (fun j _ => hm j) hi
    rw [sum_erase_eq_sub (mem_univ i)] at he
    exact (div_lt_one hM).mpr (sub_pos.mp he)
  have hN (i : Fin n) : n₀ * t i = (w i)⁻¹ := by
    change n₀ * (n₀ * w i)⁻¹ = (w i)⁻¹
    rw [mul_inv_rev]
    field_simp [hn₀.ne',(hw i).ne']
  have hN₁ (i : Fin n) : 1 < n₀ * t i := by
    rw [hN,one_lt_inv₀ (hw i)]
    exact hw₁ i
  have hMass (i : Fin n) : m i = C * u i := by
    change m i = massTotal m / n₀ * (n₀ * (m i / massTotal m))
    field_simp [hM.ne',hn₀.ne']
  have hLog (i : Fin n) : Real.log (S (n₀ * t i) /
      (S n₀ * ((t i) ^ 2 * ((1 + (t i) ^ 2) / 2) ^ h))) =
      R i - Real.log (C * S n₀) + G i := by
    have hS' := analyticRow_pos hp₀ (hN₁ i)
    have hU : 0 < (1 + (u i) ^ 2) / 2 := by positivity
    have hT : 0 < (1 + (t i) ^ 2) / 2 := by positivity
    have hTT : (1 + (t i) ^ 2) / 2 = ((1 + (u i) ^ 2) / 2) / (u i) ^ 2 := by
      unfold t
      field_simp [(hu i).ne']
      ring
    have hTpow := Real.rpow_pos_of_pos hT h
    have ht₂ := sq_pos_of_pos (ht i)
    rw [Real.log_div hS'.ne' (mul_pos hS (mul_pos ht₂ hTpow)).ne',
      Real.log_mul hS.ne' (mul_pos ht₂ hTpow).ne',
      Real.log_mul ht₂.ne' hTpow.ne',Real.log_rpow hT,Real.log_pow,
      hTT,Real.log_div hU.ne' (sq_pos_of_pos (hu i)).ne',Real.log_pow]
    unfold R G
    rw [← hN,hMass i,Real.log_mul (mul_pos hC (hu i)).ne' hS'.ne',
      Real.log_mul hC.ne' (hu i).ne',Real.log_mul hC.ne' hS.ne']
    simp only [t,Real.log_inv]
    ring
  have hP (i : Fin n) : R i ≤ Real.log (C * S n₀) - G i + A * (t i - 1) := by
    by_cases hi : t i = 1
    · have hu₁ : u i = 1 := inv_eq_one.mp hi
      have hEq := hLog i
      rw [hi,mul_one,one_pow,show (1 + 1 : ℝ) / 2 = 1 by norm_num,
        Real.one_rpow,one_mul,mul_one,div_self hS.ne',Real.log_one] at hEq
      rw [hi]
      linarith only [hEq]
    · have h := analyticRow_adapted_tangent hp hp₄ hn₁ (hN₁ i) hi
      change 0 < A * (t i - 1) - Real.log (S (n₀ * t i) /
        (S n₀ * ((t i) ^ 2 * ((1 + (t i) ^ 2) / 2) ^ ((p - 2) / 2)))) at h
      rw [hLog] at h
      linarith only [h]
  obtain ⟨j,hj⟩ := hne
  have hjt : t j ≠ 1 := fun he => hj ((hRel j) ▸ inv_eq_one.mp he)
  have hStrict := analyticRow_adapted_tangent hp hp₄ hn₁ (hN₁ j) hjt
  change 0 < A * (t j - 1) - Real.log (S (n₀ * t j) /
    (S n₀ * ((t j) ^ 2 * ((1 + (t j) ^ 2) / 2) ^ ((p - 2) / 2)))) at hStrict
  rw [hLog] at hStrict
  have hj' : R j < Real.log (C * S n₀) - G j + A * (t j - 1) := by linarith only [hStrict]
  have hSum := sum_lt_sum
    (s := (univ : Finset (Fin n))) (fun i _ => mul_le_mul_of_nonneg_left (hP i) (hw i).le)
    ⟨j,mem_univ j,mul_lt_mul_of_pos_left hj' (hw j)⟩
  have hW : ∑ i, w i = 1 := massWeight_sum_one (by omega) hm
  have hWT : (∑ i, w i * t i) = 1 := by
    have he (i : Fin n) : w i * t i = n₀⁻¹ := by
      change w i * (n₀ * w i)⁻¹ = n₀⁻¹
      field_simp [hn₀.ne',(hw i).ne']
    simp only [he,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
    exact mul_inv_cancel₀ hn₀.ne'
  have hZero : (∑ i, w i * (t i - 1)) = 0 := by simp only [mul_sub,mul_one,sum_sub_distrib,hWT,hW,sub_self]
  have he (i : Fin n) : w i * (Real.log (C * S n₀) - G i + A * (t i - 1)) =
      w i * Real.log (C * S n₀) - w i * G i + A * (w i * (t i - 1)) := by ring
  simp only [he,sum_add_distrib,sum_sub_distrib,← sum_mul,← mul_sum,hW,hZero,one_mul,mul_zero,add_zero] at hSum
  unfold nativeMassEntropy
  simp_rw [← hRel]
  change Real.log (Real.exp (∑ i, w i * R i)) < Real.log (C * S n₀) - ∑ i, w i * G i
  rw [Real.log_exp]
  exact hSum

end ACS12.NativeCells

import ACS12.GammaProductExponential

/-! The complete rate sum uniformly pays the positive finite-product exponential moments. -/
namespace ACS12.GammaMixture
open MeasureTheory Set Filter Finset

theorem gammaRate_inverse_hasSum : HasSum (fun j : ℕ => 1/gammaRate j) (1/24) := by
  have hS : Summable (fun j : ℕ => 1/((j:ℝ)+1)^2) := by
    have h := (summable_nat_add_iff 1).mpr hasSum_zeta_two.summable
    simpa only [Nat.cast_add,Nat.cast_one] using h
  have hZ := hasSum_zeta_two.summable.tsum_eq_zero_add
  simp only [Nat.cast_zero,Nat.cast_add,Nat.cast_one,zero_pow (by decide : (2:ℕ)≠0),
    div_zero,zero_add] at hZ
  rw [hasSum_zeta_two.tsum_eq] at hZ
  have hTerm (j : ℕ) : 1/gammaRate j = (1/(2*Real.pi)^2)*(1/((j:ℝ)+1)^2) := by
    unfold gammaRate
    field_simp [Real.pi_ne_zero,show (j:ℝ)+1≠0 by positivity]
    <;> ring
  have hS' : Summable (fun j : ℕ => 1/gammaRate j) :=
    (hS.mul_left (1/(2*Real.pi)^2)).congr (fun j => (hTerm j).symm)
  have hT : (∑' j : ℕ, 1/gammaRate j) = 1/24 := by
    simp_rw [hTerm]
    rw [tsum_mul_left,← hZ]
    field_simp [Real.pi_ne_zero]
    <;> ring
  exact hT ▸ hS'.hasSum

theorem gammaPartial_exponential_bound {a c : ℝ} (ha : 0 < a) (hc₀ : 0 ≤ c)
    (hc : c < gammaRate 0) (n : ℕ) :
    (∫ ω, Real.exp (c*gammaPartialTotal n ω) ∂gammaProduct a) ≤
      Real.exp ((a*(gammaRate 0/(gammaRate 0-c))*c)/24) := by
  let B := gammaRate 0/(gammaRate 0-c)
  let A := a*B*c
  have hB : 0 < B := div_pos (gammaRate_pos 0) (sub_pos.mpr hc)
  have hA : 0 ≤ A := mul_nonneg (mul_pos ha hB).le hc₀
  have hTerm (j : ℕ) :
      (gammaRate j/(gammaRate j-c))^a ≤ Real.exp (A*(1/gammaRate j)) := by
    let r := gammaRate j
    have hr : 0 < r := gammaRate_pos j
    have hcj : c < r := hc.trans_le (gammaRate_zero_le j)
    have hrc : 0 < r-c := sub_pos.mpr hcj
    have hRatio : r/(r-c) ≤ B := by
      apply (div_le_div_iff₀ hrc (sub_pos.mpr hc)).mpr
      have h := mul_nonneg hc₀ (sub_nonneg.mpr (gammaRate_zero_le j))
      unfold r
      nlinarith only [h]
    have hId : r/(r-c)-1 = (c/r)*(r/(r-c)) := by field_simp [hr.ne',hrc.ne']; ring
    have hLog := Real.log_le_sub_one_of_pos (div_pos hr hrc)
    rw [hId] at hLog
    have hL := hLog.trans (mul_le_mul_of_nonneg_left hRatio (div_nonneg hc₀ hr.le))
    rw [Real.rpow_def_of_pos (div_pos hr hrc)]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hL ha.le
    unfold A
    convert h using 1 <;> ring
  rw [(gammaPartial_exponential ha hc n).2]
  have hProd := prod_le_prod (fun j (_ : j ∈ range n) => Real.rpow_nonneg
    (div_nonneg (gammaRate_pos j).le (sub_pos.mpr (hc.trans_le (gammaRate_zero_le j))).le) _)
    (fun j (_ : j ∈ range n) => hTerm j)
  rw [← Real.exp_sum,← mul_sum] at hProd
  have hSum : (∑ j ∈ range n, 1/gammaRate j) ≤ 1/24 := by
    rw [← gammaRate_inverse_hasSum.tsum_eq]
    exact gammaRate_inverse_hasSum.summable.sum_le_tsum (range n)
      (fun j _ => div_nonneg zero_le_one (gammaRate_pos j).le)
  exact hProd.trans (Real.exp_le_exp.mpr (by
    change A*(∑ j ∈ range n, 1/gammaRate j) ≤ A/24
    nlinarith only [mul_le_mul_of_nonneg_left hSum hA]))

end ACS12.GammaMixture

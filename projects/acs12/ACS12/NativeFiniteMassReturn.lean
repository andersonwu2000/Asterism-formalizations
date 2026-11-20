import ACS12.NativeFiniteLaw
import ACS12.NativeFiniteTangent

/-! The complete finite-law comparison returns to the same original mass and row normalizations. -/
namespace ACS12.NativeCells

open Finset Pressure

theorem nativeMassEntropy_root_nonneg {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 2 ≤ p) (hP : p ≤ 4)
    {m : Fin n → ℝ} (hm : ∀ i, 0 < m i)
    (hRatio : ∀ i j, m i ≤ (7 * p / 2) * m j) :
    0 ≤ (p + 1) * Real.log (relativeRootMoment p m) + nativeMassEntropy ((p - 2) / 2) m := by
  let w : Fin n → ℝ := fun _ => 1 / (n : ℝ)
  let u := relativeMass m
  have hN : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hM := massTotal_pos hn hm
  have hMean : 0 < meanMass m := div_pos hM hN
  have hw (i : Fin n) : 0 < w i := div_pos zero_lt_one hN
  have hw₁ : ∑ i, w i = 1 := by
    simp only [w,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp [hN.ne']
  have hu (i : Fin n) : 0 < u i := div_pos (hm i) hMean
  have hu₁ : ∑ i, w i * u i = 1 := by
    simp only [w,← mul_sum]
    rw [relativeMass_sum hn hm]
    field_simp [hN.ne']
  have hU (i j : Fin n) : u i ≤ nativeSupportRatio (p + 1) * u j := by
    have h := div_le_div_of_nonneg_right (hRatio i j) hMean.le
    convert h using 1
    unfold u relativeMass nativeSupportRatio
    ring
  have hF := nativeFiniteLaw_nonneg w u hw hw₁ hu hu₁
    (by linarith only [hp] : 3 ≤ p + 1) (by linarith only [hP]) hU
  have hMoment : (∑ i, w i * u i ^ (1 / (p + 1))) = relativeRootMoment p m := by
    simp only [w,← mul_sum]
    unfold relativeRootMoment
    ring
  have hWeight (i : Fin n) : massWeight m i = w i * u i := by
    unfold massWeight w u relativeMass meanMass
    field_simp [hM.ne',hN.ne']
  have hLinear : (∑ i, w i * (u i - 1)) = 0 := by
    simp only [mul_sub,mul_one,sum_sub_distrib,hu₁,hw₁,sub_self]
  have hCost : (∑ i, w i * nativeEntropyCost (p + 1) (u i)) = nativeMassEntropy ((p - 2) / 2) m := by
    have hTerm (i : Fin n) : w i * nativeEntropyCost (p + 1) (u i) =
        massWeight m i * ((1 + 2 * ((p - 2) / 2)) * Real.log (u i) -
          ((p - 2) / 2) * Real.log ((1 + (u i) ^ 2) / 2)) -
            (p / 2) * (w i * (u i - 1)) := by
      rw [hWeight]
      unfold nativeEntropyCost
      ring
    simp only [hTerm,sum_sub_distrib,← mul_sum,hLinear,mul_zero,sub_zero,nativeMassEntropy,u]
  change 0 ≤ (p + 1) * Real.log (∑ i, w i * u i ^ (1 / (p + 1))) +
    ∑ i, w i * nativeEntropyCost (p + 1) (u i) at hF
  rwa [hMoment,hCost] at hF

theorem nativeRootRow_gt_logRowMean {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 2 ≤ p) (hP : p ≤ 4)
    {m : Fin n → ℝ} (hm : ∀ i, 0 < m i) (hne : ∃ i, relativeMass m i ≠ 1)
    (hRatio : ∀ i j, m i ≤ (7 * p / 2) * m j) :
    logRowMean p m < rootRow p m := by
  have hn₀ : 0 < n := by omega
  have hN : 0 < (n : ℝ) := Nat.cast_pos.mpr hn₀
  have hM := massTotal_pos hn₀ hm
  have hMean : 0 < meanMass m := div_pos hM hN
  have hp₀ : 0 < p := by linarith only [hp]
  have hRow : 0 < analyticRow p (n : ℝ) :=
    analyticRow_pos hp₀ (by have h : (2 : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn; linarith only [h])
  let K := meanMass m * analyticRow p (n : ℝ)
  have hK : 0 < K := mul_pos hMean hRow
  have hRootMoment : 0 < relativeRootMoment p m := by
    unfold relativeRootMoment
    exact div_pos (sum_pos (fun i _ => Real.rpow_pos_of_pos (div_pos (hm i) hMean) _)
      ⟨⟨0,hn₀⟩,mem_univ _⟩) hN
  have hRoot : rootRow p m = K * relativeRootMoment p m ^ (p + 1) :=
    rootRow_normalized hn₀ hp₀ hm
  have hRootPos : 0 < rootRow p m := by
    rw [hRoot]
    exact mul_pos hK (Real.rpow_pos_of_pos hRootMoment _)
  have hLogRoot : Real.log (rootRow p m) =
      Real.log K + (p + 1) * Real.log (relativeRootMoment p m) := by
    rw [hRoot,Real.log_mul hK.ne' (Real.rpow_pos_of_pos hRootMoment _).ne',Real.log_rpow hRootMoment]
  have hFinite := nativeMassEntropy_root_nonneg hn₀ hp hP hm hRatio
  have hNative := logRowMean_adapted_lt hn hp hP hm hne
  change Real.log (logRowMean p m) < Real.log K - nativeMassEntropy ((p - 2) / 2) m at hNative
  have hLog : Real.log (logRowMean p m) < Real.log (rootRow p m) := by
    rw [hLogRoot]
    linarith only [hFinite,hNative]
  have hLogRowPos : 0 < logRowMean p m := Real.exp_pos _
  exact (Real.log_lt_log_iff hLogRowPos hRootPos).mp hLog

end ACS12.NativeCells


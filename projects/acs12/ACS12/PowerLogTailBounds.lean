import ACS12.JointLogZ

/-! Directed complete logarithmic power tails from unit trapezoids. -/
namespace ACS12.GammaMeasure

open Set Filter MeasureTheory intervalIntegral
open scoped Topology

theorem powerLogTail_trapezoid {q : ℝ} (hq : 2 ≤ q) {m : ℕ} (hm : 5 ≤ m) :
    let x : ℝ := m
    let A := x ^ (-(q - 1)) * (Real.log x / (q - 1) + 1 / (q - 1) ^ 2) + (x ^ (-q) * Real.log x) / 2
    A ≤ powerLogTail q 1 m ∧
      powerLogTail q 1 m ≤ A - x ^ (-(q + 1)) * (1 - q * Real.log x) / 8 := by
  let a : ℝ := m
  let f (x : ℝ) := x ^ (-q) * Real.log x
  let D (x : ℝ) := x ^ (-(q + 1)) * (1 - q * Real.log x)
  let E (x : ℝ) := x ^ (-(q + 2)) * (q * (q + 1) * Real.log x - (2 * q + 1))
  let F (x : ℝ) := -(x ^ (-(q - 1)) * (Real.log x / (q - 1) + 1 / (q - 1) ^ 2))
  let A := -F a + f a / 2
  have ha : (5 : ℝ) ≤ a := by
    change (5 : ℝ) ≤ (m : ℝ)
    exact_mod_cast hm
  have ha₀ : 0 < a := (by norm_num : (0 : ℝ) < 5).trans_le ha
  have hq' : 1 < q := by linarith only [hq]
  have hq₁ := sub_pos.mpr hq'
  have hPow (x r : ℝ) (hx : 0 < x) :
      HasDerivAt (fun t : ℝ => t ^ r) (r * x ^ r / x) x := by
    convert Real.hasDerivAt_rpow_const (p := r) (Or.inl hx.ne') using 1
    rw [Real.rpow_sub_one hx.ne',mul_div_assoc]
  have hF (x : ℝ) (hx : 0 < x) : HasDerivAt F (f x) x := by
    have h := (hPow x (-(q - 1)) hx).mul
      (((Real.hasDerivAt_log hx.ne').div_const (q - 1)).add_const (1 / (q - 1) ^ 2))
    convert h.neg using 1
    dsimp only [f]
    rw [show -q = -(q - 1) - 1 by ring,Real.rpow_sub_one hx.ne']
    field_simp [hx.ne',hq₁.ne']
    ring
  have hf (x : ℝ) (hx : 0 < x) : HasDerivAt f (D x) x := by
    convert (hPow x (-q) hx).mul (Real.hasDerivAt_log hx.ne') using 1
    dsimp only [D]
    rw [show -(q + 1) = -q - 1 by ring,Real.rpow_sub_one hx.ne']
    ring
  have hD (x : ℝ) (hx : 0 < x) : HasDerivAt D (E x) x := by
    convert (hPow x (-(q + 1)) hx).mul
      (((Real.hasDerivAt_log hx.ne').const_mul q).const_sub 1) using 1
    dsimp only [E]
    rw [show -(q + 2) = -(q + 1) - 1 by ring,Real.rpow_sub_one hx.ne']
    ring
  have hE (x : ℝ) (hx : a ≤ x) : 0 ≤ E x := by
    have hx₀ := ha₀.trans_le hx
    have hx₄ : 4 ≤ x := (by norm_num : (4 : ℝ) ≤ 5).trans (ha.trans hx)
    have h₄ : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
      ring
    have hL : 1 ≤ Real.log x := by
      linarith only [Real.log_le_log (by norm_num : (0 : ℝ) < 4) hx₄,h₄,Real.log_two_gt_d9]
    have hA := mul_le_mul_of_nonneg_left hL (show 0 ≤ q * (q + 1) by positivity)
    have hB := mul_nonneg (show 0 ≤ q - 2 by linarith only [hq]) (show 0 ≤ q + 1 by positivity)
    exact mul_nonneg (Real.rpow_nonneg hx₀.le _) (by nlinarith only [hA,hB,hq])
  have hEC {c d : ℝ} (hc : a ≤ c) : ContinuousOn E (Icc c d) := by
    intro x hx
    have h : 0 < x := ha₀.trans_le (hc.trans hx.1)
    exact ((Real.continuousAt_rpow_const x _ (Or.inl h.ne')).mul
      ((((Real.continuousAt_log h.ne').const_mul (q * (q + 1))).sub_const (2 * q + 1)))).continuousWithinAt
  have hCell (k : ℕ) :
      0 ≤ trapezoidal_error f 1 (a + k) (a + (k + 1 : ℕ)) ∧
      trapezoidal_error f 1 (a + k) (a + (k + 1 : ℕ)) ≤
        (1 / 8) * ∫ x in (a + k : ℝ)..(a + (k + 1 : ℕ)), E x := by
    simp only [Nat.cast_add,Nat.cast_one,← add_assoc]
    let b : ℝ := a + k
    have hb : a ≤ b := le_add_of_nonneg_right (Nat.cast_nonneg k)
    have hb₀ := ha₀.trans_le hb
    have h₁ (x : ℝ) (hx : x ∈ Icc b (b + 1)) := hf x (hb₀.trans_le hx.1)
    have h₂ (x : ℝ) (hx : x ∈ Icc b (b + 1)) := hD x (hb₀.trans_le hx.1)
    have hC := hEC (d := b + 1) hb
    have hBE : b ≤ b + 1 := le_add_of_nonneg_right zero_le_one
    constructor
    · have h := ACS12.trapezoidalError_unit_ge h₁ h₂ hC
      have hZ : (∫ x in b..b + 1, max 0 (-E x)) = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => 0) (fun x hx => ?_),intervalIntegral.integral_zero]
        rw [uIcc_of_le hBE] at hx
        exact max_eq_left (neg_nonpos.mpr (hE x (hb.trans hx.1)))
      rwa [hZ,mul_zero] at h
    · have h := ACS12.trapezoidalError_unit_le h₁ h₂ hC
      have hZ : (∫ x in b..b + 1, max 0 (E x)) = ∫ x in b..b + 1, E x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hBE] at hx
        exact max_eq_right (hE x (hb.trans hx.1))
      rwa [hZ] at h
  let b (N : ℕ) : ℝ := a + ((N + 1 : ℕ) : ℝ)
  have hApprox (N : ℕ) :
      A + F (b N) - f (b N) / 2 ≤ ∑ j ∈ Finset.range (N + 1), f (a + j) ∧
      (∑ j ∈ Finset.range (N + 1), f (a + j)) ≤
        A + F (b N) - f (b N) / 2 + (D (b N) - D a) / 8 := by
    let M := N + 1
    have hM : 0 < M := Nat.succ_pos _
    have hb : a ≤ b N := le_add_of_nonneg_right (Nat.cast_nonneg M)
    have hFC : ContinuousOn f (Icc a (b N)) :=
      fun x hx => (hf x (ha₀.trans_le hx.1)).continuousAt.continuousWithinAt
    have hFI := hFC.intervalIntegrable_of_Icc (μ := volume) hb
    have hES (k : ℕ) : IntervalIntegrable E volume (a + k) (a + (k + 1 : ℕ)) := by
      apply (hEC (le_add_of_nonneg_right (Nat.cast_nonneg k))).intervalIntegrable_of_Icc
      exact add_le_add_right (Nat.cast_le.mpr (Nat.le_succ k)) _
    have hS := Finset.sum_le_sum (s := Finset.range M) (fun k _ => (hCell k).2)
    rw [← Finset.mul_sum,intervalIntegral.sum_integral_adjacent_intervals (a := fun k => a + (k : ℝ))
      (fun k _ => hES k),Nat.cast_zero,add_zero] at hS
    have hZ := Finset.sum_nonneg (s := Finset.range M) (fun k _ => (hCell k).1)
    have hTr := sum_trapezoidal_error_adjacent_intervals (f := f) (a := a) (h := 1)
      hM (by simpa only [mul_one] using hFI)
    simp only [mul_one] at hTr
    simp only [Nat.cast_add,Nat.cast_one] at hS hZ
    rw [hTr] at hS hZ
    change trapezoidal_error f M a (b N) ≤ (1 / 8) * (∫ x in a..b N, E x) at hS
    change 0 ≤ trapezoidal_error f M a (b N) at hZ
    have hIe := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hD x (ha₀.trans_le (by rw [uIcc_of_le hb] at hx; exact hx.1)))
      ((hEC le_rfl).intervalIntegrable_of_Icc hb)
    have hIf := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hF x (ha₀.trans_le (by rw [uIcc_of_le hb] at hx; exact hx.1))) hFI
    have hBM : (b N - a) / (M : ℝ) = 1 := by
      dsimp only [b,M]
      rw [add_sub_cancel_left,div_self (Nat.cast_ne_zero.mpr hM.ne')]
    have hTrE : trapezoidal_integral f M a (b N) =
        (f a + f (b N)) / 2 + ∑ j ∈ Finset.range N, f (a + (j + 1 : ℕ)) := by
      unfold trapezoidal_integral
      rw [hBM,one_mul,show M - 1 = N by omega]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_div_assoc,hBM,mul_one,Nat.cast_add,Nat.cast_one]
    have hSum : (∑ j ∈ Finset.range (N + 1), f (a + j)) =
        f a + ∑ j ∈ Finset.range N, f (a + (j + 1 : ℕ)) := by
      rw [Finset.sum_range_succ',Nat.cast_zero,add_zero,add_comm]
    rw [trapezoidal_error,hTrE,hIf,hIe] at hS
    rw [trapezoidal_error,hTrE,hIf] at hZ
    change -F a + f a / 2 + F (b N) - f (b N) / 2 ≤ _ ∧ _
    rw [hSum]
    constructor <;> dsimp only [A] <;> linarith only [hS,hZ]
  have hbT : Tendsto b atTop atTop := by
    apply tendsto_atTop_mono (f := fun N : ℕ => (N : ℝ))
    · intro N
      dsimp only [b]
      push_cast
      linarith only [ha]
    · exact tendsto_natCast_atTop_atTop
  have hfT : Tendsto f atTop (𝓝 0) := by simpa only [f,pow_one] using logPower_decay (by positivity : 0 < q) 1
  have hFT : Tendsto F atTop (𝓝 0) := by
    have h := (((logPower_decay hq₁ 1).div_const (q - 1)).add
      ((tendsto_rpow_neg_atTop hq₁).div_const ((q - 1) ^ 2))).neg
    simp only [zero_div,add_zero,neg_zero] at h
    apply h.congr'
    filter_upwards [] with x
    simp only [F,pow_one]
    ring
  have hDT : Tendsto D atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by positivity : 0 < q + 1)).sub
      ((logPower_decay (by positivity : 0 < q + 1) 1).const_mul q)
    simp only [mul_zero,sub_zero] at h
    apply h.congr'
    filter_upwards [] with x
    simp only [D,pow_one]
    ring
  have hLim : Tendsto (fun N : ℕ => ∑ j ∈ Finset.range (N + 1), f (a + j)) atTop
      (𝓝 (powerLogTail q 1 m)) := by
    simpa only [powerLogTail,a,f,pow_one,Function.comp_apply] using
      (powerLogTail_summable hq' 1 m (by omega)).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hL : Tendsto (fun N : ℕ => A + F (b N) - f (b N) / 2) atTop (𝓝 A) := by
    simpa only [add_zero,zero_div,sub_zero] using ((hFT.comp hbT).const_add A).sub ((hfT.comp hbT).div_const 2)
  have hU : Tendsto (fun N : ℕ => A + F (b N) - f (b N) / 2 + (D (b N) - D a) / 8) atTop
      (𝓝 (A - D a / 8)) := by
    simpa only [zero_add,zero_sub,neg_div,sub_eq_add_neg,Function.comp_apply] using hL.add (((hDT.comp hbT).sub_const (D a)).div_const 8)
  have hLower := le_of_tendsto_of_tendsto hL hLim (Eventually.of_forall fun N => (hApprox N).1)
  have hUpper := le_of_tendsto_of_tendsto hLim hU (Eventually.of_forall fun N => (hApprox N).2)
  simpa only [A,F,f,D,neg_neg,a] using And.intro hLower hUpper

end ACS12.GammaMeasure

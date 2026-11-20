import ACS12.NativeTranslatedSpectrum

/-! Exact complete Bose moments used by the order-two coefficient calibration. -/
namespace ACS12.NativeCells

open MeasureTheory Set GammaMeasure CenteredCircle.AllN

theorem completeBose_natMoment {r : ℕ} (hr : 0 < r) {d : ℝ} (hd : 0 < d) :
    (∫ s : ℝ in Ioi 0, s ^ r / (Real.exp (d * s) - 1)) =
      (r.factorial : ℝ) * powerTail ((r : ℝ) + 1) 1 / d ^ (r + 1) := by
  let f (x : ℝ) := x ^ r * (Real.exp (-x) / (1 - Real.exp (-x)))
  have hEq (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      s ^ r / (Real.exp (d * s) - 1) = (d ^ r)⁻¹ * f (d * s) := by
    have hD := mul_pos hd (show 0 < s from hs)
    have hDen := (expHead_den_pos hD).ne'
    have hDen' := (expTail_den_pos hD).ne'
    unfold f
    rw [mul_pow,Real.exp_neg]
    field_simp [hd.ne',hDen',Real.exp_ne_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi hEq,integral_const_mul,
    integral_comp_mul_left_Ioi f 0 hd,mul_zero,smul_eq_mul]
  have hE : (∫ s : ℝ in Ioi 0, f s) = (r.factorial : ℝ) * powerTail ((r : ℝ) + 1) 1 := by
    simpa only [f,Nat.cast_one,mul_one] using boseMoment_nat_integral hr (by decide : 0 < (1 : ℕ))
  rw [hE,pow_succ]
  field_simp [hd.ne']

theorem powerTail_six_eq : powerTail 6 1 = Real.pi ^ 6 / 945 := by
  have hZ : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 6) (Real.pi ^ 6 / 945) := by
    convert hasSum_zeta_nat (k := 3) (by decide) using 1
    have hB : bernoulli 6 = (1 / 42 : ℚ) := by decide +kernel
    norm_num [hB,Nat.factorial]
    <;> ring
  have h := hZ.tsum_eq
  have hE : (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 6) = fun n : ℕ => (n : ℝ) ^ (-6 : ℝ) := by
    funext n
    rw [Real.rpow_neg (Nat.cast_nonneg n),Real.rpow_ofNat,one_div]
  rw [hE] at h
  have hS := (Real.summable_nat_rpow (p := (-6 : ℝ))).mpr (by norm_num)
  have hT := hS.tsum_eq_zero_add
  simp only [Nat.cast_zero,Real.zero_rpow (by norm_num : (-6 : ℝ) ≠ 0),zero_add] at hT
  have hP : powerTail 6 1 = ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-6 : ℝ) := by
    simp only [powerTail,Nat.cast_one,Nat.cast_add,add_comm]
  rw [hP,← hT,h]

theorem baseBose_second_moment_value :
    (∫ x : ℝ in Ioi 0, baseBose x * x ^ 2) = 1 / 240 := by
  have h := completeBose_natMoment (r := 3) (by decide) (d := 2 * Real.pi) (by positivity)
  have hEq : (fun x : ℝ => baseBose x * x ^ 2) =
      (fun x : ℝ => x ^ (3 : ℕ) / (Real.exp (2 * Real.pi * x) - 1)) := by
    funext x
    unfold baseBose
    ring
  rw [hEq,h]
  norm_num [powerTail_four_eq]
  field_simp [Real.pi_ne_zero]
  <;> ring

theorem baseBose_fourth_moment_value :
    (∫ x : ℝ in Ioi 0, baseBose x * x ^ 4) = 1 / 504 := by
  have h := completeBose_natMoment (r := 5) (by decide) (d := 2 * Real.pi) (by positivity)
  have hEq : (fun x : ℝ => baseBose x * x ^ 4) =
      (fun x : ℝ => x ^ (5 : ℕ) / (Real.exp (2 * Real.pi * x) - 1)) := by
    funext x
    unfold baseBose
    ring
  rw [hEq,h]
  norm_num [powerTail_six_eq]
  field_simp [Real.pi_ne_zero]
  <;> ring

theorem baseBose_even_moments_integrable :
    IntegrableOn (fun x => baseBose x * x ^ 2) (Ioi 0) ∧
      IntegrableOn (fun x => baseBose x * x ^ 4) (Ioi 0) := by
  constructor
  · apply Integrable.of_integral_ne_zero
    rw [baseBose_second_moment_value]
    norm_num
  · apply Integrable.of_integral_ne_zero
    rw [baseBose_fourth_moment_value]
    norm_num

end ACS12.NativeCells


import ACS12.NativeBoseRow
import ACS12.PureNativeOneValue

/-! Exact Bose rows at the required pressure and native calibration endpoints. -/
namespace ACS12.NativeCells

open MeasureTheory Set
open GammaMeasure (gammaArgument gammaDensity powerTail)
open CenteredCircle.AllN

private theorem scaledBoseMoment {r : ℕ} (hr : 0 < r) {d : ℝ} (hd : 0 < d) :
    (∫ s : ℝ in Ioi 0, s ^ r / (Real.exp (d * s) - 1)) =
      (r.factorial : ℝ) * powerTail ((r : ℝ) + 1) 1 / d ^ (r + 1) := by
  let f (x : ℝ) := x ^ r * (Real.exp (-x) / (1 - Real.exp (-x)))
  have hEq (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      s ^ r / (Real.exp (d * s) - 1) = (d ^ r)⁻¹ * f (d * s) := by
    have hD := mul_pos hd (show 0 < s from hs)
    have hDen := (expHead_den_pos hD).ne'
    have hDen' := (expTail_den_pos hD).ne'
    dsimp only [f]
    rw [mul_pow,Real.exp_neg]
    field_simp [hd.ne',hDen',Real.exp_ne_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi hEq,integral_const_mul,
    integral_comp_mul_left_Ioi f 0 hd,mul_zero,smul_eq_mul]
  have hE : (∫ s : ℝ in Ioi 0, f s) = (r.factorial : ℝ) * powerTail ((r : ℝ) + 1) 1 := by
    simpa only [f,Nat.cast_one,mul_one] using GammaMeasure.boseMoment_nat_integral hr (by decide : 0 < (1 : ℕ))
  rw [hE,pow_succ]
  field_simp [hd.ne']

private theorem scaledBoseMoment_integrable {r : ℕ} (hr : 0 < r) {d : ℝ} (hd : 0 < d) :
    IntegrableOn (fun s => s ^ r / (Real.exp (d * s) - 1)) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [scaledBoseMoment hr hd]
  have hq : 1 < (r : ℝ) + 1 := by exact lt_add_of_pos_left _ (Nat.cast_pos.mpr hr)
  exact (div_pos (mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _))
    (GammaMeasure.powerTail_pos hq (by decide))) (pow_pos hd _)).ne'

private theorem powerTail_two_eq : powerTail 2 1 = Real.pi ^ 2 / 6 := by
  simpa only [GammaMeasure.pureZ,one_mul,show (1 : ℝ) + 1 = 2 by norm_num] using GammaMeasure.pureZ_one_eq

theorem powerTail_four_eq : powerTail 4 1 = Real.pi ^ 4 / 90 := by
  have h := hasSum_zeta_four.tsum_eq
  have hE : (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 4) = fun n : ℕ => (n : ℝ) ^ (-4 : ℝ) := by
    funext n
    rw [Real.rpow_neg (Nat.cast_nonneg n),Real.rpow_ofNat,one_div]
  rw [hE] at h
  have hS := (Real.summable_nat_rpow (p := (-4 : ℝ))).mpr (by norm_num)
  have hT := hS.tsum_eq_zero_add
  simp only [Nat.cast_zero,Real.zero_rpow (by norm_num : (-4 : ℝ) ≠ 0),zero_add] at hT
  have hP : powerTail 4 1 = (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-4 : ℝ)) := by
    simp only [powerTail,Nat.cast_one,Nat.cast_add,add_comm]
  rw [hP,← hT,h]

private theorem density_two_sinh {s : ℝ} (hs : 0 < s) :
    gammaDensity 2 s * Real.sinh (Real.pi * s) = 2 * s := by
  have h := GammaMeasure.imageDensity_two (L := 2 * Real.pi) (by positivity) hs
  rw [GammaMeasure.imageDensity_eq_spectral 2 (by positivity : 0 < 2 * Real.pi)] at h
  have hArg : 2 * Real.pi * s / (2 * Real.pi) = s := by field_simp [Real.pi_ne_zero]
  have hArg' : 2 * Real.pi * s / 2 = Real.pi * s := by ring
  rw [hArg,hArg'] at h
  have hEq : Real.pi / (2 * Real.pi) = 1 / 2 := by field_simp [Real.pi_ne_zero]
  rw [hEq] at h
  linarith only [h]

private theorem density_four_eq (s : ℝ) :
    gammaDensity 4 s = (2 / 3) * (1 + s ^ 2) * gammaDensity 2 s := by
  have hC : gammaArgument 2 s = gammaArgument 1 s + 1 := by
    unfold gammaArgument
    push_cast
    ring
  have hN : gammaArgument 1 s ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp at he
  have hNorm : ‖gammaArgument 1 s‖ ^ 2 = 1 + s ^ 2 := by
    have h := GammaMeasure.norm_gammaArgument_add 1 s 0
    norm_num at h
    exact h
  have hG : ‖Complex.Gamma (gammaArgument 2 s)‖ ^ 2 =
      (1 + s ^ 2) * ‖Complex.Gamma (gammaArgument 1 s)‖ ^ 2 := by
    rw [hC,Complex.Gamma_add_one _ hN,norm_mul,mul_pow,hNorm]
  have hArg₂ : ((2 / 2 : ℝ) : ℂ) + (s : ℂ) * Complex.I = gammaArgument 1 s := by norm_num [gammaArgument]
  have hArg₄ : ((4 / 2 : ℝ) : ℂ) + (s : ℂ) * Complex.I = gammaArgument 2 s := by norm_num [gammaArgument]
  unfold gammaDensity
  rw [hArg₂,hArg₄,hG]
  norm_num [Real.rpow_ofNat]
  ring

theorem boseRow_two_eq {N : ℝ} (hN : 0 < N) : boseRow 2 N = N ^ 2 / 3 := by
  let d := 2 * Real.pi / N
  have hd : 0 < d := by dsimp only [d]; positivity
  have hG := scaledBoseMoment (r := 1) (by decide) hd
  unfold boseRow
  have hE (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      2 * gammaDensity 2 s * (2 * Real.sinh (Real.pi * s) / (Real.exp (2 * Real.pi * s / N) - 1)) =
        8 * (s ^ (1 : ℕ) / (Real.exp (d * s) - 1)) := by
    have hArg : 2 * Real.pi * s / N = d * s := by dsimp only [d]; ring
    rw [hArg,pow_one]
    have h := density_two_sinh (show 0 < s from hs)
    linear_combination (4 / (Real.exp (d * s) - 1)) * h
  rw [setIntegral_congr_fun measurableSet_Ioi hE,integral_const_mul,hG]
  norm_num [powerTail_two_eq]
  dsimp only [d]
  field_simp [hN.ne',Real.pi_ne_zero]
  ring

theorem boseRow_four_eq {N : ℝ} (hN : 0 < N) : boseRow 4 N = (N ^ 4 + 10 * N ^ 2) / 45 := by
  let d := 2 * Real.pi / N
  have hd : 0 < d := by dsimp only [d]; positivity
  have hI₁ := scaledBoseMoment_integrable (r := 1) (by decide) hd
  have hI₃ := scaledBoseMoment_integrable (r := 3) (by decide) hd
  have hG₁ := scaledBoseMoment (r := 1) (by decide) hd
  have hG₃ := scaledBoseMoment (r := 3) (by decide) hd
  unfold boseRow
  have hE (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      2 * gammaDensity 4 s * (2 * Real.sinh (Real.pi * s) / (Real.exp (2 * Real.pi * s / N) - 1)) =
        (16 / 3) * (s ^ (1 : ℕ) / (Real.exp (d * s) - 1) + s ^ (3 : ℕ) / (Real.exp (d * s) - 1)) := by
    have hArg : 2 * Real.pi * s / N = d * s := by dsimp only [d]; ring
    rw [hArg,pow_one,density_four_eq]
    have h := density_two_sinh (show 0 < s from hs)
    linear_combination ((8 / 3) * (1 + s ^ 2) / (Real.exp (d * s) - 1)) * h
  rw [setIntegral_congr_fun measurableSet_Ioi hE,integral_const_mul,integral_add hI₁ hI₃,hG₁,hG₃]
  norm_num [powerTail_two_eq,powerTail_four_eq]
  dsimp only [d]
  field_simp [hN.ne',Real.pi_ne_zero]
  ring

theorem analyticRow_two_eq {N : ℝ} (hN : 1 < N) : analyticRow 2 N = (N ^ 2 - 1) / 3 := by
  rw [← boseRow_sub_self (by norm_num : (0 : ℝ) < 2) hN,boseRow_two_eq (zero_lt_one.trans hN),boseRow_two_eq zero_lt_one]
  ring

theorem analyticRow_four_eq {N : ℝ} (hN : 1 < N) : analyticRow 4 N = (N ^ 4 + 10 * N ^ 2 - 11) / 45 := by
  rw [← boseRow_sub_self (by norm_num : (0 : ℝ) < 4) hN,boseRow_four_eq (zero_lt_one.trans hN),boseRow_four_eq zero_lt_one]
  ring

end ACS12.NativeCells

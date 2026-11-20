import ACS12.BoseNoiseExponential

/-! Exact complete Bose moments from its existing exponential mixture.
The universal even-zeta formula is the finite Bernoulli coefficient account. -/
namespace ACS12.NativeCells
open MeasureTheory ProbabilityTheory Set Filter
open GammaMeasure (powerTail)
set_option backward.isDefEq.respectTransparency false

noncomputable def scaledBoseNoise (s : BoseNoiseSample) : ℝ := 60*boseNoise s
noncomputable def scaledBoseMoment (k : ℕ) : ℝ :=
  ∫ s, (scaledBoseNoise s)^k ∂boseNoiseMeasure

theorem scaledBoseNoise_measurable : Measurable scaledBoseNoise :=
  measurable_boseNoise.const_mul 60

theorem scaledBoseNoise_ae_pos : ∀ᵐ s ∂boseNoiseMeasure, 0 < scaledBoseNoise s :=
  boseNoise_ae_pos.mono (fun _ hs => mul_pos (by norm_num) hs)

theorem scaledBoseNoise_pow_integrable (k : ℕ) :
    Integrable (fun s => (scaledBoseNoise s)^k) boseNoiseMeasure := by
  have h := (boseNoise_power_integrable (show (0:ℝ)≤(k:ℝ) by positivity)).const_mul ((60:ℝ)^k)
  simpa only [scaledBoseNoise,mul_pow,Real.rpow_natCast] using h

theorem scaledBoseMoment_formula (k : ℕ) :
    scaledBoseMoment k = (k.factorial:ℝ)*(15/Real.pi^2)^k*
      powerTail (2+2*(k:ℝ)) 1/powerTail 2 1 := by
  let ν := nativeZetaMeasure 2
  let γ := gammaMeasure 1 1
  letI := nativeZeta_probability (by norm_num : (1:ℝ)<2)
  letI := isProbabilityMeasure_gammaMeasure zero_lt_one zero_lt_one
  have hG := gammaUnit_power (q:=1) (r:=(k:ℝ)) zero_lt_one (by positivity)
  have hSlice (j : ℕ) :
      (∫ e, (scaledBoseNoise (j,e))^k ∂γ) =
        (k.factorial:ℝ)*(15/Real.pi^2)^k*(1+(j:ℝ))^(-(2*(k:ℝ))) := by
    have hR := GammaMixture.gammaRate_pos j
    have hE : (fun e => (scaledBoseNoise (j,e))^k) =
        (fun e : ℝ => ((60:ℝ)/GammaMixture.gammaRate j)^k*e^k) := by
      funext e
      unfold scaledBoseNoise boseNoise
      rw [←mul_pow]
      congr 1
      ring
    rw [hE,integral_const_mul]
    have hGamma : (∫ e, e^k ∂γ) = (k.factorial:ℝ) := by
      simpa only [γ,Real.rpow_natCast,Real.Gamma_one,div_one,
        add_comm (1:ℝ) (k:ℝ),Real.Gamma_nat_eq_factorial] using hG.2
    rw [hGamma,Real.rpow_neg (by positivity : (0:ℝ)≤1+(j:ℝ)),
      show 2*(k:ℝ)=((2*k:ℕ):ℝ) by push_cast; ring,Real.rpow_natCast]
    have hBase : (60:ℝ)/GammaMixture.gammaRate j = (15/Real.pi^2)/(1+(j:ℝ))^2 := by
      unfold GammaMixture.gammaRate
      field_simp [Real.pi_ne_zero,show (1+(j:ℝ))≠0 by positivity,
        show ((j:ℝ)+1)≠0 by positivity]
      <;> ring
    rw [hBase,div_pow,pow_mul]
    ring
  have hJ := nativeZeta_power (p:=2) (r:=-(2*(k:ℝ))) (by norm_num)
    (by have h := Nat.cast_nonneg (α:=ℝ) k; linarith : (1:ℝ)<2- -(2*(k:ℝ)))
  rw [show 2- -(2*(k:ℝ))=2+2*(k:ℝ) by ring] at hJ
  change (∫ s, (scaledBoseNoise s)^k ∂ν.prod γ) = _
  rw [integral_prod _ (scaledBoseNoise_pow_integrable k)]
  rw [show (fun x : ℕ => ∫ e, scaledBoseNoise (x,e)^k ∂γ) =
    (fun x : ℕ => (k.factorial:ℝ)*(15/Real.pi^2)^k*(1+(x:ℝ))^(-(2*(k:ℝ)))) by
      funext x; exact hSlice x]
  rw [integral_const_mul]
  change _*(∫ x, (1+(x:ℝ))^(-(2*(k:ℝ))) ∂nativeZetaMeasure 2) = _
  rw [hJ.2]
  ring

theorem powerTail_even_bernoulli {k : ℕ} (hk : k ≠ 0) :
    powerTail (2*(k:ℝ)) 1 =
      (-1:ℝ)^(k+1)*2^(2*k-1)*Real.pi^(2*k)*(bernoulli (2*k):ℚ)/(2*k).factorial := by
  have h := hasSum_zeta_nat hk
  have hPow : (fun n : ℕ => 1/(n:ℝ)^(2*k)) =
      (fun n : ℕ => (n:ℝ)^(-(2*(k:ℝ)))) := by
    funext n
    rw [Real.rpow_neg (Nat.cast_nonneg n),
      show 2*(k:ℝ)=((2*k:ℕ):ℝ) by push_cast; ring,Real.rpow_natCast,one_div]
  rw [hPow] at h
  have hs := h.summable.tsum_eq_zero_add
  have hkR : (0:ℝ)<(k:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  simp only [Nat.cast_zero,Real.zero_rpow (by linarith : -(2*(k:ℝ))≠0),zero_add] at hs
  have hp : powerTail (2*(k:ℝ)) 1 =
      ∑' n : ℕ, ((n+1:ℕ):ℝ)^(-(2*(k:ℝ))) := by
    simp only [powerTail,Nat.cast_one,Nat.cast_add,add_comm]
  rw [hp,←hs,h.tsum_eq]

end ACS12.NativeCells

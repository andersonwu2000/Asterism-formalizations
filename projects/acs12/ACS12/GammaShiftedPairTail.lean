import ACS12.OrdinaryGammaTail

/-! Compact imaginary shifts retain the exact exponential Gamma-pair cancellation. -/
namespace ACS12.GammaMeasure
open Set
set_option backward.isDefEq.respectTransparency false

theorem gamma_pair_compact_tail {a b T : ℝ} (ha : 0 < a) (hT : 0 ≤ T) :
    ∃ C > 0, ∃ k : ℕ, ∀ s ∈ Icc a b, ∀ v : ℝ, |v| ≤ T →
      ∀ ξ : ℝ, T+1 ≤ ξ →
      ‖Complex.Gamma (gammaArgument s (v+ξ)) * Complex.Gamma (gammaArgument s (v-ξ))‖ ≤
        C*(1+ξ)^k*Real.exp (-Real.pi*ξ) := by
  obtain ⟨B,hB,k,hTail⟩ := gamma_compact_shape_tail (b:=b) ha
  refine ⟨B^2*(1+T)^(2*k),by positivity,2*k,?_⟩
  intro s hs v hv ξ hξ
  have hv₂ : v ≤ T := (le_abs_self v).trans hv
  have hv₁' : -T ≤ v := by have h := (abs_le.mp hv).1; exact h
  have hξ₀ : 0 ≤ ξ := by linarith
  have hp : 1 ≤ v+ξ := by linarith only [hv₁',hξ]
  have hm : v-ξ ≤ -1 := by linarith only [hv₂,hξ]
  have habsPlus : |v+ξ| = v+ξ := abs_of_nonneg (by linarith only [hp])
  have habsMinus : |v-ξ| = ξ-v := by rw [abs_of_nonpos (by linarith only [hm])]; ring
  have hOne : 0 ≤ 1+ξ := by positivity
  have hPow (w : ℝ) (hw : w ≤ ξ+T) (hw₀ : 0 ≤ 1+w) :
      (1+w)^k ≤ ((1+T)*(1+ξ))^k := by
    apply pow_le_pow_left₀ hw₀
    nlinarith [mul_nonneg hT hξ₀]
  have hP := hPow (v+ξ) (by linarith only [hv₂]) (by linarith only [hp])
  have hM := hPow (ξ-v) (by linarith only [hv₁']) (by linarith only [hm])
  have hPlus := hTail s hs (v+ξ) (by rwa [habsPlus])
  have hMinus := hTail s hs (v-ξ) (by rw [habsMinus]; linarith only [hm])
  rw [habsPlus] at hPlus
  rw [habsMinus] at hMinus
  rw [norm_mul]
  calc
    _ ≤ (B*((1+T)*(1+ξ))^k*Real.exp (-Real.pi*(v+ξ)/2)) *
        (B*((1+T)*(1+ξ))^k*Real.exp (-Real.pi*(ξ-v)/2)) :=
      mul_le_mul (hPlus.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hP hB.le) (Real.exp_pos _).le))
        (hMinus.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hM hB.le) (Real.exp_pos _).le))
        (norm_nonneg _) (by positivity)
    _ = _ := by
      have he : Real.exp (-Real.pi*(v+ξ)/2)*Real.exp (-Real.pi*(ξ-v)/2) =
          Real.exp (-Real.pi*ξ) := by
        rw [←Real.exp_add]
        congr 1
        ring
      calc
        _ = B^2*(((1+T)*(1+ξ))^k)^2*
          (Real.exp (-Real.pi*(v+ξ)/2)*Real.exp (-Real.pi*(ξ-v)/2)) := by ring
        _ = _ := by rw [he,←pow_mul,mul_pow]; ring

end ACS12.GammaMeasure

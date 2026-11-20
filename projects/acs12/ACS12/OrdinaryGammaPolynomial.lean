import ACS12.OrdinaryGammaOrder
import ACS12.GammaUnitReflection

/-! Ordinary beta order plus the literal finite integer Gamma recurrence. -/
namespace ACS12.GammaMeasure
set_option backward.isDefEq.respectTransparency false

theorem gammaArgument_norm_le (s t : ℝ) (hs : 0 ≤ s) :
    ‖gammaArgument s t‖ ≤ s + |t| := by
  calc
    _ ≤ ‖(s:ℂ)‖ + ‖(t:ℂ)*Complex.I‖ := norm_add_le _ _
    _ = s + |t| := by simp [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs]

theorem gammaUnit_norm_even (t : ℝ) :
    ‖Complex.Gamma (gammaArgument 1 (-t))‖ = ‖Complex.Gamma (gammaArgument 1 t)‖ := by
  have h : gammaArgument 1 (-t) = star (gammaArgument 1 t) := by
    simp [gammaArgument,Complex.conj_I]
  rw [h,Complex.star_def,Complex.Gamma_conj]
  exact Complex.norm_conj _

theorem gammaUnit_norm_abs (t : ℝ) :
    ‖Complex.Gamma (gammaArgument 1 |t|)‖ = ‖Complex.Gamma (gammaArgument 1 t)‖ := by
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h,gammaUnit_norm_even]

theorem gamma_integer_norm_le (k : ℕ) (t : ℝ) :
    ‖Complex.Gamma (gammaArgument (k+1:ℕ) t)‖ ≤
      Real.Gamma (k+1:ℕ) * (1+|t|)^k * ‖Complex.Gamma (gammaArgument 1 t)‖ := by
  induction k with
  | zero => simp [gammaArgument]
  | succ k ih =>
    have hk : 0 < (k+1:ℕ) := by omega
    have hkR : 0 < ((k+1:ℕ):ℝ) := by exact_mod_cast hk
    have hz : gammaArgument (k+1:ℕ) t ≠ 0 := by
      intro h
      have hh := congrArg Complex.re h
      simp only [gammaArgument_re,Complex.zero_re] at hh
      linarith
    have harg : gammaArgument (k+1+1:ℕ) t = gammaArgument (k+1:ℕ) t + 1 := by
      simp only [gammaArgument,Nat.cast_add,Nat.cast_one,Complex.ofReal_add,Complex.ofReal_one]
      ring
    have hΓ : Real.Gamma (k+1+1:ℕ) = (k+1:ℕ)*Real.Gamma (k+1:ℕ) := by
      rw [show ((k+1+1:ℕ):ℝ) = (k+1:ℕ)+1 by push_cast; ring]
      exact Real.Gamma_add_one hkR.ne'
    have hn : ‖gammaArgument (k+1:ℕ) t‖ ≤ (k+1:ℕ)*(1+|t|) := by
      have h := gammaArgument_norm_le (k+1:ℕ) t hkR.le
      have hOne : (1:ℝ) ≤ (k+1:ℕ) := by exact_mod_cast (by omega : 1 ≤ k+1)
      have habs := abs_nonneg t
      nlinarith
    rw [harg,Complex.Gamma_add_one _ hz,norm_mul,hΓ,pow_succ]
    calc
      _ ≤ ((k+1:ℕ)*(1+|t|)) *
          (Real.Gamma (k+1:ℕ)*(1+|t|)^k*‖Complex.Gamma (gammaArgument 1 t)‖) :=
        mul_le_mul hn ih (norm_nonneg _) (by positivity)
      _ = _ := by ring

theorem gamma_shape_integer_bound {s t : ℝ} (hs : 0 < s) (k : ℕ)
    (hsk : s ≤ (k+1:ℕ)) :
    ‖Complex.Gamma (gammaArgument s t)‖ ≤
      Real.Gamma s * (1+|t|)^k * ‖Complex.Gamma (gammaArgument 1 t)‖ := by
  have hG : 0 < Real.Gamma (k+1:ℕ) := Real.Gamma_pos_of_pos (by positivity)
  have hS := ACS12.normalizedGammaModulus_mono (ξ:=t) hs hsk
  change ‖Complex.Gamma (gammaArgument s t)‖/Real.Gamma s ≤
    ‖Complex.Gamma (gammaArgument (k+1:ℕ) t)‖/Real.Gamma (k+1:ℕ) at hS
  have hI : ‖Complex.Gamma (gammaArgument (k+1:ℕ) t)‖/Real.Gamma (k+1:ℕ) ≤
      (1+|t|)^k*‖Complex.Gamma (gammaArgument 1 t)‖ := by
    apply (div_le_iff₀ hG).mpr
    nlinarith only [gamma_integer_norm_le k t]
  have h := hS.trans hI
  have hp := (div_le_iff₀ (Real.Gamma_pos_of_pos hs)).mp h
  nlinarith only [hp]

end ACS12.GammaMeasure


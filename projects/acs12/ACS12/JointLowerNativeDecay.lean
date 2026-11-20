import ACS12.JointLowerNativeMotion

/-! The full native atom cancellation retains a power of tail decay under motion. -/
namespace ACS12.GammaMeasure

open Set

theorem weightedAffineResponse_base_deriv {k : ℕ} (hk : k ≤ 3) (A B C D a b q d : ℝ)
    (hx : 0 < a - b * d) :
    HasDerivAt (fun y => weightedAffineResponse k A B C D y b q d)
      (-q * weightedAffineResponse k A B C D a b (q + 1) d) a := by
  let P₀ := A + B * d + C * d ^ 2 + D * d ^ 3
  let P₁ := B + 2 * C * d + 3 * D * d ^ 2
  let P₂ := 2 * C + 6 * D * d
  let P₃ := 6 * D
  have hX (r : ℝ) : HasDerivAt (fun y => (y - b * d) ^ r) (r * (a - b * d) ^ (r - 1)) a := by
    simpa only [id_eq,one_mul] using
      (((hasDerivAt_id a).sub_const (b * d)).rpow_const (p := r) (Or.inl hx.ne'))
  have h₀ := hX (-q)
  have h₁ := hX (-q - 1)
  have h₂ := hX (-q - 2)
  have h₃ := hX (-q - 3)
  interval_cases k
  · convert h₀.const_mul P₀ using 1
    simp only [weightedAffineResponse_zero,P₀,show -(q + 1) = -q - 1 by ring]
    ring
  · convert ((h₀.const_mul P₁).add (h₁.const_mul (P₀ * (b * q)))) using 1
    change -q * (P₁ * (a - b * d) ^ (-(q + 1)) +
      P₀ * (b * (q + 1)) * (a - b * d) ^ (-(q + 1) - 1)) = _
    simp only [show -(q + 1) = -q - 1 by ring]
    ring
  · convert (((h₀.const_mul P₂).add (h₁.const_mul (2 * P₁ * (b * q)))).add
      (h₂.const_mul (P₀ * (b ^ 2 * q * (q + 1))))) using 1
    change -q * (P₂ * (a - b * d) ^ (-(q + 1)) +
      2 * P₁ * (b * (q + 1)) * (a - b * d) ^ (-(q + 1) - 1) +
      P₀ * (b ^ 2 * (q + 1) * (q + 1 + 1)) * (a - b * d) ^ (-(q + 1) - 2)) = _
    simp only [show -(q + 1) = -q - 1 by ring,show -q - 1 - 1 = -q - 2 by ring,
      show -q - 1 - 2 = -q - 2 - 1 by ring]
    ring
  · convert ((((h₀.const_mul P₃).add (h₁.const_mul (3 * P₂ * (b * q)))).add
      (h₂.const_mul (3 * P₁ * (b ^ 2 * q * (q + 1))))).add
      (h₃.const_mul (P₀ * (b ^ 3 * q * (q + 1) * (q + 2))))) using 1
    simp only [weightedAffineResponse_third,P₀,P₁,P₂,P₃,show -(q + 1) = -q - 1 by ring,
      show -q - 1 - 1 = -q - 2 by ring,show -q - 1 - 2 = -q - 3 by ring,
      show -q - 1 - 3 = -q - 3 - 1 by ring,show -q - 2 - 1 = -q - 3 by ring]
    ring

theorem weightedAffineResponse_scaled {k : ℕ} (hk : k ≤ 3) (A B C D a b q d : ℝ)
    (hx : 0 < a - b * d) :
    weightedAffineResponse k A B C D a b q d =
      weightedAffineResponse k A B C D (1 + b / (a - b * d) * d)
        (b / (a - b * d)) q d * (a - b * d) ^ (-q) := by
  let x := a - b * d
  have hx₀ : 0 < x := hx
  have hX : 1 + b / x * d - b / x * d = 1 := by ring
  interval_cases k
  · simp only [weightedAffineResponse_zero]
    rw [show a - b * d = x from rfl,hX,Real.one_rpow,mul_one]
  · unfold weightedAffineResponse
    dsimp only
    rw [show a - b * d = x from rfl,hX,Real.one_rpow,Real.one_rpow,Real.rpow_sub_one hx₀.ne']
    field_simp [hx₀.ne']
  · unfold weightedAffineResponse
    dsimp only
    rw [show a - b * d = x from rfl,hX,Real.one_rpow,Real.one_rpow,Real.one_rpow,
      Real.rpow_sub_one hx₀.ne',Real.rpow_sub hx₀ (-q) 2,Real.rpow_two]
    field_simp [hx₀.ne']
  · unfold weightedAffineResponse
    dsimp only
    rw [show a - b * d = x from rfl,hX,Real.one_rpow,Real.one_rpow,Real.one_rpow,Real.one_rpow,
      Real.rpow_sub_one hx₀.ne',Real.rpow_sub hx₀ (-q) 2,Real.rpow_two,Real.rpow_sub hx₀ (-q) 3,
      show (3 : ℝ) = (3 : ℕ) by norm_num,Real.rpow_natCast]
    field_simp [hx₀.ne']

end ACS12.GammaMeasure

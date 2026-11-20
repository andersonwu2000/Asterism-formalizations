import ACS12.JointLowerSourceThird

/-! Ordinary derivatives of polynomial-weighted affine powers along the lower diagonal. -/
namespace ACS12.GammaMeasure

open Set

private noncomputable def cubicResponse (k : ℕ) (A B C D d : ℝ) : ℝ :=
  match k with
  | 0 => A + B * d + C * d ^ 2 + D * d ^ 3
  | 1 => B + 2 * C * d + 3 * D * d ^ 2
  | 2 => 2 * C + 6 * D * d
  | _ => 6 * D

private theorem cubicResponse_deriv {k : ℕ} (hk : k < 3) (A B C D d : ℝ) :
    HasDerivAt (cubicResponse k A B C D) (cubicResponse (k + 1) A B C D d) d := by
  have h := hasDerivAt_id d
  interval_cases k
  · convert (((h.const_mul B).const_add A).add ((h.pow 2).const_mul C)).add ((h.pow 3).const_mul D) using 1
    norm_num [cubicResponse,id_eq] <;> ring
  · convert (((h.const_mul (2 * C)).const_add B).add ((h.pow 2).const_mul (3 * D))) using 1
    norm_num [cubicResponse,id_eq] <;> ring
  · convert (h.const_mul (6 * D)).const_add (2 * C) using 1
    simp only [cubicResponse,mul_one]

private theorem affineNegativePower_deriv (a b q d : ℝ) (hx : 0 < a - b * d) :
    HasDerivAt (fun δ => (a - b * δ) ^ (-q)) (b * q * (a - b * d) ^ (-q - 1)) d := by
  convert (((hasDerivAt_id d).const_mul b).const_sub a).rpow_const (p := -q) (Or.inl hx.ne') using 1
  simp only [id_eq,mul_one]
  ring

noncomputable def weightedAffineResponse (k : ℕ) (A B C D a b q d : ℝ) : ℝ :=
  let x := a - b * d
  let P (i : ℕ) := cubicResponse i A B C D d
  match k with
  | 0 => P 0 * x ^ (-q)
  | 1 => P 1 * x ^ (-q) + P 0 * (b * q) * x ^ (-q - 1)
  | 2 => P 2 * x ^ (-q) + 2 * P 1 * (b * q) * x ^ (-q - 1) +
      P 0 * (b ^ 2 * q * (q + 1)) * x ^ (-q - 2)
  | _ => P 3 * x ^ (-q) + 3 * P 2 * (b * q) * x ^ (-q - 1) +
      3 * P 1 * (b ^ 2 * q * (q + 1)) * x ^ (-q - 2) +
      P 0 * (b ^ 3 * q * (q + 1) * (q + 2)) * x ^ (-q - 3)

theorem weightedAffineResponse_deriv {k : ℕ} (hk : k < 3) (A B C D a b q d : ℝ)
    (hx : 0 < a - b * d) :
    HasDerivAt (weightedAffineResponse k A B C D a b q) (weightedAffineResponse (k + 1) A B C D a b q d) d := by
  have hP (i : ℕ) (hi : i < 3) := cubicResponse_deriv hi A B C D d
  have hX (r : ℝ) := affineNegativePower_deriv a b r d hx
  have hX₁ := hX (q + 1)
  have hX₂ := hX (q + 2)
  simp only [neg_add_rev,show -(1 : ℝ) + -q = -q - 1 by ring,show -(2 : ℝ) + -q = -q - 2 by ring,
    show -q - 1 - 1 = -q - 2 by ring,show -q - 2 - 1 = -q - 3 by ring] at hX₁ hX₂
  interval_cases k
  · convert (hP 0 (by decide)).mul (hX q) using 1
    unfold weightedAffineResponse
    ring
  · have h₀ := (hP 1 (by decide)).mul (hX q)
    have h₁ := ((hP 0 (by decide)).mul_const (b * q)).mul hX₁
    convert h₀.add h₁ using 1
    unfold weightedAffineResponse
    ring
  · have h₀ := (hP 2 (by decide)).mul (hX q)
    have h₁ := ((hP 1 (by decide)).const_mul 2 |>.mul_const (b * q)).mul hX₁
    have h₂ := ((hP 0 (by decide)).mul_const (b ^ 2 * q * (q + 1))).mul hX₂
    convert (h₀.add h₁).add h₂ using 1
    unfold weightedAffineResponse
    ring

theorem weightedAffineResponse_zero (A B C D a b q d : ℝ) :
    weightedAffineResponse 0 A B C D a b q d = (A + B * d + C * d ^ 2 + D * d ^ 3) * (a - b * d) ^ (-q) := rfl

theorem weightedAffineResponse_first (A B C D a b q d : ℝ) :
    weightedAffineResponse 1 A B C D a b q d =
      (B + 2 * C * d + 3 * D * d ^ 2) * (a - b * d) ^ (-q) +
        (A + B * d + C * d ^ 2 + D * d ^ 3) * (b * q) * (a - b * d) ^ (-q - 1) :=
  rfl

theorem weightedAffineResponse_second (A B C D a b q d : ℝ) :
    weightedAffineResponse 2 A B C D a b q d =
      (2 * C + 6 * D * d) * (a - b * d) ^ (-q) +
        2 * (B + 2 * C * d + 3 * D * d ^ 2) * (b * q) * (a - b * d) ^ (-q - 1) +
        (A + B * d + C * d ^ 2 + D * d ^ 3) * (b ^ 2 * q * (q + 1)) * (a - b * d) ^ (-q - 2) :=
  rfl

theorem weightedAffineResponse_third (A B C D a b q d : ℝ) :
    weightedAffineResponse 3 A B C D a b q d =
      6 * D * (a - b * d) ^ (-q) + 3 * (2 * C + 6 * D * d) * (b * q) * (a - b * d) ^ (-q - 1) +
        3 * (B + 2 * C * d + 3 * D * d ^ 2) * (b ^ 2 * q * (q + 1)) * (a - b * d) ^ (-q - 2) +
        (A + B * d + C * d ^ 2 + D * d ^ 3) * (b ^ 3 * q * (q + 1) * (q + 2)) * (a - b * d) ^ (-q - 3) :=
  rfl

noncomputable def lowerNativeSite (k : ℕ) (p j d : ℝ) : ℝ :=
  let a := 1 + j
  let b := 1 + 2 * j
  weightedAffineResponse k (19 / 25 * p) (-(63 / 25) * p) (56 / 25 * p) (-(12 / 25) * p) a b (p + 1) d
    - weightedAffineResponse k 1 (-2) 0 0 a b p d
    + weightedAffineResponse k (6 / 25 * p) (-(12 / 25) * p) (-(6 / 25) * p) (12 / 25 * p) (a + 1) b (p + 1) d
    + weightedAffineResponse k 1 (-2) 0 0 (a + 1) b p d

theorem lowerNativeSite_deriv {k : ℕ} (hk : k < 3) {p j d : ℝ}
    (hj : 0 ≤ j) (hd : d < 1 / 2) :
    HasDerivAt (lowerNativeSite k p j) (lowerNativeSite (k + 1) p j d) d := by
  have h : 0 < 1 + j - (1 + 2 * j) * d := by
    nlinarith only [hd,mul_nonneg hj (show 0 ≤ 1 - 2 * d by linarith only [hd])]
  have h' : 0 < 1 + j + 1 - (1 + 2 * j) * d := by linarith only [h]
  exact (((weightedAffineResponse_deriv hk _ _ _ _ _ _ _ _ h).sub
    (weightedAffineResponse_deriv hk _ _ _ _ _ _ _ _ h)).add
    (weightedAffineResponse_deriv hk _ _ _ _ _ _ _ _ h')).add
    (weightedAffineResponse_deriv hk _ _ _ _ _ _ _ _ h')

theorem lowerNativeSite_zero {p j d : ℝ} :
    lowerNativeSite 0 p j d =
      lowerDiagonalMass d * pureRight p (1 - d) (1 - d + j * lowerDiagonalMass d) := by
  unfold lowerNativeSite
  dsimp only
  simp only [weightedAffineResponse_zero,lowerDiagonalMass,pureRight,middleA,middleZ]
  rw [show 1 + j - (1 + 2 * j) * d = 1 - d + j * (1 - 2 * d) by ring,
    show 1 + j + 1 - (1 + 2 * j) * d = 1 - d + j * (1 - 2 * d) + 1 by ring]
  ring

end ACS12.GammaMeasure

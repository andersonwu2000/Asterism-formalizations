import ACS12.JointLowerNativeMotion

/-! Exact two literal site numerators in the retained central price. -/
namespace ACS12.GammaMeasure

noncomputable def lowerNativeAlpha (p : ℝ) : ℝ := (12 / 25) * p * (p - 1) * (2 - p) / (p + 1)

theorem lowerNativeAlpha_bounds {p : ℝ} (hp : 1 ≤ p) (hpP : p ≤ 9 / 5) :
    0 ≤ lowerNativeAlpha p ∧ lowerNativeAlpha p ≤ 3 / 40 := by
  have hp₀ := zero_lt_one.trans_le hp
  have hp₁ : 0 ≤ p - 1 := sub_nonneg.mpr hp
  have hp₂ : 0 ≤ 2 - p := by linarith only [hpP]
  constructor
  · unfold lowerNativeAlpha
    positivity
  · unfold lowerNativeAlpha
    apply (div_le_iff₀ (by positivity : 0 < p + 1)).mpr
    let t := p - 1
    have ht : 0 ≤ t := hp₁
    have h₁ := mul_nonneg ht (sq_nonneg (t - 1 / 2))
    have h₂ := sq_nonneg (t - 1 / 2 - 3 / 64)
    have h : 0 ≤ 32 * t ^ 3 - 27 * t + 10 := by nlinarith only [h₁,h₂]
    unfold t at h
    nlinarith only [h]

private theorem weightedAffineResponse_third_factor (A B C D a b q d : ℝ) (hx : 0 < a - b * d) :
    let x := a - b * d
    weightedAffineResponse 3 A B C D a b q d =
      x ^ (-q - 3) * (6 * D * x ^ 3 + 3 * (2 * C + 6 * D * d) * (b * q) * x ^ 2 +
        3 * (B + 2 * C * d + 3 * D * d ^ 2) * (b ^ 2 * q * (q + 1)) * x +
        (A + B * d + C * d ^ 2 + D * d ^ 3) * (b ^ 3 * q * (q + 1) * (q + 2))) := by
  let x := a - b * d
  change _ = x ^ (-q - 3) * _
  have h (k : ℕ) : x ^ (-q - 3 + (k : ℝ)) = x ^ (-q - 3) * x ^ k := by
    rw [Real.rpow_add hx,Real.rpow_natCast]
  have h₃ : x ^ (-q) = x ^ (-q - 3) * x ^ 3 := by
    convert h 3 using 2
    push_cast
    ring
  have h₂ : x ^ (-q - 1) = x ^ (-q - 3) * x ^ 2 := by
    convert h 2 using 2
    push_cast
    ring
  have h₁ : x ^ (-q - 2) = x ^ (-q - 3) * x := by
    rw [← pow_one x]
    convert h 1 using 2 <;> push_cast <;> ring
  rw [weightedAffineResponse_third,h₃,h₂,h₁]
  ring

private theorem nativeHead_factor (p j d : ℝ) (hd : d < 1 / 2) (hj : 0 ≤ j) :
    let a := 1 + j
    let b := 1 + 2 * j
    let x := a - b * d
    let y := a + 1 - b * d
    let P₀ := (19 / 25 - (63 / 25) * d + (56 / 25) * d ^ 2 - (12 / 25) * d ^ 3) * p
    let P₁ := (-(63 / 25) + 2 * (56 / 25) * d - 3 * (12 / 25) * d ^ 2) * p
    let P₂ := (2 * (56 / 25) - 6 * (12 / 25) * d) * p
    let Q₀ := (6 / 25 - (12 / 25) * d - (6 / 25) * d ^ 2 + (12 / 25) * d ^ 3) * p
    let Q₁ := (-(12 / 25) - 2 * (6 / 25) * d + 3 * (12 / 25) * d ^ 2) * p
    let Q₂ := (-(12 / 25) + 6 * (12 / 25) * d) * p
    lowerNativeSite 3 p j d =
      x ^ (-p - 4) * (-(72 / 25) * p * x ^ 3 + 3 * P₂ * b * (p + 1) * x ^ 2 +
        3 * P₁ * b ^ 2 * (p + 1) * (p + 2) * x + P₀ * b ^ 3 * (p + 1) * (p + 2) * (p + 3) +
        6 * b ^ 2 * p * (p + 1) * x ^ 2 - (1 - 2 * d) * b ^ 3 * p * (p + 1) * (p + 2) * x) +
      y ^ (-p - 4) * ((72 / 25) * p * y ^ 3 + 3 * Q₂ * b * (p + 1) * y ^ 2 +
        3 * Q₁ * b ^ 2 * (p + 1) * (p + 2) * y + Q₀ * b ^ 3 * (p + 1) * (p + 2) * (p + 3) -
        6 * b ^ 2 * p * (p + 1) * y ^ 2 + (1 - 2 * d) * b ^ 3 * p * (p + 1) * (p + 2) * y) := by
  let a := 1 + j
  let b := 1 + 2 * j
  have hx : 0 < a - b * d := by
    unfold a b
    nlinarith only [hd,mul_nonneg hj (show 0 ≤ 1 - 2 * d by linarith only [hd])]
  have hy : 0 < a + 1 - b * d := by linarith only [hx]
  have hE (x : ℝ) (h : 0 < x) : x ^ (-p - 3) = x ^ (-p - 4) * x := by
    rw [← Real.rpow_add_one h.ne',show -p - 4 + 1 = -p - 3 by ring]
  change weightedAffineResponse 3 _ _ _ _ a b (p + 1) d -
    weightedAffineResponse 3 _ _ _ _ a b p d +
    weightedAffineResponse 3 _ _ _ _ (a + 1) b (p + 1) d +
    weightedAffineResponse 3 _ _ _ _ (a + 1) b p d = _
  rw [weightedAffineResponse_third_factor _ _ _ _ a b (p + 1) d hx,
    weightedAffineResponse_third_factor _ _ _ _ a b p d hx,
    weightedAffineResponse_third_factor _ _ _ _ (a + 1) b (p + 1) d hy,
    weightedAffineResponse_third_factor _ _ _ _ (a + 1) b p d hy]
  rw [show -(p + 1) - 3 = -p - 4 by ring,hE _ hx,hE _ hy]
  unfold a b
  ring

noncomputable def lowerHead₀Left (p u : ℝ) : ℝ :=
  -lowerNativeAlpha p * u ^ 2 + (p - 1) * (4 * p / 5 - 2) * u + (p + 2) * (1 - 13 * p / 25)

noncomputable def lowerHead₀Right (p v : ℝ) : ℝ :=
  (36 / 25) * v ^ (p + 4) / (p + 1) + lowerNativeAlpha p * v ^ 3 +
    (p - 1) * (2 + 66 * p / 25) * v ^ 2 - (p + 2) * (3 + 108 * p / 25) * v +
    (54 / 25) * (p + 2) * (p + 3)

set_option maxHeartbeats 1800000 in
theorem lowerNativeHead_zero_eq {p d : ℝ} (hp : 1 ≤ p) (hd : d < 1 / 2) :
    let u := 1 - d
    let v := u + 1
    ((36 / 25) * p + lowerNativeSite 3 p 0 d) / (p * (p + 1)) =
      u ^ (-p - 3) * lowerHead₀Left p u + v ^ (-p - 4) * lowerHead₀Right p v := by
  let u := 1 - d
  let v := u + 1
  have hv : 0 < v := by unfold v u; linarith only [hd]
  have hu : 0 < u := by unfold u; linarith only [hd]
  have hp₀ := zero_lt_one.trans_le hp
  have hp₁ : 0 < p + 1 := by positivity
  have hvE : v ^ (-p - 4) * v ^ (p + 4) = 1 := by
    rw [← Real.rpow_add hv,show -p - 4 + (p + 4) = 0 by ring,Real.rpow_zero]
  have huE : u ^ (-p - 3) = u ^ (-p - 4) * u := by
    rw [← Real.rpow_add_one hu.ne',show -p - 4 + 1 = -p - 3 by ring]
  change _ = u ^ (-p - 3) * _ + v ^ (-p - 4) * _
  rw [nativeHead_factor p 0 d hd le_rfl,huE]
  let T := lowerNativeAlpha p * v ^ 3 + (p - 1) * (2 + 66 * p / 25) * v ^ 2 -
    (p + 2) * (3 + 108 * p / 25) * v + (54 / 25) * (p + 2) * (p + 3)
  have hR : v ^ (-p - 4) * lowerHead₀Right p v =
      (36 / 25) / (p + 1) + v ^ (-p - 4) * T := by
    rw [show lowerHead₀Right p v = (36 / 25) * v ^ (p + 4) / (p + 1) + T by
      unfold lowerHead₀Right T; ring]
    rw [mul_add,show v ^ (-p - 4) * ((36 / 25) * v ^ (p + 4) / (p + 1)) =
      (36 / 25) / (p + 1) * (v ^ (-p - 4) * v ^ (p + 4)) by ring,hvE,mul_one]
  rw [hR]
  unfold lowerHead₀Left T lowerNativeAlpha v u
  norm_num only [add_zero,mul_zero,zero_add,one_mul]
  field_simp [hp₀.ne',hp₁.ne']
  ring

noncomputable def lowerHead₁Left (p x : ℝ) : ℝ :=
  -lowerNativeAlpha p * x ^ 3 + (p - 1) * (96 * p / 25 - 18) * x ^ 2 +
    (p + 2) * (39 * p / 25 + 9) * x - (9 / 5) * (p + 2) * (p + 3)

noncomputable def lowerHead₁Right (p y : ℝ) : ℝ :=
  lowerNativeAlpha p * y ^ 2 + (18 / 5) * (p - 1) * (p + 5) * y - 27 * (p + 2) * (1 + 4 * p / 25)

set_option maxHeartbeats 1800000 in
theorem lowerNativeHead_one_eq {p d : ℝ} (hp : 1 ≤ p) (hd : d < 1 / 2) :
    let x := 2 - 3 * d
    let y := x + 1
    lowerNativeSite 3 p 1 d / (p * (p + 1)) =
      x ^ (-p - 4) * lowerHead₁Left p x + y ^ (-p - 3) * lowerHead₁Right p y := by
  let x := 2 - 3 * d
  let y := x + 1
  have hy : 0 < y := by unfold y x; linarith only [hd]
  have hp₀ := zero_lt_one.trans_le hp
  have hp₁ : 0 < p + 1 := by positivity
  have hE : y ^ (-p - 3) = y ^ (-p - 4) * y := by
    rw [← Real.rpow_add_one hy.ne',show -p - 4 + 1 = -p - 3 by ring]
  change _ = x ^ (-p - 4) * _ + y ^ (-p - 3) * _
  rw [nativeHead_factor p 1 d hd zero_le_one,hE]
  norm_num only [mul_one,show 1 + (1 : ℝ) = 2 by norm_num,show 2 + (1 : ℝ) = 3 by norm_num]
  unfold lowerHead₁Left lowerHead₁Right lowerNativeAlpha y x
  rw [show 2 - 3 * d + 1 = 3 - 3 * d by ring]
  field_simp [hp₀.ne',hp₁.ne']
  ring

end ACS12.GammaMeasure

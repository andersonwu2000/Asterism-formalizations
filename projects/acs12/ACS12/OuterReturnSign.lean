import ACS12.OuterReturnShape

/-! The full frequency sign for the outer signed law return. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN Set

theorem outerReturn_density_pos {u m s lam : ℝ} (hu : 0 < u) (hu₁ : u < 1) (hs : 0 < s)
    (hm : 0 ≤ u - m) (hM : u - m ≤ 1 - u) (hlam : 0 ≤ lam) (hlam' : lam < 83 / 300) :
    0 < outerNativeResponse u m s - lam * outerSourceResponse u m s := by
  let x := u * s
  let Y := Real.exp (-s * u)
  let δ := 1 - u
  let D := u - m
  let B := scaledExpTail s u - scaledExpTail s 1
  let A0 := middleA0 u s
  let g := middleRightDensity u s
  let z := middleZ u
  have hx : 0 < x := mul_pos hu hs
  have hY : 0 < Y := Real.exp_pos _
  have hY₁ : 0 < 1 - Y := by
    dsimp only [Y]
    simpa only [neg_mul] using expHead_den_pos (mul_pos hs hu)
  have hδ : 0 < δ := sub_pos.mpr hu₁
  have hB : 0 < B := sub_pos.mpr (scaledExpTail_strictAnti hs hu (mem_Ioi.mpr zero_lt_one) hu₁)
  have hBc : B ≤ δ * BoseShape.C x := by
    dsimp only [B, δ, x]
    simpa only [mul_comm s u] using scaledExpTail_gap_le hs hu hu₁.le
  have hB₁ : B ≤ δ / 2 := hBc.trans (by
    have h := mul_le_mul_of_nonneg_left (boseC_lt_half hx).le hδ.le
    linarith only [h])
  have ha := (polyA_pos hx).le
  have hb := (polyB_pos hx).le
  have hQa : polyA x ≤ x ^ 2 / 2 := (densityPolynomial_lt_quadratic .a hx).le
  have hQb : polyB x ≤ x ^ 2 / 2 := (densityPolynomial_lt_quadratic .b hx).le
  have hD₀ : 0 ≤ D := hm
  have hD₁ : D ≤ δ := hM
  change 0 < δ * A0 - g * (Y * D - B) - lam * (polyB x * B + polyA x * D)
  by_cases hg : g ≤ 0
  · have hA0 : A0 < 1 := by
      unfold A0 middleA0
      have ha₀ := (middleA_pos hu hu₁.le).le
      exact sub_lt_self _ (mul_pos (by positivity) (Real.exp_pos _))
    have hz₀ : (13 / 25) * u ≤ z := by
      unfold z middleZ middleA
      nlinarith only [sq_nonneg u]
    have hz : 0 < z := (mul_pos (by norm_num) hu).trans_le hz₀
    have hgz : g = z * s - A0 := rfl
    have hzS : z * s ≤ 1 := (show z * s ≤ A0 by linarith only [hg, hgz]).trans hA0.le
    have hQ : polyB x * B + polyA x * D ≤ (3 / 4) * δ * x ^ 2 := by
      have h1 := mul_le_mul hQb hB₁ hB.le (by positivity : 0 ≤ x ^ 2 / 2)
      have h2 := mul_le_mul hQa hD₁ hD₀ (by positivity : 0 ≤ x ^ 2 / 2)
      nlinarith only [h1, h2]
    have hNative : δ * (z * s) ≤ δ * A0 - g * (Y * D - B) := by
      have hYd := mul_nonneg hY.le hD₀
      have hB' : 0 ≤ δ + Y * D - B := by linarith only [hB₁, hYd, hδ]
      have h := mul_nonneg (neg_nonneg.mpr hg) hB'
      rw [hgz] at h ⊢
      nlinarith only [h]
    have hS : (169 / 625) * u ^ 2 ≤ z ^ 2 := by
      have h := mul_le_mul hz₀ hz₀ (show 0 ≤ (13 / 25) * u by positivity) hz.le
      nlinarith only [h]
    have hL := mul_lt_mul_of_pos_right hlam' (sq_pos_of_pos hu)
    have hCoef : (3 / 4) * lam * u ^ 2 < z ^ 2 := by
      nlinarith only [hS, hL, sq_pos_of_pos hu]
    have hZS : (3 / 4) * lam * u ^ 2 * s < z := by
      have h := mul_lt_mul_of_pos_right hCoef hs
      have hZ := mul_le_mul_of_nonneg_left hzS hz.le
      nlinarith only [h, hZ]
    have hP : 0 < δ * (z * s - (3 / 4) * lam * x ^ 2) := by
      have h := mul_pos (sub_pos.mpr hZS) hs
      apply mul_pos hδ
      dsimp only [x]
      nlinarith only [h]
    have hQl := mul_le_mul_of_nonneg_left hQ hlam
    nlinarith only [hNative, hQl, hP]
  · have hg₀ : 0 < g := lt_of_not_ge hg
    have hQ : polyB x * B + polyA x * D ≤ δ * (polyA x + polyB x * BoseShape.C x) := by
      have h1 := mul_le_mul_of_nonneg_left hBc hb
      have h2 := mul_le_mul_of_nonneg_left hD₁ ha
      nlinarith only [h1, h2]
    have hN : δ * (A0 - Y * g) ≤ δ * A0 - g * (Y * D - B) := by
      have hYD := mul_le_mul_of_nonneg_left hD₁ hY.le
      have hP : 0 ≤ Y * δ - Y * D + B := by linarith only [hYD, hB]
      nlinarith only [mul_nonneg hg₀.le hP]
    have hA : (1 / 2) * (1 - Y) < A0 - Y * g := outerNative_lower_half hu hu₁.le hs
    have hYe : Real.exp (-x) = Y := by dsimp only [x, Y]; rw [show -(u * s) = -s * u by ring]
    have hK := outerPeanoC_upper hx
    rw [hYe] at hK
    have hKlam := mul_le_mul_of_nonneg_left hK.le hlam
    have hL : (3 / 2) * lam < 1 / 2 := by linarith only [hlam']
    have hPos : 0 < δ * (A0 - Y * g - lam * (polyA x + polyB x * BoseShape.C x)) := by
      apply mul_pos hδ
      nlinarith only [hA, hKlam, mul_lt_mul_of_pos_right hL hY₁]
    nlinarith only [hN, mul_le_mul_of_nonneg_left hQ hlam, hPos]

end ACS12.GammaMeasure


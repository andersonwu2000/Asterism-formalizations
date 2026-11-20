import ACS12.PureAdjacentContactMoment
import ACS12.PureAdjacentOne

/-! The cap/u contact pays its entire left source value. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN Set
open scoped BigOperators

noncomputable def adjacentCapSpan (u : ℝ) : ℝ :=
  40 / 21 - (3072 / 1715) * u ^ 2

private noncomputable def contactBUpper (u : ℝ) : ℝ :=
  u ^ 2 * (1 / (1 + u) + 1011 / 5000 - (59 / 1000) * u)

private theorem zetaTwo_gt :
    (411 / 250 : ℝ) < pureZ 1 := by
  have h0 := powerTail_trapezoid_lower (q := 2) (m := 7) (by norm_num) (by decide)
  have h1 := powerTail_shift (q := 2) (by norm_num) 1
  have h2 := powerTail_shift (q := 2) (by norm_num) 2
  have h3 := powerTail_shift (q := 2) (by norm_num) 3
  have h4 := powerTail_shift (q := 2) (by norm_num) 4
  have h5 := powerTail_shift (q := 2) (by norm_num) 5
  have h6 := powerTail_shift (q := 2) (by norm_num) 6
  norm_num at h0 h1 h2 h3 h4 h5 h6
  unfold pureZ
  norm_num
  linarith only [h0, h1, h2, h3, h4, h5, h6]

private theorem contactBudget_convex :
    ConvexOn ℝ (Icc (39 / 50) (7 / 8))
      (fun u => contactBUpper u + (13 / 50) * adjacentCapSpan u ^ 2) := by
  let d : ℝ := 3072 / 1715
  let k : ℝ := 40 / 21
  let f (u : ℝ) := contactBUpper u + (13 / 50) * adjacentCapSpan u ^ 2
  let G (u : ℝ) := u - 1 + (1 + u)⁻¹ + (1011 / 5000) * u ^ 2 - (59 / 1000) * u ^ 3 +
    (13 / 50) * (k - d * u ^ 2) ^ 2
  let D (u : ℝ) := 1 - (1 + u)⁻¹ ^ 2 + (1011 / 2500) * u - (177 / 1000) * u ^ 2 -
    (26 / 25) * d * u * (k - d * u ^ 2)
  let E (u : ℝ) := 2 / (1 + u) ^ 3 + 1011 / 2500 - (177 / 500) * u +
    (26 / 25) * d * (3 * d * u ^ 2 - k)
  have hEq (u : ℝ) (hu : 0 < 1 + u) : f u = G u := by
    dsimp only [f, G, contactBUpper, adjacentCapSpan, d, k]
    field_simp [hu.ne']
    ring
  have hD (u : ℝ) (hu : 0 < 1 + u) : HasDerivAt G (D u) u := by
    have h := hasDerivAt_id u
    have hInv := (h.const_add 1).inv hu.ne'
    have hSpan := ((h.pow 2).const_mul d).const_sub k
    have hG := ((((h.sub_const 1).add hInv).add ((h.pow 2).const_mul (1011 / 5000))).sub
      ((h.pow 3).const_mul (59 / 1000))).add ((hSpan.pow 2).const_mul (13 / 50))
    simpa only [G, id_eq, Pi.add_apply, Pi.sub_apply, Pi.pow_apply] using
      hG.congr_deriv (show _ = D u by norm_num [D, id_eq, Pi.pow_apply] <;> ring)
  have hD₂ (u : ℝ) (hu : 0 < 1 + u) : HasDerivAt D (E u) u := by
    have h := hasDerivAt_id u
    have hInv := (h.const_add 1).inv hu.ne'
    have hSpan := ((h.pow 2).const_mul d).const_sub k
    have hD := ((((hInv.pow 2).const_sub 1).add (h.const_mul (1011 / 2500))).sub
      ((h.pow 2).const_mul (177 / 1000))).sub ((h.mul hSpan).const_mul ((26 / 25) * d))
    convert hD.congr_deriv (show _ = E u by
      norm_num [E, id_eq, Pi.inv_apply, Pi.pow_apply]
      field_simp [hu.ne']
      ring) using 1
    funext x
    simp only [D, id_eq, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.inv_apply]
    ring
  have hP (u : ℝ) (hu : u ∈ Icc (39 / 50 : ℝ) (7 / 8)) : 0 < 1 + u := by linarith [hu.1]
  have hC : ConvexOn ℝ (Icc (39 / 50) (7 / 8)) G := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (fun u hu => (hD u (hP u hu)).continuousAt.continuousWithinAt)
      (fun u hu => (hD u (hP u (interior_subset hu))).hasDerivWithinAt)
      (fun u hu => (hD₂ u (hP u (interior_subset hu))).hasDerivWithinAt)
    intro u hu
    have hu' : u ∈ Icc (39 / 50 : ℝ) (7 / 8) := interior_subset hu
    have hS := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 39 / 50) hu'.1 2
    have hA : 0 ≤ 1011 / 2500 - (177 / 500) * u := by linarith [hu'.2]
    have hB : 0 ≤ 3 * d * u ^ 2 - k := by dsimp only [d, k]; nlinarith only [hS]
    exact add_nonneg (by
      have h := div_nonneg (by norm_num : (0 : ℝ) ≤ 2) (pow_nonneg (hP u hu').le 3)
      linarith only [h, hA]) (mul_nonneg (by norm_num [d]) hB)
  exact hC.congr (fun u hu => (hEq u (hP u hu)).symm)

theorem adjacentContact_reference {u : ℝ} (hu : 39 / 50 ≤ u) (hu' : u ≤ 7 / 8) :
    (13 / 50) * adjacentCapSpan u ^ 2 + 3 / 100 <
      pureZ 1 - 1 - pureBStack 1 u := by
  let f (x : ℝ) := contactBUpper x + (13 / 50) * adjacentCapSpan x ^ 2
  let a := ((7 / 8 : ℝ) - u) / (7 / 8 - 39 / 50)
  let b := (u - (39 / 50 : ℝ)) / (7 / 8 - 39 / 50)
  have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr hu') (by norm_num)
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hu) (by norm_num)
  have hab : a + b = 1 := by dsimp only [a, b]; ring
  have hU : a * (39 / 50) + b * (7 / 8) = u := by dsimp only [a, b]; ring
  have h := contactBudget_convex.2 (show (39 / 50 : ℝ) ∈ Icc (39 / 50) (7 / 8) by constructor <;> norm_num)
    (show (7 / 8 : ℝ) ∈ Icc (39 / 50) (7 / 8) by constructor <;> norm_num) ha hb hab
  simp only [smul_eq_mul, hU] at h
  change f u ≤ a * f (39 / 50) + b * f (7 / 8) at h
  have hA : f (39 / 50) ≤ 307 / 500 := by norm_num [f, contactBUpper, adjacentCapSpan]
  have hB : f (7 / 8) ≤ 307 / 500 := by norm_num [f, contactBUpper, adjacentCapSpan]
  have hF := h.trans (add_le_add (mul_le_mul_of_nonneg_left hA ha) (mul_le_mul_of_nonneg_left hB hb))
  have hF' : f u ≤ 307 / 500 := hF.trans_eq (by linear_combination (307 / 500 : ℝ) * hab)
  have hu₀ : 0 < u := (by norm_num : (0 : ℝ) < 39 / 50).trans_le hu
  have hStack : pureBStack 1 u ≤ contactBUpper u := by
    simpa only [pureBStack, contactBUpper, sub_self, Real.rpow_zero, one_mul] using oneBStack_le hu₀ hu'
  dsimp only [f] at hF'
  linarith only [hF', hStack, zetaTwo_gt]

theorem adjacentContact_deficit {p u : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hu : 39 / 50 ≤ u) (hu' : u ≤ 7 / 8) :
    (13 / 50) * adjacentCapSpan u ^ 2 <
      pureZ p - 1 - pureBStack p u := by
  have hu₀ := (by norm_num : (0 : ℝ) < 39 / 50).trans_le hu
  have hu₁ := hu'.trans (by norm_num : (7 / 8 : ℝ) ≤ 1)
  have hL := pureBDeficit_exponent_loss hp hp₂ hu₀ hu₁
  have hA := adjacentContact_reference hu hu'
  have hB : (1 - u) / (48 * u) ≤ 3 / 100 := by
    apply (div_le_iff₀ (by positivity : 0 < 48 * u)).mpr
    linarith
  linarith only [hL, hA, hB]

end ACS12.GammaMeasure

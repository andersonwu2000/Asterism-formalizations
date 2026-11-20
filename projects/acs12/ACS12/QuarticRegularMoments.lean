import ACS12.NativeRegularRow
import ACS12.NativeLiteralRows
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace ACS12.NativeCells
open Set

private theorem sine_minus_tangent_nonneg {x : ℝ} (hx : x ∈ Icc 0 Real.pi) :
    0 ≤ Real.sin x - x * Real.cos x := by
  have hd (y : ℝ) : HasDerivAt (fun t => Real.sin t - t * Real.cos t)
      (y * Real.sin y) y := by
    convert (Real.hasDerivAt_sin y).sub ((hasDerivAt_id y).mul (Real.hasDerivAt_cos y)) using 1 <;> dsimp <;> ring
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0:ℝ) Real.pi)
    (Real.continuous_sin.sub (continuous_id.mul Real.continuous_cos)).continuousOn
    (fun y _ => (hd y).hasDerivWithinAt)
    (fun y hy => mul_nonneg (interior_subset hy).1
      (Real.sin_nonneg_of_nonneg_of_le_pi (interior_subset hy).1 (interior_subset hy).2))
  simpa using hm ⟨le_rfl, Real.pi_pos.le⟩ hx hx.1

private theorem sine_cotangent_gap {x : ℝ} (hx : x ∈ Icc 0 Real.pi) :
    0 ≤ (1-x^2/3)*Real.sin x-x*Real.cos x := by
  have hd (y : ℝ) : HasDerivAt (fun t => (1-t^2/3)*Real.sin t-t*Real.cos t)
      (y/3*(Real.sin y-y*Real.cos y)) y := by
    convert (((hasDerivAt_const y (1:ℝ)).sub (((hasDerivAt_id y).pow 2).div_const 3)).mul
      (Real.hasDerivAt_sin y)).sub ((hasDerivAt_id y).mul (Real.hasDerivAt_cos y)) using 1 <;> dsimp <;> ring
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0:ℝ) Real.pi)
    (by fun_prop)
    (fun y _ => (hd y).hasDerivWithinAt)
    (fun y hy => mul_nonneg (by have := (interior_subset hy).1; positivity)
      (sine_minus_tangent_nonneg (interior_subset hy)))
  simpa using hm ⟨le_rfl, Real.pi_pos.le⟩ hx hx.1

/-- Gaussian upper envelope for sinc, obtained from the cotangent tangent. -/
theorem quartic_sinc_gaussian {x : ℝ} (hx : x ∈ Icc 0 Real.pi) :
    Real.sinc x ≤ Real.exp (-x^2/6) := by
  let f : ℝ → ℝ := fun t => Real.exp (t^2/6)*Real.sinc t
  have hd (y : ℝ) (hy : y ∈ interior (Icc (0:ℝ) Real.pi)) :
      HasDerivAt f (Real.exp (y^2/6) *
        ((y^2/3-1)*Real.sin y+y*Real.cos y)/y^2) y := by
    rw [interior_Icc] at hy
    have heq : f =ᶠ[nhds y] fun t => Real.exp (t^2/6)*(Real.sin t/t) := by
      filter_upwards [eventually_ne_nhds hy.1.ne'] with t ht
      simp [f, Real.sinc, ht]
    apply HasDerivAt.congr_of_eventuallyEq _ heq
    convert ((((hasDerivAt_id y).pow 2).div_const 6).exp).mul
      ((Real.hasDerivAt_sin y).div (hasDerivAt_id y) hy.1.ne') using 1 <;>
      dsimp <;> field_simp <;> ring
  have hm := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0:ℝ) Real.pi)
    (show ContinuousOn f (Icc 0 Real.pi) from (by dsimp [f]; fun_prop))
    (fun y hy => (hd y hy).hasDerivWithinAt)
    (fun y hy => div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        (by nlinarith [sine_cotangent_gap (interior_subset hy)])) (sq_nonneg y))
  have hb : Real.exp (x^2/6)*Real.sinc x ≤ 1 := by
    simpa [f] using hm ⟨le_rfl, Real.pi_pos.le⟩ hx hx.1
  have hi : Real.sinc x ≤ 1 / Real.exp (x^2/6) := (le_div_iff₀ (Real.exp_pos (x^2/6))).mpr (by simpa [mul_comm] using hb)
  simpa [Real.exp_neg, div_eq_mul_inv] using hi

private theorem quartic_gaussian_moment {c y : ℝ}
    (hc : c ∈ Icc (986960/100000) (986961/100000)) (hy : y ∈ Icc 0 (1/25)) :
    c^2/45*((1-y)*(1+11*y)*Real.exp (-2*c*y/3)) ≤ 23/10 := by
  have hc0 : 0 ≤ c := by linarith [hc.1]
  let f : ℝ → ℝ := fun t => (1-t)*(1+11*t)*Real.exp (-2*c*t/3)
  have hd (t : ℝ) : HasDerivAt f
      ((10-22*t-2*c/3*((1-t)*(1+11*t)))*Real.exp (-2*c*t/3)) t := by
    have h1 := (hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)
    have h2 := (hasDerivAt_const t (1:ℝ)).add ((hasDerivAt_id t).const_mul 11)
    have h3 := (((hasDerivAt_id t).const_mul (-2*c)).div_const 3).exp
    convert (h1.mul h2).mul h3 using 1 <;> dsimp [f] <;> ring
  have hm : MonotoneOn f (Icc 0 (1/25)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0:ℝ) (1/25))
      (by dsimp [f]; fun_prop) (fun t _ => (hd t).hasDerivWithinAt)
    intro t ht
    have ht' : t ∈ Icc (0:ℝ) (1/25) := interior_subset ht
    have hP : (1-t)*(1+11*t) ≤ 864/625 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ht'.2)
        (show 0 ≤ 10-11*((1:ℝ)/25+t) by linarith [ht'.2])]
    apply mul_nonneg _ (Real.exp_pos _).le
    have hmul := mul_le_mul_of_nonneg_left hP (show 0 ≤ 2*c/3 by positivity)
    nlinarith [hc.2, ht'.2]
  have htop := mul_le_mul_of_nonneg_left
    (hm hy ⟨by norm_num,le_rfl⟩ hy.2) (show 0 ≤ c^2/45 by positivity)
  have hpow : c^2 ≤ (986961/100000:ℝ)^2 := pow_le_pow_left₀ hc0 hc.2 2
  have hseries := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 2*(986960/100000)/75) 6
  norm_num [Finset.sum_range_succ] at hseries
  have he := hseries.trans (Real.exp_le_exp.mpr (show (12337:ℝ)/46875 ≤ 2*c/75 by linarith [hc.1]))
  have hbound : c^2/45*f (1/25) ≤ 23/10 := by
    dsimp [f]
    rw [show -2*c*(1/25)/3 = -(2*c/75) by ring, Real.exp_neg]
    apply (le_of_mul_le_mul_right _ (Real.exp_pos (2*c/75)))
    field_simp
    rw [show c*2/75 = 2*c/75 by ring]
    nlinarith [hpow, he]
  exact htop.trans hbound

theorem quartic_regular_second_bound {N : ℝ} (hN : 5 ≤ N) :
    Real.sin (Real.pi/N)^2*(N^2-1)/3 ≤ 33/10 := by
  have hN0 : 0 < N := by linarith
  have hN2 : 0 ≤ N^2-1 := by nlinarith
  have hs := mul_le_mul_of_nonneg_right
    (Real.sin_sq_le_sq (x:=Real.pi/N)) (show 0 ≤ (N^2-1)/3 by positivity)
  have hp : Real.pi^2 < 99/10 := by nlinarith [Real.pi_lt_d4, Real.pi_pos]
  have he : (Real.pi/N)^2*((N^2-1)/3) ≤ Real.pi^2/3 := by
    field_simp
    nlinarith [sq_nonneg Real.pi]
  nlinarith [hs.trans he]

theorem quartic_regular_fourth_bound {N : ℝ} (hN : 5 ≤ N) :
    Real.sin (Real.pi/N)^4*(N^4+10*N^2-11)/45 ≤ 23/10 := by
  have hN0 : 0 < N := by linarith
  have hN2 : 0 < N^2 := sq_pos_of_pos hN0
  have hy : 1/N^2 ∈ Icc (0:ℝ) (1/25) :=
    ⟨by positivity, (div_le_iff₀ hN2).mpr (by nlinarith)⟩
  have hc : Real.pi^2 ∈ Icc (986960/100000:ℝ) (986961/100000) := by
    constructor <;> nlinarith [Real.pi_gt_d6, Real.pi_lt_d6, Real.pi_pos]
  have hb : Real.pi/N ∈ Icc (0:ℝ) Real.pi :=
    ⟨by positivity, (div_le_iff₀ hN0).mpr (by nlinarith [Real.pi_pos])⟩
  have hsp : 0 ≤ Real.sinc (Real.pi/N) := by
    rw [Real.sinc_of_ne_zero (by positivity)]
    exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hb.1 hb.2) hb.1
  have h4 := pow_le_pow_left₀ hsp (quartic_sinc_gaussian hb) 4
  rw [← Real.exp_nat_mul] at h4
  norm_num only [Nat.cast_ofNat] at h4
  have hex : (4:ℝ)*(-(Real.pi/N)^2/6) = -2*Real.pi^2*(1/N^2)/3 := by ring
  rw [hex] at h4
  have hp : 0 ≤ Real.pi^4/45*((1-1/N^2)*(1+11*(1/N^2))) := by
    apply mul_nonneg (by positivity)
    exact mul_nonneg (by linarith [hy.2]) (by positivity)
  have hh := mul_le_mul_of_nonneg_left h4 hp
  have heq : Real.pi^4/45*((1-1/N^2)*(1+11*(1/N^2))) * Real.sinc (Real.pi/N)^4 =
      Real.sin (Real.pi/N)^4*(N^4+10*N^2-11)/45 := by
    rw [Real.sinc_of_ne_zero (by positivity)]
    field_simp
    ring
  rw [heq] at hh
  have ht := quartic_gaussian_moment hc hy
  convert hh.trans (le_of_eq_of_le _ ht) using 1
  ring

end ACS12.NativeCells

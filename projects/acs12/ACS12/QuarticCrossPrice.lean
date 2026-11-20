import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

namespace ACS12.HighCurrent
open Set

noncomputable def quarticCrossPrice (p θ : ℝ) : ℝ :=
  if θ < Real.pi / 4 then (2*Real.cos θ)^(-p) *
    (3*(1-Real.sin (2*θ)^p)/(2*p)+θ*(Real.cos (2*θ)/Real.sin (2*θ))) else 0

/-- Rational upper envelope obtained by differentiating its exact remainder. -/
theorem quartic_arctan_upper {v : ℝ} (hv : 0 ≤ v) :
    Real.arctan v ≤ v*(1-v^2/(3+9*v^2/5)) := by
  let f : ℝ → ℝ := fun t => t*(1-t^2/(3+9*t^2/5))-Real.arctan t
  have hd (t : ℝ) : HasDerivAt f
      (4*t^6/((t^2+1)*(3*t^2+5)^2)) t := by
    have hd0 : 3+9*t^2/5 ≠ 0 := by positivity
    have h1 := (hasDerivAt_id t).pow 2
    have h2 := (hasDerivAt_const t (3:ℝ)).add ((h1.const_mul 9).div_const 5)
    have hh := ((hasDerivAt_id t).mul ((hasDerivAt_const t (1:ℝ)).sub (h1.div h2 hd0))).sub
      (Real.hasDerivAt_arctan t)
    convert hh using 1 <;> dsimp [f] <;> field_simp <;> ring
  have hm : MonotoneOn f (Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0:ℝ))
      (fun t _ => (hd t).continuousAt.continuousWithinAt)
      (fun t _ => (hd t).hasDerivWithinAt) (fun t _ => by positivity)
  have hh := hm (show (0:ℝ) ∈ Ici 0 by simp) hv hv
  simpa [f] using hh

theorem quartic_cross_rational {w : ℝ} (hw : 0 ≤ w) :
    (1+w)^2/16 * (3/8*(1-16*w^2/(1+w)^4) +
      (1-w)/2*(1-w/(3+9*w/5))) ≤ 1/16-5*(w/(1+w))^2/32 := by
  have h1 : 0 < 1+w := by positivity
  have h2 : 0 < 5+3*w := by positivity
  have hid : 16*(1/16-5*(w/(1+w))^2/32 -
      (1+w)^2/16 * (3/8*(1-16*w^2/(1+w)^4) +
        (1-w)/2*(1-w/(3+9*w/5)))) =
      ((3+w)*(5-16*w)^2+w^2*(82+94*w+295*w^2+405*w^3+80*w^4)) /
        (120*(1+w)^2*(5+3*w)) := by field_simp; ring
  have hnon : 0 ≤ ((3+w)*(5-16*w)^2+w^2*(82+94*w+295*w^2+405*w^3+80*w^4)) /
        (120*(1+w)^2*(5+3*w)) := by positivity
  linarith

private theorem quartic_power_quotient {b p : ℝ} (hb : 0 ≤ b) (hp : 4 ≤ p) :
    (1-b^p)/p ≤ (1-b^4)/4 := by
  have h := one_add_mul_self_le_rpow_one_add
    (show -1 ≤ b^(4:ℕ)-1 by nlinarith [sq_nonneg (b^2)]) (show 1 ≤ p/4 by linarith)
  rw [add_sub_cancel] at h
  rw [← Real.rpow_natCast, ← Real.rpow_mul hb] at h
  norm_num only [Nat.cast_ofNat] at h
  rw [show (4:ℝ)*(p/4)=p by ring] at h
  norm_num only [Real.rpow_ofNat] at h
  apply (div_le_iff₀ (show 0 < p by linarith)).mpr
  nlinarith

theorem quartic_cross_four_bound {θ : ℝ} (hθ : 0 < θ) (hθU : θ < Real.pi/4) :
    quarticCrossPrice 4 θ ≤ 1/16-5*Real.sin θ^4/32 := by
  have ht : θ < Real.pi/2 := by linarith [Real.pi_pos]
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],ht⟩
  let v := Real.tan θ
  let w := v^2
  have hv : 0 < v := by dsimp [v]; rw [Real.tan_eq_sin_div_cos]; positivity
  have hw : 0 ≤ w := sq_nonneg v
  have hat : Real.arctan v = θ := Real.arctan_tan (by linarith [Real.pi_pos]) ht
  have hss : Real.sin θ^2 = w/(1+w) := by rw [← hat]; exact Real.sin_sq_arctan v
  have hcc : Real.cos θ^2 = 1/(1+w) := by rw [← hat]; exact Real.cos_sq_arctan v
  have h2c : 0 ≤ Real.cos (2*θ) := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos],by linarith⟩
  have hw1 : w ≤ 1 := by
    have hh := Real.cos_two_mul θ
    rw [hcc] at hh
    rw [← mul_div_assoc, mul_one] at hh
    have := (le_div_iff₀ (show 0 < 1+w by positivity)).mp
      (show 1 ≤ 2/(1+w) by linarith [hh])
    linarith
  have ha : Real.arctan v/v ≤ 1-v^2/(3+9*v^2/5) :=
    (div_le_iff₀ hv).mpr (by simpa [mul_comm] using quartic_arctan_upper hv.le)
  rw [hat] at ha
  have ha' : θ/v ≤ 1-w/(3+9*w/5) := by simpa [w,mul_comm] using ha
  have hcot : Real.cos (2*θ)/Real.sin (2*θ) = (1-w)/(2*v) := by
    dsimp [w,v]
    rw [Real.tan_eq_sin_div_cos, Real.sin_two_mul, Real.cos_two_mul']
    field_simp <;> ring
  have hθcot : θ*(Real.cos (2*θ)/Real.sin (2*θ)) ≤
      (1-w)/2*(1-w/(3+9*w/5)) := by
    rw [hcot]
    have hh := mul_le_mul_of_nonneg_left ha' (div_nonneg (sub_nonneg.mpr hw1) (by norm_num : (0:ℝ) ≤ 2))
    convert hh using 1 <;> ring
  have hs4 : Real.sin (2*θ)^4 = 16*w^2/(1+w)^4 := by
    rw [Real.sin_two_mul]
    calc
      (2*Real.sin θ*Real.cos θ)^4 = 16*(Real.sin θ^2)^2*(Real.cos θ^2)^2 := by ring
      _ = _ := by rw [hss,hcc]; field_simp
  have hc4 : (2*Real.cos θ)^(- (4:ℝ)) = (1+w)^2/16 := by
    rw [Real.rpow_neg (by positivity : 0 ≤ 2*Real.cos θ), Real.rpow_ofNat]
    have hh : (2*Real.cos θ)^4 = 16*(Real.cos θ^2)^2 := by ring
    rw [hh,hcc]
    field_simp
  have hh := mul_le_mul_of_nonneg_left hθcot (show 0 ≤ (1+w)^2/16 by positivity)
  have hr := quartic_cross_rational hw
  rw [quarticCrossPrice, if_pos hθU, hc4, Real.rpow_ofNat, hs4]
  have hsout : Real.sin θ^4 = (w/(1+w))^2 := by calc
    Real.sin θ^4 = (Real.sin θ^2)^2 := by ring
    _ = _ := by rw [hss]
  rw [hsout]
  norm_num only [show (2:ℝ)*4=8 by norm_num]
  nlinarith [hh,hr]

theorem quarticCrossPrice_le {p θ : ℝ} (hp : 4 ≤ p) (hθ : 0 < θ)
    (hθU : θ ≤ Real.pi/4) : quarticCrossPrice p θ ≤ 1/16-5*Real.sin θ^4/32 := by
  have hp0 : 0 < p := by linarith
  have ht : θ < Real.pi/2 := by linarith [Real.pi_pos]
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],ht⟩
  have hs2 : 0 < Real.sin (2*θ) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hc2 : 0 ≤ Real.cos (2*θ) := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos],by linarith⟩
  by_cases hlt : θ < Real.pi/4
  · have hbase : 1 ≤ 2*Real.cos θ := by nlinarith [Real.cos_two_mul θ]
    have hfac : (2*Real.cos θ)^(-p) ≤ (2*Real.cos θ)^(-(4:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
    have hq := quartic_power_quotient hs2.le hp
    have hcost : 3*(1-Real.sin (2*θ)^p)/(2*p) ≤ 3*(1-Real.sin (2*θ)^4)/8 := by
      convert mul_le_mul_of_nonneg_left hq (by norm_num : (0:ℝ) ≤ 3/2) using 1 <;> ring
    have hbp : 0 ≤ 3*(1-Real.sin (2*θ)^p)/(2*p)+θ*(Real.cos (2*θ)/Real.sin (2*θ)) := by
      have hb := Real.rpow_le_one hs2.le (Real.sin_le_one _) hp0.le
      have hb' : 0 ≤ 1-Real.sin (2*θ)^p := sub_nonneg.mpr hb
      positivity
    have hcost' : 3*(1-Real.sin (2*θ)^p)/(2*p)+θ*(Real.cos (2*θ)/Real.sin (2*θ)) ≤
        3*(1-Real.sin (2*θ)^4)/8+θ*(Real.cos (2*θ)/Real.sin (2*θ)) := by linarith
    have hm := mul_le_mul hfac hcost' hbp
      (Real.rpow_pos_of_pos (by positivity : 0 < 2*Real.cos θ) (-(4:ℝ))).le
    have hh : quarticCrossPrice p θ ≤ quarticCrossPrice 4 θ := by
      simpa only [quarticCrossPrice,if_pos hlt,show (2:ℝ)*4=8 by norm_num,Real.rpow_ofNat] using hm
    exact hh.trans (quartic_cross_four_bound hθ hlt)
  · rw [quarticCrossPrice,if_neg hlt]
    have hs : Real.sin θ^2 ≤ 1/2 := by nlinarith [Real.cos_two_mul_eq_one_sub θ]
    have hs4 := pow_le_pow_left₀ (sq_nonneg (Real.sin θ)) hs 2
    nlinarith

end ACS12.HighCurrent

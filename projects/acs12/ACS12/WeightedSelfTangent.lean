import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-! Quantitative tangent support from the strict decrease of N cubed times the slope. -/
namespace ACS12
open Set
set_option maxHeartbeats 1200000

 theorem weightedSlope_tangent {Q q₁ q₂ : ℝ→ℝ}
    (hD : ∀ N>1, HasDerivAt Q (q₁ N) N)
    (hD₁ : ∀ N>1, HasDerivAt q₁ (q₂ N) N)
    (hNeg : ∀ N>1, q₂ N+3*q₁ N/N<0)
    {n x : ℝ} (hn : 1<n) (hx : 1<x) (hxn : x≠n) :
    Q x+n^3*q₁ n/(2*x^2)<Q n+n*q₁ n/2 := by
  let W (N : ℝ):=N^3*q₁ N
  have hWD (N : ℝ) (hN : 1<N) :
      HasDerivAt W (N^3*(q₂ N+3*q₁ N/N)) N := by
    have hN₀ : 0<N := zero_lt_one.trans hN
    convert ((hasDerivAt_id N).pow 3).mul (hD₁ N hN) using 1
    simp only [id_eq,Pi.pow_apply,Nat.cast_ofNat,Nat.reduceSub,mul_one]
    field_simp [hN₀.ne']
    <;> ring
  have hW : StrictAntiOn W (Ioi 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioi _)
    · exact fun N hN=>(hWD N hN).continuousAt.continuousWithinAt
    · intro N hN
      have hN₁ : 1<N:=interior_subset hN
      rw [(hWD N hN₁).deriv]
      exact mul_neg_of_pos_of_neg (pow_pos (zero_lt_one.trans hN₁) 3) (hNeg N hN₁)
  let H (N : ℝ):=Q N+n^3*q₁ n/(2*N^2)
  have hHD (N : ℝ) (hN : 1<N) :
      HasDerivAt H (q₁ N-W n/N^3) N := by
    have hN₀ : 0<N:=zero_lt_one.trans hN
    have h:= (hD N hN).add
      ((hasDerivAt_const N (n^3*q₁ n)).div
        (((hasDerivAt_id N).pow 2).const_mul 2) (by positivity : 2*N^2≠0))
    convert h using 1
    simp only [id_eq,Pi.pow_apply,Nat.cast_ofNat,Nat.reduceSub,mul_one]
    unfold W
    field_simp [hN₀.ne']
    <;> ring
  have hProd (N : ℝ) (hN : 1<N) :
      (q₁ N-W n/N^3)*N^3=W N-W n := by
    unfold W
    field_simp [(zero_lt_one.trans hN).ne']
  have hHn : H n=Q n+n*q₁ n/2 := by
    unfold H
    field_simp [(zero_lt_one.trans hn).ne']
    <;> ring
  change H x<Q n+n*q₁ n/2
  rw [←hHn]
  rcases lt_or_gt_of_ne hxn with hxn|hnx
  · have hMono : StrictMonoOn H (Icc x n) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      · intro N hN
        exact (hHD N (hx.trans_le hN.1)).continuousAt.continuousWithinAt
      · intro N hN
        rw [interior_Icc] at hN
        have hN₁:=hx.trans hN.1
        rw [(hHD N hN₁).deriv]
        have h:=hW hN₁ hn hN.2
        apply pos_of_mul_pos_left (b:=N^3) _ (pow_pos (zero_lt_one.trans hN₁) 3).le
        rw [hProd N hN₁]
        exact sub_pos.mpr h
    exact hMono (left_mem_Icc.mpr hxn.le) (right_mem_Icc.mpr hxn.le) hxn
  · have hAnti : StrictAntiOn H (Icc n x) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      · intro N hN
        exact (hHD N (hn.trans_le hN.1)).continuousAt.continuousWithinAt
      · intro N hN
        rw [interior_Icc] at hN
        have hN₁:=hn.trans hN.1
        rw [(hHD N hN₁).deriv]
        have h:=hW hn hN₁ hN.1
        apply neg_of_mul_neg_left (b:=N^3) _ (pow_pos (zero_lt_one.trans hN₁) 3).le
        rw [hProd N hN₁]
        exact sub_neg.mpr h
    exact hAnti (left_mem_Icc.mpr hnx.le) (right_mem_Icc.mpr hnx.le) hnx

end ACS12

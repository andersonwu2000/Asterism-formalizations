import ACS12.BoseShape
import ACS12.FourthRoot

/-! The centered pure head comparison uses decrease of x/sinh x. -/
namespace ACS12.GammaMeasure
open Set CenteredCircle.AllN BoseShape
set_option maxHeartbeats 1000000

private theorem sinh_sub_price {x : ℝ} (hx : 0 < x) : Real.sinh x < x*Real.cosh x := by
  let f (t : ℝ) := t*Real.cosh t-Real.sinh t
  have hD (t : ℝ) : HasDerivAt f (t*Real.sinh t) t := by
    convert (((hasDerivAt_id t).mul (Real.hasDerivAt_cosh t)).sub (Real.hasDerivAt_sinh t)) using 1
    simp only [id_eq,one_mul]; ring
  have h := positive_of_derivative (by simp [f]) hD
    (fun t ht => mul_pos ht (Real.sinh_pos_iff.mpr ht)) hx
  exact sub_pos.mp h

theorem pureHead_sinhRatio_strictAnti : StrictAntiOn (fun x : ℝ => x/Real.sinh x) (Ioi 0) := by
  have hD (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun x : ℝ => x/Real.sinh x)
        ((Real.sinh x-x*Real.cosh x)/(Real.sinh x)^2) x := by
    simpa only [id_eq,one_mul] using
      (hasDerivAt_id x).div (Real.hasDerivAt_sinh x) (Real.sinh_pos_iff.mpr hx).ne'
  apply strictAntiOn_of_deriv_neg (convex_Ioi _)
  · exact fun x hx => (hD x hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx₀ : 0 < x := interior_subset hx
    rw [(hD x hx₀).deriv]
    exact div_neg_of_neg_of_pos (sub_neg.mpr (sinh_sub_price hx₀)) (sq_pos_of_pos (Real.sinh_pos_iff.mpr hx₀))

private theorem pureHead_centered_identity {s v r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    Real.exp (-s*v)*(r+scaledExpTail s r) =
      Real.exp (-s*(v-r/2))*(r/(2*Real.sinh (s*r/2))) := by
  have hsr : 0 < s*r := mul_pos hs hr
  have hSinh : 0 < Real.sinh (s*r/2) := Real.sinh_pos_iff.mpr (half_pos hsr)
  have hExp : Real.exp (s*r)-1 ≠ 0 := (expTail_den_pos hsr).ne'
  have hFactor : 2*Real.sinh (s*r/2)*Real.exp (s*r/2) = Real.exp (s*r)-1 := by
    rw [Real.sinh_eq]
    have hPlus : Real.exp (s*r/2)*Real.exp (s*r/2) = Real.exp (s*r) := by
      rw [←Real.exp_add]; congr 1; ring
    have hMinus : Real.exp (-(s*r/2))*Real.exp (s*r/2) = 1 := by
      rw [←Real.exp_add]; simp
    nlinarith only [hPlus,hMinus]
  have hMove : Real.exp (-s*(v-r/2)) = Real.exp (-s*v)*Real.exp (s*r/2) := by
    rw [←Real.exp_add]; congr 1; ring
  have hSquare : Real.exp (s*r/2)^2 = Real.exp (s*r) := by
    rw [pow_two,←Real.exp_add]; congr 1; ring
  have hCross : Real.exp (s*r)*(2*Real.sinh (s*r/2)) =
      (Real.exp (s*r)-1)*Real.exp (s*r/2) := by
    calc
      _ = (2*Real.sinh (s*r/2))*Real.exp (s*r/2)^2 := by rw [hSquare]; ring
      _ = _ := by linear_combination congrArg (fun x : ℝ => x*Real.exp (s*r/2)) hFactor
  unfold scaledExpTail
  rw [hMove]
  field_simp [hExp,hSinh.ne']
  nlinarith only [hCross]

theorem pureHead_centered_density_lt {s u m : ℝ} (hs : 0 < s) (hm : m < u)
    (hr : 0 < 2*m-u) :
    Real.exp (-s*u)*(u+scaledExpTail s u) <
      Real.exp (-s*m)*((2*m-u)+scaledExpTail s (2*m-u)) := by
  have hu : 0 < u := by linarith only [hm,hr]
  have hrU : 2*m-u < u := by linarith only [hm]
  have hRatio := pureHead_sinhRatio_strictAnti
    (half_pos (mul_pos hs hr)) (half_pos (mul_pos hs hu))
    (by nlinarith only [mul_pos hs (sub_pos.mpr hrU)] : s*(2*m-u)/2 < s*u/2)
  have hNorm : (2*m-u)/(2*Real.sinh (s*(2*m-u)/2)) > u/(2*Real.sinh (s*u/2)) := by
    have h := div_lt_div_of_pos_right hRatio hs
    have hId (r : ℝ) (hr : 0 < r) :
        (s*r/2/Real.sinh (s*r/2))/s = r/(2*Real.sinh (s*r/2)) := by
      field_simp [hs.ne',(Real.sinh_pos_iff.mpr (half_pos (mul_pos hs hr))).ne']
      <;> ring
    simpa only [hId u hu,hId (2*m-u) hr] using h
  rw [pureHead_centered_identity hs hu,pureHead_centered_identity hs hr]
  have hCenter : -s*(m-(2*m-u)/2) = -s*(u-u/2) := by ring
  rw [hCenter]
  exact mul_lt_mul_of_pos_left hNorm (Real.exp_pos _)

end ACS12.GammaMeasure

import ACS12.PureZetaBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! The full increasing second-Bernoulli error multiplier. -/
namespace ACS12.GammaMeasure

open Set MeasureTheory Filter

noncomputable def boseB2Error (x : ℝ) : ℝ :=
  x⁻¹ + 1 / 2 + x / 12 - (1 - Real.exp (-x))⁻¹

theorem boseB2Error_pos {x : ℝ} (hx : 0 < x) : 0 < boseB2Error x :=
  sub_pos.mpr (bose_inverse_B2 hx)

private theorem boseB2Error_cosh_guard {x : ℝ} (hx : 0 < x) :
    0 < (x ^ 2 - 12) * (Real.cosh x - 1) + 6 * x ^ 2 := by
  let a (j : ℕ) := x ^ (2 * (j + 2)) / ((2 * (j + 2)).factorial : ℝ)
  let b (j : ℕ) := x ^ (2 * (j + 3)) / ((2 * (j + 3)).factorial : ℝ)
  have ha : HasSum a (Real.cosh x - (1 + x ^ 2 / 2)) := by
    simpa [a,Finset.sum_range_succ,Nat.factorial] using
      (hasSum_nat_add_iff' 2).mpr (Real.hasSum_cosh x)
  have hb : HasSum b (Real.cosh x - (1 + x ^ 2 / 2 + x ^ 4 / 24)) := by
    simpa [b,Finset.sum_range_succ,Nat.factorial] using
      (hasSum_nat_add_iff' 3).mpr (Real.hasSum_cosh x)
  let f (j : ℕ) := x ^ 2 * a j - 12 * b j
  have hf : HasSum f ((x ^ 2 - 12) * (Real.cosh x - 1) + 6 * x ^ 2) := by
    convert (ha.mul_left (x ^ 2)).sub (hb.mul_left 12) using 1
    ring
  have hCoeff (j : ℕ) :
      f j = x ^ (2 * j + 6) * ((2 * (j : ℝ) + 6) * (2 * (j : ℝ) + 5) - 12) /
        ((2 * j + 6).factorial : ℝ) := by
    let q := 2 * j + 4
    have hq : (q : ℝ) = 2 * (j : ℝ) + 4 := by unfold q; push_cast; rfl
    unfold f a b
    rw [show 2 * (j + 2) = q by unfold q; omega,show 2 * (j + 3) = q + 2 by unfold q; omega,
      show 2 * j + 6 = q + 2 by unfold q; omega,
      show 2 * (j : ℝ) + 6 = (q : ℝ) + 2 by rw [hq]; ring,
      show 2 * (j : ℝ) + 5 = (q : ℝ) + 1 by rw [hq]; ring]
    have hF : (0 : ℝ) < q.factorial := Nat.cast_pos.mpr (Nat.factorial_pos q)
    have hq₁ : ((q : ℝ) + 1) ≠ 0 := by positivity
    have hq₂ : ((q : ℝ) + 2) ≠ 0 := by positivity
    rw [show q + 2 = q + 1 + 1 by omega]
    simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
    rw [show (q : ℝ) + 1 + 1 = (q : ℝ) + 2 by ring]
    field_simp [hF.ne',hq₁,hq₂]
  have hF (j : ℕ) : 0 < f j := by
    rw [hCoeff]
    have hj := Nat.cast_nonneg (α := ℝ) j
    have hP : 0 < (2 * (j : ℝ) + 6) * (2 * (j : ℝ) + 5) - 12 := by
      nlinarith only [hj,sq_nonneg (j : ℝ)]
    positivity
  rw [← hf.tsum_eq]
  exact hf.summable.tsum_pos (fun j => (hF j).le) 0 (hF 0)

theorem boseB2Error_strictMono : StrictMonoOn boseB2Error (Ioi 0) := by
  have hD (x : ℝ) (hx : 0 < x) : HasDerivAt boseB2Error
      (1 / 12 - x⁻¹ ^ 2 + Real.exp (-x) / (1 - Real.exp (-x)) ^ 2) x := by
    have hE := (hasDerivAt_neg x).exp
    have hDen : 0 < 1 - Real.exp (-x) := CenteredCircle.AllN.expHead_den_pos hx
    have hi := (hasDerivAt_id x).inv hx.ne'
    have hTail := (hE.const_sub 1).inv hDen.ne'
    convert ((hi.add_const (1 / 2)).add ((hasDerivAt_id x).div_const 12)).sub hTail using 1
    simp only [id_eq,neg_neg]
    rw [inv_pow]
    ring
  have hE (x : ℝ) (hx : 0 < x) :
      Real.exp (-x) / (1 - Real.exp (-x)) ^ 2 = (2 * (Real.cosh x - 1))⁻¹ := by
    have hDen : 0 < 1 - Real.exp (-x) := CenteredCircle.AllN.expHead_den_pos hx
    have hC : 0 < 2 * (Real.cosh x - 1) := mul_pos (by norm_num)
      (sub_pos.mpr (Real.one_lt_cosh.mpr hx.ne'))
    apply (div_eq_iff (pow_ne_zero _ hDen.ne')).mpr
    apply (eq_inv_mul_iff_mul_eq₀ hC.ne').2
    rw [Real.cosh_eq]
    simp only [Real.exp_neg]
    field_simp [Real.exp_ne_zero x] <;> ring
  apply strictMonoOn_of_deriv_pos (convex_Ioi _)
  · intro x hx
    exact (hD x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx₀ : 0 < x := hx
    rw [(hD x hx₀).deriv,hE x hx₀]
    have hC : 0 < Real.cosh x - 1 := sub_pos.mpr (Real.one_lt_cosh.mpr hx₀.ne')
    apply pos_of_mul_pos_left (b := 12 * x ^ 2 * (Real.cosh x - 1)) _ (by positivity)
    have hEq : (12 * x ^ 2 * (Real.cosh x - 1)) *
        (1 / 12 - x⁻¹ ^ 2 + (2 * (Real.cosh x - 1))⁻¹) =
        (x ^ 2 - 12) * (Real.cosh x - 1) + 6 * x ^ 2 := by
      rw [inv_pow]
      field_simp [hx₀.ne',hC.ne'] <;> ring
    rw [mul_comm,hEq]
    exact boseB2Error_cosh_guard hx₀


theorem signedBose_B2_upper {f : ℝ → ℝ} {r c : ℝ} (hr : 0 < r) (hc : 0 < c)
    (hF : MeasureTheory.IntegrableOn f (Ioi 0))
    (hI : MeasureTheory.IntegrableOn (fun s => f s * s⁻¹) (Ioi 0))
    (hD : MeasureTheory.IntegrableOn (fun s => f s * s) (Ioi 0))
    (hQ : MeasureTheory.IntegrableOn (fun s => f s * (r / (1 - Real.exp (-(r * s))))) (Ioi 0))
    (hLeft : ∀ s > 0, s < c → f s ≤ 0)
    (hRight : ∀ s > c, 0 ≤ f s)
    (hPos : 0 < ∫ s : ℝ in Ioi 0, f s) :
    (∫ s : ℝ in Ioi 0, f s * (r / (1 - Real.exp (-(r * s))))) <
      (∫ s : ℝ in Ioi 0, f s * s⁻¹) + (r / 2) * (∫ s : ℝ in Ioi 0, f s) +
        (r ^ 2 / 12) * ∫ s : ℝ in Ioi 0, f s * s := by
  let E (s : ℝ) := r * boseB2Error (r * s)
  let A (s : ℝ) := f s * s⁻¹ + (r / 2) * f s + (r ^ 2 / 12) * (f s * s)
  let Q (s : ℝ) := f s * (r / (1 - Real.exp (-(r * s))))
  have hEq (s : ℝ) (hs : 0 < s) : A s - Q s = f s * E s := by
    unfold A Q E boseB2Error
    rw [mul_inv_rev]
    field_simp [hr.ne',hs.ne',(CenteredCircle.AllN.expHead_den_pos (mul_pos hr hs)).ne']
  have hA₁ : IntegrableOn (fun s => f s * s⁻¹ + (r / 2) * f s) (Ioi 0) :=
    hI.add (hF.const_mul _)
  have hA : IntegrableOn A (Ioi 0) := hA₁.add (hD.const_mul _)
  have hE : IntegrableOn (fun s => f s * E s) (Ioi 0) := by
    apply (hA.sub hQ).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact hEq s hs
  have hEC : 0 < E c := mul_pos hr (boseB2Error_pos (mul_pos hr hc))
  have hMon : MonotoneOn E (Ioi 0) := by
    intro x hx y hy hxy
    exact mul_le_mul_of_nonneg_left (boseB2Error_strictMono.monotoneOn
      (show 0 < r * x from mul_pos hr hx) (show 0 < r * y from mul_pos hr hy)
      (mul_le_mul_of_nonneg_left hxy hr.le)) hr.le
  have hL := integral_mono_ae (hF.mul_const (E c)) hE (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rcases lt_trichotomy s c with hsc | rfl | hcs
    · exact mul_le_mul_of_nonpos_left (hMon hs hc hsc.le) (hLeft s hs hsc)
    · exact le_rfl
    · exact mul_le_mul_of_nonneg_left (hMon hc hs hcs.le) (hRight s hcs))
  rw [integral_mul_const] at hL
  have hEInt : (∫ s : ℝ in Ioi 0, f s * E s) =
      (∫ s : ℝ in Ioi 0, A s) - ∫ s : ℝ in Ioi 0, Q s := by
    rw [← integral_sub hA hQ]
    exact setIntegral_congr_fun measurableSet_Ioi (fun s hs => (hEq s hs).symm)
  rw [hEInt] at hL
  have hStrict := (mul_pos hPos hEC).trans_le hL
  unfold A at hStrict
  rw [integral_add hA₁ (hD.const_mul _),integral_add hI (hF.const_mul _),
    integral_const_mul,integral_const_mul] at hStrict
  linarith only [hStrict]

end ACS12.GammaMeasure


import ACS12.QuarticCotSeries
import ACS12.QuarticRootComparison
import ACS12.ConcaveSupport

namespace ACS12.NativeCells
open Set

private theorem cot_curvature_mono (n : ℕ) {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1/4) :
    quarticCotCurvatureTerm n x ≤ quarticCotCurvatureTerm n y := by
  have hy0 : 0 ≤ y := hx.trans hxy
  have hk : (1:ℝ) ≤ ((n:ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  have hdx : 0 < ((n:ℝ)+1)^2-x^2 := by nlinarith
  have hdy : 0 < ((n:ℝ)+1)^2-y^2 := by nlinarith
  have hsq : x^2 ≤ y^2 := pow_le_pow_left₀ hx hxy 2
  have he (t : ℝ) (ht : ((n:ℝ)+1)^2-t^2 ≠ 0) :
      quarticCotCurvatureTerm n t = 2/(((n:ℝ)+1)^2-t^2)+
        4*t^2/(((n:ℝ)+1)^2-t^2)^2 := by
    unfold quarticCotCurvatureTerm
    field_simp
    ring
  rw [he x hdx.ne',he y hdy.ne']
  gcongr <;> nlinarith

private theorem cot_normalized_mono (n : ℕ) {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1/4) :
    2*quarticCotTerm n x/x+quarticCotCurvatureTerm n x ≤
      2*quarticCotTerm n y/y+quarticCotCurvatureTerm n y := by
  have hy0 : 0 < y := hx.trans_le hxy
  have hk : (1:ℝ) ≤ ((n:ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  have hdy : 0 < ((n:ℝ)+1)^2-y^2 := by nlinarith
  have hs := pow_le_pow_left₀ hx.le hxy 2
  have he (t : ℝ) (ht : t ≠ 0) :
      2*quarticCotTerm n t/t = 4/(((n:ℝ)+1)^2-t^2) := by
    unfold quarticCotTerm
    field_simp
    norm_num
  rw [he x hx.ne',he y hy0.ne']
  apply add_le_add _ (cot_curvature_mono n hx.le hxy hy)
  gcongr

private theorem quarticSlope_quarter : quarticLogSincSlope (1/4) = Real.pi-4 := by
  unfold quarticLogSincSlope
  rw [show Real.pi*((1:ℝ)/4)=Real.pi/4 by ring,Real.sin_pi_div_four,Real.cos_pi_div_four]
  field_simp

private theorem quarticCurvature_quarter : quarticLogSincCurvature (1/4) = 16-2*Real.pi^2 := by
  have hs : Real.sin (Real.pi/4)^2 = 1/2 := by
    have hh := Real.cos_two_mul_eq_one_sub (Real.pi/4)
    rw [show 2*(Real.pi/4)=Real.pi/2 by ring,Real.cos_pi_div_two] at hh
    linarith
  unfold quarticLogSincCurvature
  rw [show Real.pi*((1:ℝ)/4)=Real.pi/4 by ring,hs]
  ring

/-- Both curvature bounds come from the same positive cotangent series. -/
theorem quarticLogSinc_curvature_bounds {y : ℝ} (hy : 0 < y) (hycap : y ≤ 1/4) :
    -4 ≤ quarticLogSincCurvature y ∧ quarticLogSincCurvature y ≤ -Real.pi^2/3 := by
  have hyhalf : y < 1/2 := by linarith
  have h0 := quarticCotCurvatureTerm_zero_hasSum.summable
  have hY := quarticCotCurvatureTerm_summable hy hyhalf
  have hQ := quarticCotCurvatureTerm_summable (by norm_num : (0:ℝ)<1/4) (by norm_num : (1:ℝ)/4<1/2)
  have hlo := h0.tsum_le_tsum (fun n => cot_curvature_mono n le_rfl hy.le hycap) hY
  have hhi := hY.tsum_le_tsum (fun n => cot_curvature_mono n hy.le hycap le_rfl) hQ
  rw [quarticCotCurvatureTerm_tsum_zero] at hlo
  have ey := quarticLogSincCurvature_eq_neg_tsum hy hyhalf
  have eq := quarticLogSincCurvature_eq_neg_tsum (by norm_num : (0:ℝ)<1/4) (by norm_num : (1:ℝ)/4<1/2)
  rw [quarticCurvature_quarter] at eq
  constructor
  · nlinarith [Real.pi_lt_d4,Real.pi_pos]
  · linarith

theorem quarticLogSinc_perspective_curvature {y : ℝ} (hy : 0 < y) (hycap : y ≤ 1/4) :
    0 ≤ 2*quarticLogSincSlope y+y*quarticLogSincCurvature y+(43/4)*y := by
  have hsum (t : ℝ) (ht : 0 < t) (htcap : t ≤ 1/4) :
      Summable (fun n => 2*quarticCotTerm n t/t+quarticCotCurvatureTerm n t) :=
    ((quarticCotTerm_summable ht (by linarith)).mul_left 2 |>.div_const t).add
      (quarticCotCurvatureTerm_summable ht (by linarith))
  have hid (t : ℝ) (ht : 0 < t) (htcap : t ≤ 1/4) :
      (∑' n : ℕ, (2*quarticCotTerm n t/t+quarticCotCurvatureTerm n t)) =
        -2*quarticLogSincSlope t/t-quarticLogSincCurvature t := by
    rw [Summable.tsum_add (((quarticCotTerm_summable ht (by linarith)).mul_left 2).div_const t)
      (quarticCotCurvatureTerm_summable ht (by linarith)),tsum_div_const,tsum_mul_left,
      quarticLogSincSlope_eq_neg_tsum ht (by linarith),
      quarticLogSincCurvature_eq_neg_tsum ht (by linarith)]
    ring
  have hh := (hsum y hy hycap).tsum_le_tsum
    (fun n => cot_normalized_mono n hy hycap le_rfl)
    (hsum (1/4) (by norm_num) le_rfl)
  rw [hid y hy hycap,hid (1/4) (by norm_num) le_rfl,
    quarticSlope_quarter,quarticCurvature_quarter] at hh
  have hpi : -2*(Real.pi-4)/(1/4)-(16-2*Real.pi^2) ≤ (43:ℝ)/4 := by
    nlinarith [Real.pi_lt_d4,Real.pi_gt_d4]
  have hb := hh.trans hpi
  have hm := mul_le_mul_of_nonneg_right hb hy.le
  field_simp at hm
  nlinarith

theorem quarticSineDeficit_lower {n : ℕ} (hn : 5 ≤ n) {w : Fin n → ℝ}
    (hw : ∀ i, 0 < w i) (hcap : ∀ i, w i ≤ 1/4) (hW : ∑ i, w i = 1) :
    ((∑ i, let u := (n:ℝ)*w i; (u*Real.log u-u+1) -
      (43/24)*(u-1)^2*(u+2)/(n:ℝ)^2)/(n:ℝ)) ≤ quarticSineDeficit w := by
  have hN : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  have hN5 : (5:ℝ) ≤ n := by exact_mod_cast hn
  let x : ℝ := 1/n
  let k : ℝ := 43/24
  let f : ℝ → ℝ := fun y => y*quarticLogSinc y+k*y^3
  let f' : ℝ → ℝ := fun y => quarticLogSinc y+y*quarticLogSincSlope y+3*k*y^2
  let f'' : ℝ → ℝ := fun y => 2*quarticLogSincSlope y+y*quarticLogSincCurvature y+6*k*y
  have hx : x ∈ Ioc (0:ℝ) (1/4) :=
    ⟨by dsimp [x]; positivity, (div_le_iff₀ hN).mpr (by linarith)⟩
  have hD (y : ℝ) (hy : y ∈ Ioc (0:ℝ) (1/4)) : HasDerivAt f (f' y) y := by
    convert ((hasDerivAt_id y).mul (quarticLogSinc_hasDerivAt hy.1 (by linarith [hy.2]))).add
      (((hasDerivAt_id y).pow 3).const_mul k) using 1 <;> dsimp [f,f'] <;> ring
  have hDD (y : ℝ) (hy : y ∈ Ioc (0:ℝ) (1/4)) : HasDerivAt f' (f'' y) y := by
    convert ((quarticLogSinc_hasDerivAt hy.1 (by linarith [hy.2])).add
      ((hasDerivAt_id y).mul (quarticLogSincSlope_hasDerivAt hy.1 (by linarith [hy.2])))).add
      (((hasDerivAt_id y).pow 2).const_mul (3*k)) using 1 <;> dsimp [f',f''] <;> ring
  have hconv : ConvexOn ℝ (Ioc (0:ℝ) (1/4)) f := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioc _ _)
      (fun y hy => (hD y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hD y (interior_subset hy)).hasDerivWithinAt)
      (fun y hy => (hDD y (interior_subset hy)).hasDerivWithinAt)
    intro y hy
    have hy' : y ∈ Ioc (0:ℝ) (1/4) := interior_subset hy
    simpa [f'',k,show (6:ℝ)*(43/24)=43/4 by norm_num] using quarticLogSinc_perspective_curvature hy'.1 hy'.2
  have htan (i : Fin n) : f x+f' x*(w i-x) ≤ f (w i) := by
    have hh := ACS12.concave_tangent_upper hconv.neg ⟨hw i,hcap i⟩ hx (hD x hx).neg
    change -f (w i) ≤ -f x+(-f' x)*(w i-x) at hh
    linarith
  have hbal : ∑ i : Fin n, (w i-x) = 0 := by
    simp [Finset.sum_sub_distrib,hW,x,Finset.sum_const,Finset.card_univ,Fintype.card_fin,hN.ne']
  have hsum : (n:ℝ)*f x ≤ ∑ i, f (w i) := by
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ:Finset (Fin n))) => htan i)
    simpa [Finset.sum_add_distrib,← Finset.mul_sum,hbal] using hh
  have hs (y : ℝ) (hy : y ∈ Ioc (0:ℝ) (1/4)) : 0 < Real.sin (Real.pi*y) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hy.1)
      (by nlinarith [Real.pi_pos,hy.2])
  have he (y : ℝ) (hy : y ∈ Ioc (0:ℝ) (1/4)) :
      f y = y*Real.log (Real.sin (Real.pi*y))-y*Real.log y+k*y^3 := by
    dsimp [f,quarticLogSinc]
    rw [Real.log_div (hs y hy).ne' hy.1.ne']
    ring
  have hFsum : (∑ i, f (w i)) =
      (∑ i, w i*Real.log (Real.sin (Real.pi*w i))) -
      (∑ i, w i*Real.log (w i)) + k*(∑ i, w i^3) := by
    simp_rw [he _ ⟨hw _,hcap _⟩]
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.mul_sum]
  have hFx : (n:ℝ)*f x = Real.log (Real.sin (Real.pi/n))+Real.log (n:ℝ)+k/(n:ℝ)^2 := by
    rw [he x hx]
    dsimp [x]
    rw [show Real.pi*(1/(n:ℝ))=Real.pi/n by ring,Real.log_div (by norm_num) hN.ne',Real.log_one]
    field_simp
    ring
  have hTerm (i : Fin n) :
      (((n:ℝ)*w i)*Real.log ((n:ℝ)*w i)-(n:ℝ)*w i+1-
        k*((n:ℝ)*w i-1)^2*((n:ℝ)*w i+2)/(n:ℝ)^2)/(n:ℝ) =
      w i*Real.log (w i)+w i*Real.log (n:ℝ)-w i+1/(n:ℝ)-k*w i^3+
        3*k*w i/(n:ℝ)^2-2*k/(n:ℝ)^3 := by
    rw [Real.log_mul hN.ne' (hw i).ne']
    field_simp
    ring
  have hL : ((∑ i, let u := (n:ℝ)*w i; (u*Real.log u-u+1) -
      k*(u-1)^2*(u+2)/(n:ℝ)^2)/(n:ℝ)) =
      (∑ i, w i*Real.log (w i))+Real.log (n:ℝ)-k*(∑ i,w i^3)+k/(n:ℝ)^2 := by
    calc
      _ = ∑ i, (w i*Real.log (w i)+w i*Real.log (n:ℝ)-w i+1/(n:ℝ)-k*w i^3+
          3*k*w i/(n:ℝ)^2-2*k/(n:ℝ)^3) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl (fun i _ => hTerm i)
      _ = _ := by
        simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.sum_mul,
          ← Finset.mul_sum,← Finset.sum_div,hW,Finset.sum_const,
          Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        field_simp
        ring
  change _ ≤ quarticSineDeficit w
  rw [show (43:ℝ)/24=k from rfl,hL]
  rw [hFsum,hFx] at hsum
  unfold quarticSineDeficit
  linarith

end ACS12.NativeCells

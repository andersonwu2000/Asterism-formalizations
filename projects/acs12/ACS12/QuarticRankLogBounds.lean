import ACS12.QuarticSineTangents
import ACS12.QuarticBaseTangent

namespace ACS12.NativeCells
open Set

noncomputable def quarticLogGauge (y : ℝ) : ℝ :=
  quarticPolyLog y+4*quarticLogSinc y-Real.log 45

noncomputable def quarticLogGaugeSlope (y : ℝ) : ℝ :=
  -2*y/(1-y^2)+22*y/(1+11*y^2)+4*quarticLogSincSlope y

noncomputable def quarticLogGaugeCurvature (y : ℝ) : ℝ :=
  -2*(1+y^2)/(1-y^2)^2+22*(1-11*y^2)/(1+11*y^2)^2+4*quarticLogSincCurvature y

theorem quarticLogGauge_eq_row {y : ℝ} (hy : 0 < y) (hycap : y ≤ 1/4) :
    quarticLogGauge y = Real.log (analyticRow 4 y⁻¹)+4*Real.log (Real.sin (Real.pi*y)) := by
  have hs : 0 < Real.sin (Real.pi*y) := Real.sin_pos_of_pos_of_lt_pi
    (mul_pos Real.pi_pos hy) (by nlinarith [Real.pi_pos])
  rw [quarticLogGauge,quarticLogSinc,Real.log_div hs.ne' hy.ne',quartic_log_row_inverse hy hycap]
  ring

theorem quarticLogGauge_hasDerivAt {y : ℝ} (hy : y ∈ Ioc (0:ℝ) (1/4)) :
    HasDerivAt quarticLogGauge (quarticLogGaugeSlope y) y := by
  exact ((quarticPolyLog_deriv ⟨hy.1.le,hy.2⟩).add
    ((quarticLogSinc_hasDerivAt hy.1 (by linarith [hy.2])).const_mul 4)).sub_const _

theorem quarticLogGaugeSlope_hasDerivAt {y : ℝ} (hy : y ∈ Ioc (0:ℝ) (1/4)) :
    HasDerivAt quarticLogGaugeSlope (quarticLogGaugeCurvature y) y := by
  have hsq : y^2 ≤ (1/4:ℝ)^2 := pow_le_pow_left₀ hy.1.le hy.2 2
  have hm : 0 < 1-y^2 := by nlinarith
  have hp : 0 < 1+11*y^2 := by positivity
  have hd := hasDerivAt_id y
  have hd2 := hd.pow 2
  have h1 := (hd.const_mul (-2)).div (hd2.const_sub 1) hm.ne'
  have h2 := (hd.const_mul 22).div ((hd2.const_mul 11).const_add 1) hp.ne'
  have h3 := (quarticLogSincSlope_hasDerivAt hy.1 (by linarith [hy.2])).const_mul 4
  convert (h1.add h2).add h3 using 1 <;> dsimp [quarticLogGaugeSlope,quarticLogGaugeCurvature] <;>
    field_simp <;> ring

theorem quarticLogGauge_curvature_le {y : ℝ} (hy : y ∈ Ioc (0:ℝ) (1/4)) :
    quarticLogGaugeCurvature y ≤ 7 := by
  have hsq : y^2 ≤ (1/4:ℝ)^2 := pow_le_pow_left₀ hy.1.le hy.2 2
  have hm : 0 < 1-y^2 := by nlinarith
  have hp : 0 < 1+11*y^2 := by positivity
  have h1 : -2*(1+y^2)/(1-y^2)^2 ≤ -2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hm)).mpr
    nlinarith [mul_nonneg (sq_nonneg y) (show 0 ≤ 3-y^2 by linarith)]
  have h2 : 22*(1-11*y^2)/(1+11*y^2)^2 ≤ 22 := by
    apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
    nlinarith [sq_nonneg y,sq_nonneg (y^2)]
  have h3 := (quarticLogSinc_curvature_bounds hy.1 hy.2).2
  unfold quarticLogGaugeCurvature
  nlinarith [Real.pi_gt_d4,Real.pi_pos]

theorem quarticLogGauge_mean_le {n : ℕ} (hn : 5 ≤ n) {w : Fin n → ℝ}
    (hw : ∀ i, 0 < w i) (hcap : ∀ i,w i ≤ 1/4) (hW : ∑ i,w i=1) :
    (∑ i,quarticLogGauge (w i))/(n:ℝ) ≤ quarticLogGauge (1/(n:ℝ))+
      (7/2)*(∑ i,(w i-1/(n:ℝ))^2)/(n:ℝ) := by
  have hN : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  have hN5 : (5:ℝ) ≤ n := by exact_mod_cast hn
  let x : ℝ := 1/n
  let f : ℝ → ℝ := fun y => quarticLogGauge y-(7/2)*(y-x)^2
  let f' : ℝ → ℝ := fun y => quarticLogGaugeSlope y-7*(y-x)
  have hx : x ∈ Ioc (0:ℝ) (1/4) :=
    ⟨by dsimp [x]; positivity,(div_le_iff₀ hN).mpr (by linarith)⟩
  have hd (y : ℝ) (hy : y ∈ Ioc (0:ℝ) (1/4)) : HasDerivAt f (f' y) y := by
    convert (quarticLogGauge_hasDerivAt hy).sub
      ((((hasDerivAt_id y).sub_const x).pow 2).const_mul (7/2)) using 1 <;> dsimp [f,f'] <;> ring
  have hdd (y : ℝ) (hy : y ∈ Ioc (0:ℝ) (1/4)) :
      HasDerivAt f' (quarticLogGaugeCurvature y-7) y := by
    simpa [f'] using (quarticLogGaugeSlope_hasDerivAt hy).sub (((hasDerivAt_id y).sub_const x).const_mul 7)
  have hc : ConcaveOn ℝ (Ioc (0:ℝ) (1/4)) f := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ioc _ _)
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt)
      (fun y hy => (hdd y (interior_subset hy)).hasDerivWithinAt)
    exact fun y hy => sub_nonpos.mpr (quarticLogGauge_curvature_le (interior_subset hy))
  have hh := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ:Finset (Fin n))) =>
    ACS12.concave_tangent_upper hc ⟨hw i,hcap i⟩ hx (hd x hx))
  have hb : (∑ i,(w i-x))=0 := by
    simp [Finset.sum_sub_distrib,hW,x,Finset.sum_const,Finset.card_univ,Fintype.card_fin,hN.ne']
  have hs : (∑ i,f (w i)) ≤ (n:ℝ)*f x := by
    simpa [Finset.sum_add_distrib,← Finset.mul_sum,hb] using hh
  dsimp [f] at hs
  rw [Finset.sum_sub_distrib,← Finset.mul_sum] at hs
  simp only [sub_self,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,sub_zero] at hs
  apply (div_le_iff₀ hN).mpr
  dsimp [x] at hs
  rw [add_mul,div_mul_cancel₀ _ hN.ne']
  nlinarith

theorem quarticLogSinc_mean_lower {n : ℕ} (hn : 5 ≤ n) {w : Fin n → ℝ}
    (hw : ∀ i,0<w i) (hcap : ∀ i,w i≤1/4) (hW : ∑ i,w i=1) :
    quarticLogSinc (1/(n:ℝ))-2*(∑ i,(w i-1/(n:ℝ))^2)/(n:ℝ) ≤
      (∑ i,quarticLogSinc (w i))/(n:ℝ) := by
  have hN : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  have hN5 : (5:ℝ) ≤ n := by exact_mod_cast hn
  let x : ℝ := 1/n
  let f : ℝ → ℝ := fun y => quarticLogSinc y+2*(y-x)^2
  let f' : ℝ → ℝ := fun y => quarticLogSincSlope y+4*(y-x)
  have hx : x ∈ Ioc (0:ℝ) (1/4) :=
    ⟨by dsimp [x]; positivity,(div_le_iff₀ hN).mpr (by linarith)⟩
  have hd (y : ℝ) (hy : y ∈ Ioc (0:ℝ) (1/4)) : HasDerivAt f (f' y) y := by
    convert (quarticLogSinc_hasDerivAt hy.1 (by linarith [hy.2])).add
      ((((hasDerivAt_id y).sub_const x).pow 2).const_mul 2) using 1 <;> dsimp [f,f'] <;> ring
  have hdd (y : ℝ) (hy : y ∈ Ioc (0:ℝ) (1/4)) :
      HasDerivAt f' (quarticLogSincCurvature y+4) y := by
    simpa [f'] using (quarticLogSincSlope_hasDerivAt hy.1 (by linarith [hy.2])).add
      (((hasDerivAt_id y).sub_const x).const_mul 4)
  have hc : ConvexOn ℝ (Ioc (0:ℝ) (1/4)) f := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioc _ _)
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt)
      (fun y hy => (hdd y (interior_subset hy)).hasDerivWithinAt)
    intro y hy
    have hy' := interior_subset hy
    linarith [(quarticLogSinc_curvature_bounds hy'.1 hy'.2).1]
  have ht (i : Fin n) : f x+f' x*(w i-x) ≤ f (w i) := by
    have hh := ACS12.concave_tangent_upper hc.neg ⟨hw i,hcap i⟩ hx (hd x hx).neg
    change -f (w i) ≤ -f x+(-f' x)*(w i-x) at hh
    linarith
  have hb : (∑ i,(w i-x))=0 := by
    simp [Finset.sum_sub_distrib,hW,x,Finset.sum_const,Finset.card_univ,Fintype.card_fin,hN.ne']
  have hs : (n:ℝ)*f x ≤ ∑ i,f (w i) := by
    have hh := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ:Finset (Fin n))) => ht i)
    simpa [Finset.sum_add_distrib,← Finset.mul_sum,hb] using hh
  dsimp [f] at hs
  rw [Finset.sum_add_distrib,← Finset.mul_sum] at hs
  simp only [sub_self,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,add_zero] at hs
  apply (le_div_iff₀ hN).mpr
  dsimp [x] at hs
  rw [sub_mul,div_mul_cancel₀ _ hN.ne']
  nlinarith

theorem quarticLogSin_mean_lower {n : ℕ} (hn : 5 ≤ n) {w : Fin n → ℝ}
    (hw : ∀ i,0<w i) (hcap : ∀ i,w i≤1/4) (hW : ∑ i,w i=1) :
    Real.log (Real.sin (Real.pi/n))+(∑ i,Real.log ((n:ℝ)*w i))/(n:ℝ)-
      2*(∑ i,(w i-1/(n:ℝ))^2)/(n:ℝ) ≤ (∑ i,Real.log (Real.sin (Real.pi*w i)))/(n:ℝ) := by
  have hN : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  have hN5 : (5:ℝ) ≤ n := by exact_mod_cast hn
  have hs (i : Fin n) : 0 < Real.sin (Real.pi*w i) := Real.sin_pos_of_pos_of_lt_pi
    (mul_pos Real.pi_pos (hw i)) (by nlinarith [Real.pi_pos,hcap i])
  have hsx : 0 < Real.sin (Real.pi/n) := Real.sin_pos_of_pos_of_lt_pi (by positivity)
    ((div_lt_iff₀ hN).mpr (by nlinarith [Real.pi_pos]))
  have hh := quarticLogSinc_mean_lower hn hw hcap hW
  unfold quarticLogSinc at hh
  simp_rw [Real.log_div (hs _).ne' (hw _).ne'] at hh
  rw [show Real.pi*(1/(n:ℝ))=Real.pi/n by ring,Real.log_div hsx.ne' (by positivity),
    Real.log_div (by norm_num) hN.ne',Real.log_one,Finset.sum_sub_distrib] at hh
  simp_rw [Real.log_mul hN.ne' (hw _).ne']
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp at hh ⊢
  nlinarith

end ACS12.NativeCells

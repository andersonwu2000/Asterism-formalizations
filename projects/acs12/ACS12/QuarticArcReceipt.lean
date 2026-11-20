import ACS12.QuarticRankGeometry
import CenteredCircle.LaplaceSampling
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! A fixed square for the two intervening arcs and its logarithmic comparison. -/
namespace ACS12.NativeCells

open Set Filter MeasureTheory Finset
open CenteredCircle.AllN (integral_strict_of_ae_lt)
open scoped Topology

private noncomputable def arcLogSlope (y : ℝ) :=
  Real.pi*Real.cos (Real.pi*y)/Real.sin (Real.pi*y)

private theorem arcLog_deriv {y : ℝ} (hy : y ∈ Ioo (0:ℝ) 1) :
    HasDerivAt quarticArcLog (arcLogSlope y) y := by
  have h := (((hasDerivAt_id y).const_mul Real.pi).sin).log (quarticArcSin_pos hy).ne'
  convert h using 1
  simp only [arcLogSlope,id_eq,mul_one,mul_comm]

private theorem arcLogSlope_deriv {y : ℝ} (hy : y ∈ Ioo (0:ℝ) 1) :
    HasDerivAt arcLogSlope (-Real.pi^2/Real.sin (Real.pi*y)^2) y := by
  have hPi := (hasDerivAt_id y).const_mul Real.pi
  have h := (hPi.cos.const_mul Real.pi).div hPi.sin (quarticArcSin_pos hy).ne'
  convert h using 1
  simp only [id_eq,mul_one]
  have hE : Real.pi*(-Real.sin (Real.pi*y)*Real.pi)*Real.sin (Real.pi*y) -
      Real.pi*Real.cos (Real.pi*y)*(Real.cos (Real.pi*y)*Real.pi) = -Real.pi^2 := by
    linear_combination -(Real.pi^2)*Real.sin_sq_add_cos_sq (Real.pi*y)
  rw [hE]

private noncomputable def arcBlend (T I J : ℝ) (z : ℝ × ℝ) : ℝ := T+I*z.1+J*z.2

private noncomputable def arcKernel (T I J : ℝ) (z : ℝ × ℝ) : ℝ :=
  Real.pi^2/Real.sin (Real.pi*arcBlend T I J z)^2

private abbrev arcSide : Set ℝ := Icc (0:ℝ) 1

private noncomputable abbrev arcInterval : Measure ℝ := volume.restrict (Ioc (0:ℝ) 1)

private noncomputable abbrev arcSquare : Measure (ℝ × ℝ) := arcInterval.prod arcInterval

private theorem arcBlend_mem {T I J : ℝ} (hT : 0 < T) (hI : 0 ≤ I) (hJ : 0 ≤ J)
    (hS : 2*T+I+J=1) {z : ℝ × ℝ} (hz : z ∈ arcSide ×ˢ arcSide) :
    arcBlend T I J z ∈ Ioo (0:ℝ) 1 := by
  have hLo := mul_nonneg hI hz.1.1
  have hHi := mul_le_of_le_one_right hI hz.1.2
  have hLo' := mul_nonneg hJ hz.2.1
  have hHi' := mul_le_of_le_one_right hJ hz.2.2
  change 0 < T+I*z.1+J*z.2 ∧ T+I*z.1+J*z.2 < 1
  constructor <;> linarith only [hT,hS,hLo,hHi,hLo',hHi']

private theorem arcSquare_ae : ∀ᵐ z ∂arcSquare, z ∈ arcSide ×ˢ arcSide := by
  have h : ∀ᵐ z : ℝ × ℝ ∂arcSquare, z.1 ∈ Set.Ioc (0:ℝ) 1 ∧ z.2 ∈ Set.Ioc (0:ℝ) 1 :=
    (Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)).and
      (Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc))
  filter_upwards [h] with z hz
  exact ⟨⟨hz.1.1.le,hz.1.2⟩,⟨hz.2.1.le,hz.2.2⟩⟩

private theorem arcSquare_integrable {f : ℝ × ℝ → ℝ} (hf : ContinuousOn f (arcSide ×ˢ arcSide)) :
    Integrable f arcSquare := by
  rw [arcSquare,Measure.prod_restrict]
  apply (hf.integrableOn_compact (μ := (volume : Measure ℝ).prod volume)
    (isCompact_Icc.prod isCompact_Icc)).mono_set
  exact prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self

private theorem arcKernel_continuousOn {T I J : ℝ} (hT : 0 < T) (hI : 0 ≤ I) (hJ : 0 ≤ J)
    (hS : 2*T+I+J=1) : ContinuousOn (arcKernel T I J) (arcSide ×ˢ arcSide) := by
  unfold arcKernel arcBlend
  apply continuousOn_const.div (by fun_prop)
  exact fun z hz => pow_ne_zero _ (quarticArcSin_pos (arcBlend_mem hT hI hJ hS hz)).ne'

private theorem arcKernel_integral_pos {T I J : ℝ} (hT : 0 < T) (hI : 0 ≤ I) (hJ : 0 ≤ J)
    (hS : 2*T+I+J=1) : 0 < ∫ z, arcKernel T I J z ∂arcSquare := by
  have hμ : arcSquare Set.univ = 1 := by
    rw [← Set.univ_prod_univ,Measure.prod_prod]
    simp [arcInterval,Measure.restrict_apply,Real.volume_Ioc]
  letI : NeZero arcSquare := ⟨fun h => by simp [h] at hμ⟩
  have h := integral_strict_of_ae_lt arcSquare (integrable_zero _ _ _)
    (arcSquare_integrable (arcKernel_continuousOn hT hI hJ hS)) (by
      filter_upwards [arcSquare_ae] with z hz
      have hSin := quarticArcSin_pos (arcBlend_mem hT hI hJ hS hz)
      exact div_pos (sq_pos_of_pos Real.pi_pos) (sq_pos_of_pos hSin))
  simpa only [integral_zero] using h

private theorem arcKernel_integral_identity {T I J : ℝ} (hT : 0 < T) (hI : 0 < I) (hJ : 0 < J)
    (hS : 2*T+I+J=1) :
    I*J*(∫ z, arcKernel T I J z ∂arcSquare) = 2*(quarticArcLog (T+I)-quarticArcLog T) := by
  let K := arcKernel T I J
  have hK := arcKernel_continuousOn hT hI.le hJ.le hS
  have hMem : ∀ z ∈ arcSide ×ˢ arcSide, arcBlend T I J z ∈ Ioo (0:ℝ) 1 :=
    fun z hz => arcBlend_mem hT hI.le hJ.le hS hz
  have hInner (x : ℝ) (hx : x ∈ arcSide) :
      J*(∫ y, K (x,y) ∂arcInterval) = arcLogSlope (T+I*x)-arcLogSlope (T+I*x+J) := by
    let F (y : ℝ) := -arcLogSlope (arcBlend T I J (x,y))
    have hD (y : ℝ) (hy : y ∈ uIcc (0:ℝ) 1) : HasDerivAt F (J*K (x,y)) y := by
      rw [Set.uIcc_of_le zero_le_one] at hy
      have hArg := ((hasDerivAt_id y).const_mul J).const_add (T+I*x)
      have h := ((arcLogSlope_deriv (hMem (x,y) ⟨hx,hy⟩)).neg.comp y hArg)
      convert h using 1
      simp only [K,arcKernel,arcBlend,mul_one,neg_div,neg_neg]
      ring
    have hI' : IntervalIntegrable (fun y => J*K (x,y)) volume 0 1 :=
      ((hK.comp (by fun_prop : ContinuousOn (fun y : ℝ => (x,y)) arcSide)
        (fun y hy => ⟨hx,hy⟩)).const_mul J).intervalIntegrable_of_Icc zero_le_one
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hD hI'
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_of_le zero_le_one] at h
    simpa [F,arcBlend,sub_eq_add_neg,add_comm] using h
  let S (x : ℝ) := arcLogSlope (T+I*x)-arcLogSlope (T+I*x+J)
  have hInt : (∫ z, K z ∂arcSquare) = ∫ x, S x / J ∂arcInterval := by
    rw [integral_prod _ (arcSquare_integrable hK)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    have h := hInner x ⟨hx.1.le,hx.2⟩
    apply (eq_div_iff hJ.ne').mpr
    simpa only [mul_comm, S] using h
  let F (x : ℝ) := quarticArcLog (T+I*x) - quarticArcLog (T+I*x+J)
  have hD (x : ℝ) (hx : x ∈ uIcc (0:ℝ) 1) : HasDerivAt F (I*S x) x := by
    rw [Set.uIcc_of_le zero_le_one] at hx
    have h0 : T+I*x ∈ Ioo (0:ℝ) 1 := by simpa [arcBlend] using hMem (x,0) ⟨hx,by norm_num [arcSide]⟩
    have h1 : T+I*x+J ∈ Ioo (0:ℝ) 1 := by simpa [arcBlend] using hMem (x,1) ⟨hx,by norm_num [arcSide]⟩
    have hA := ((hasDerivAt_id x).const_mul I).const_add T
    have h0' := (arcLog_deriv h0).comp x hA
    have h1' := (arcLog_deriv h1).comp x (hA.add_const J)
    convert h0'.sub h1' using 1
    simp only [S,mul_one]
    ring
  have hC (x : ℝ) (hx : x ∈ arcSide) : ContinuousWithinAt (fun z => I*S z) arcSide x := by
    have h0 : T+I*x ∈ Ioo (0:ℝ) 1 := by simpa [arcBlend] using hMem (x,0) ⟨hx,by norm_num [arcSide]⟩
    have h1 : T+I*x+J ∈ Ioo (0:ℝ) 1 := by simpa [arcBlend] using hMem (x,1) ⟨hx,by norm_num [arcSide]⟩
    have hA := ((hasDerivAt_id x).const_mul I).const_add T
    have h0' := (arcLogSlope_deriv h0).comp x hA
    have h1' := (arcLogSlope_deriv h1).comp x (hA.add_const J)
    have hD := ((h0'.sub h1').const_mul I).continuousAt.continuousWithinAt (s := arcSide)
    exact hD
  have hSInt : IntervalIntegrable (fun x => I*S x) volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc zero_le_one hC
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hD hSInt
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_of_le zero_le_one] at h
  rw [hInt,integral_div,show I*J*((∫ x, S x ∂arcInterval)/J) = I*(∫ x,S x ∂arcInterval) by
    field_simp [hJ.ne'], h]
  have hEq1 : T+I+J=1-T := by linarith only [hS]
  have hEq2 : T+J=1-(T+I) := by linarith only [hS]
  simp only [F,mul_zero,mul_one,add_zero,hEq1,hEq2,quarticArcLog_complement]
  ring

private theorem arcLogBlend_continuousOn {T I J : ℝ} (hT : 0<T) (hI : 0≤I) (hJ : 0≤J) (hS : 2*T+I+J=1) :
    ContinuousOn (fun z => quarticArcLog (arcBlend T I J z)) (arcSide ×ˢ arcSide) := by
  unfold quarticArcLog arcBlend
  apply ContinuousOn.log (by fun_prop)
  intro z hz
  exact (quarticArcSin_pos (arcBlend_mem hT hI hJ hS hz)).ne'

private theorem arcKernel_log_ratio {T I J T₀ I₀ J₀ : ℝ}
    (hT : 0 < T) (hI : 0 < I) (hJ : 0 < J) (hS : 2*T+I+J=1)
    (hT₀ : 0 < T₀) (hI₀ : 0 < I₀) (hJ₀ : 0 < J₀) (hS₀ : 2*T₀+I₀+J₀=1)
    {g g₀ : ℝ} (hg : quarticArcLog (T+I)-quarticArcLog T ≤ g)
    (hg₀ : g₀ = quarticArcLog (T₀+I₀)-quarticArcLog T₀) :
    let A := arcKernel T₀ I₀ J₀
    let D := ∫ z, A z ∂arcSquare
    let F (z : ℝ × ℝ) := A z*(quarticArcLog (arcBlend T₀ I₀ J₀ z)-quarticArcLog (arcBlend T I J z))
    0 < g ∧ 0 < g₀ ∧
      Real.log (I/I₀)+Real.log (J/J₀)+(2/D)*(∫ z, F z ∂arcSquare) ≤ Real.log (g/g₀) := by
  let A := arcKernel T₀ I₀ J₀
  let B := arcKernel T I J
  let D := ∫ z, A z ∂arcSquare
  let E := ∫ z, B z ∂arcSquare
  let F (z : ℝ × ℝ) := A z*(quarticArcLog (arcBlend T₀ I₀ J₀ z)-quarticArcLog (arcBlend T I J z))
  have hD : 0 < D := arcKernel_integral_pos hT₀ hI₀.le hJ₀.le hS₀
  have hE : 0 < E := arcKernel_integral_pos hT hI.le hJ.le hS
  have hEA : 0 < E/D := div_pos hE hD
  have hA := arcKernel_continuousOn hT₀ hI₀.le hJ₀.le hS₀
  have hB := arcKernel_continuousOn hT hI.le hJ.le hS
  have hAint : Integrable A arcSquare := arcSquare_integrable hA
  have hBint : Integrable B arcSquare := arcSquare_integrable hB
  have hFint : Integrable F arcSquare := arcSquare_integrable
    (hA.mul ((arcLogBlend_continuousOn hT₀ hI₀.le hJ₀.le hS₀).sub (arcLogBlend_continuousOn hT hI.le hJ.le hS)))
  have hJensen : (2/D)*(∫ z, F z ∂arcSquare) ≤ Real.log (E/D) := by
    have hBound (z : ℝ × ℝ) (hz : z ∈ arcSide ×ˢ arcSide) :
        2*F z ≤ (D/E)*B z + (Real.log (E/D)-1)*A z := by
      have hs₀ := quarticArcSin_pos (arcBlend_mem hT₀ hI₀.le hJ₀.le hS₀ hz)
      have hs := quarticArcSin_pos (arcBlend_mem hT hI.le hJ.le hS hz)
      have hA₀ : 0 < A z := div_pos (sq_pos_of_pos Real.pi_pos) (sq_pos_of_pos hs₀)
      have hB₀ : 0 < B z := div_pos (sq_pos_of_pos Real.pi_pos) (sq_pos_of_pos hs)
      have hRatio : Real.log (B z/A z) =
          2*(quarticArcLog (arcBlend T₀ I₀ J₀ z)-quarticArcLog (arcBlend T I J z)) := by
        rw [Real.log_div hB₀.ne' hA₀.ne']
        unfold A B arcKernel quarticArcLog
        rw [Real.log_div (pow_ne_zero _ Real.pi_ne_zero) (pow_ne_zero _ hs.ne'),
          Real.log_div (pow_ne_zero _ Real.pi_ne_zero) (pow_ne_zero _ hs₀.ne')]
        simp only [Real.log_pow, Nat.cast_ofNat]
        ring
      have h := Real.log_le_sub_one_of_pos (div_pos (div_pos hB₀ hA₀) hEA)
      rw [Real.log_div (div_pos hB₀ hA₀).ne' hEA.ne', hRatio] at h
      have h' := mul_le_mul_of_nonneg_right h hA₀.le
      have hEq : (B z/A z/(E/D)-1)*A z = (D/E)*B z-A z := by
        field_simp [hA₀.ne',hE.ne',hD.ne']
      rw [hEq] at h'
      unfold F
      linarith only [h']
    have h := integral_mono_ae (hFint.const_mul 2) ((hBint.const_mul (D/E)).add
      (hAint.const_mul (Real.log (E/D)-1))) (by
        filter_upwards [arcSquare_ae] with z hz using hBound z hz)
    change (∫ z, 2*F z ∂arcSquare) ≤ ∫ z, (D/E)*B z+(Real.log (E/D)-1)*A z ∂arcSquare at h
    rw [integral_const_mul,integral_add (hBint.const_mul _) (hAint.const_mul _),integral_const_mul,integral_const_mul] at h
    change 2*(∫ z, F z ∂arcSquare) ≤ (D/E)*E+(Real.log (E/D)-1)*D at h
    rw [div_mul_cancel₀ _ hE.ne'] at h
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hD).mpr (by linarith only [h])
  have hBactual := arcKernel_integral_identity hT hI hJ hS
  change I*J*E = _ at hBactual
  have hBreg := arcKernel_integral_identity hT₀ hI₀ hJ₀ hS₀
  change I₀*J₀*D = _ at hBreg
  rw [← hg₀] at hBreg
  have hgPos : 0 < g := by linarith only [hg,hBactual,mul_pos (mul_pos hI hJ) hE]
  have hg₀Pos : 0 < g₀ := by linarith only [hBreg,mul_pos (mul_pos hI₀ hJ₀) hD]
  refine ⟨hgPos,hg₀Pos,?_⟩
  have hComp : (I/I₀)*(J/J₀)*(E/D) ≤ g/g₀ := by
    have hId : (I/I₀)*(J/J₀)*(E/D) = (I*J*E)/(I₀*J₀*D) := by ring
    rw [hId,hBreg]
    have h := div_le_div_of_nonneg_right (show I*J*E ≤ 2*g by linarith only [hBactual,hg])
      (show 0 ≤ 2*g₀ by positivity)
    exact h.trans_eq (by field_simp [hg₀Pos.ne'])
  have hC := Real.log_le_log (mul_pos (mul_pos (div_pos hI hI₀) (div_pos hJ hJ₀)) hEA) hComp
  rw [Real.log_mul (mul_pos (div_pos hI hI₀) (div_pos hJ hJ₀)).ne' hEA.ne',
    Real.log_mul (div_pos hI hI₀).ne' (div_pos hJ hJ₀).ne'] at hC
  linarith only [hC,hJensen]

/-- The fixed regular kernel has a nonnegative total logarithmic displacement
because the cyclic mean of every affine input is its regular input. -/
theorem quarticInterveningArc_log_receipt {n : ℕ} [NeZero n] {T I J g : Fin n → ℝ}
    {T₀ I₀ J₀ g₀ : ℝ} (hT : ∀ i, 0 < T i) (hI : ∀ i, 0 < I i) (hJ : ∀ i, 0 < J i)
    (hS : ∀ i, 2*T i+I i+J i=1)
    (hT₀ : 0 < T₀) (hI₀ : 0 < I₀) (hJ₀ : 0 < J₀) (hS₀ : 2*T₀+I₀+J₀=1)
    (hMeanT : (∑ i,T i)=(n:ℝ)*T₀) (hMeanI : (∑ i,I i)=(n:ℝ)*I₀)
    (hMeanJ : (∑ i,J i)=(n:ℝ)*J₀)
    (hg : ∀ i, quarticArcLog (T i+I i)-quarticArcLog (T i) ≤ g i)
    (hg₀ : g₀=quarticArcLog (T₀+I₀)-quarticArcLog T₀) :
    (∀ i, 0 < g i) ∧
      (∑ i, Real.log (I i/I₀))+(∑ i, Real.log (J i/J₀)) ≤ ∑ i, Real.log (g i/g₀) := by
  let A := arcKernel T₀ I₀ J₀
  let D := ∫ z, A z ∂arcSquare
  let F (i : Fin n) (z : ℝ × ℝ) := A z*(quarticArcLog (arcBlend T₀ I₀ J₀ z)-
    quarticArcLog (arcBlend (T i) (I i) (J i) z))
  have hD : 0 < D := arcKernel_integral_pos hT₀ hI₀.le hJ₀.le hS₀
  have hA := arcKernel_continuousOn hT₀ hI₀.le hJ₀.le hS₀
  have hFInt (i : Fin n) : Integrable (F i) arcSquare := arcSquare_integrable
    (hA.mul ((arcLogBlend_continuousOn hT₀ hI₀.le hJ₀.le hS₀).sub (arcLogBlend_continuousOn (hT i) (hI i).le (hJ i).le (hS i))))
  have hEach (i : Fin n) := arcKernel_log_ratio (hT i) (hI i) (hJ i) (hS i) hT₀ hI₀ hJ₀ hS₀ (hg i) hg₀
  refine ⟨fun i => (hEach i).1,?_⟩
  have hSum (z : ℝ × ℝ) : (∑ i : Fin n,arcBlend (T i) (I i) (J i) z) = (n:ℝ)*arcBlend T₀ I₀ J₀ z := by
    unfold arcBlend
    simp only [sum_add_distrib,← sum_mul,hMeanT,hMeanI,hMeanJ]
    ring
  have hN : 0 < (n:ℝ) := Nat.cast_pos.mpr (NeZero.pos n)
  have hDisplacement (z : ℝ × ℝ) (hz : z ∈ arcSide ×ˢ arcSide) : 0 ≤ ∑ i,F i z := by
    let p (i : Fin n) := arcBlend (T i) (I i) (J i) z
    have h := quarticArcLog_concave.le_map_sum (t := (univ : Finset (Fin n)))
      (w := fun _ => 1/(n:ℝ)) (p := p)
      (fun _ _ => (one_div_pos.mpr hN).le)
      (by simp [nsmul_eq_mul])
      (fun i _ => arcBlend_mem (hT i) (hI i).le (hJ i).le (hS i) hz)
    simp only [smul_eq_mul,one_div_mul_eq_div,← sum_div,p] at h
    rw [hSum z,mul_div_cancel_left₀ _ hN.ne'] at h
    have hL := (div_le_iff₀ hN).mp h
    unfold F
    rw [← mul_sum,sum_sub_distrib,sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    exact mul_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)) (sub_nonneg.mpr (by simpa [mul_comm] using hL))
  have hJensen : 0 ≤ ∑ i, ∫ z, F i z ∂arcSquare := by
    rw [← integral_finsetSum _ (fun i _ => hFInt i)]
    apply integral_nonneg_of_ae
    filter_upwards [arcSquare_ae] with z hz using hDisplacement z hz
  have hPrice := sum_le_sum (s := (univ : Finset (Fin n))) (fun i _ => (hEach i).2.2)
  change (∑ i, (Real.log (I i/I₀)+Real.log (J i/J₀)+(2/D)*(∫ z, F i z ∂arcSquare))) ≤ _ at hPrice
  rw [sum_add_distrib,sum_add_distrib,← mul_sum] at hPrice
  have hNonneg : 0 ≤ (2/D)*(∑ i, ∫ z, F i z ∂arcSquare) :=
    mul_nonneg (div_nonneg (by norm_num) hD.le) hJensen
  linarith only [hPrice,hNonneg]

end ACS12.NativeCells

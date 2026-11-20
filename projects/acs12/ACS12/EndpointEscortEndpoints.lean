import ACS12.EndpointEscortAtom
import ACS12.AffineEscortLogGuards
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! The two endpoints of the common escort: total-exponent monotonicity and a log chord. -/
namespace ACS12.NativeCells
open Set
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

noncomputable def endpointK : ℝ := 2/7
private noncomputable def endpointG (a : ℝ) := Real.log (a^2+endpointK^2)
private noncomputable def endpointG1 (a : ℝ) := 2*a/(a^2+endpointK^2)
private noncomputable def endpointG2 (a : ℝ) := 2*(endpointK^2-a^2)/(a^2+endpointK^2)^2
private noncomputable def endpointG3 (a : ℝ) := 4*a*(a^2-3*endpointK^2)/(a^2+endpointK^2)^3

private theorem endpointG_deriv (a : ℝ) : HasDerivAt endpointG (endpointG1 a) a := by
  have h:=(((hasDerivAt_id a).pow 2).add_const (endpointK^2)).log
    (show a^2+endpointK^2≠0 by unfold endpointK;positivity)
  convert h using 1
  simp only [endpointG1,Pi.pow_apply,id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one]

private theorem endpointG1_deriv (a : ℝ) : HasDerivAt endpointG1 (endpointG2 a) a := by
  have h:=((hasDerivAt_id a).const_mul 2).div (((hasDerivAt_id a).pow 2).add_const (endpointK^2))
    (show a^2+endpointK^2≠0 by unfold endpointK;positivity)
  convert h using 1
  simp only [endpointG2,Pi.pow_apply,id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul]
  field_simp [show a^2+endpointK^2≠0 by unfold endpointK;positivity]
  <;>ring

private theorem endpointG2_deriv (a : ℝ) : HasDerivAt endpointG2 (endpointG3 a) a := by
  have h:=((((hasDerivAt_id a).pow 2).const_sub (endpointK^2)).const_mul 2).div
    ((((hasDerivAt_id a).pow 2).add_const (endpointK^2)).pow 2)
    (show (a^2+endpointK^2)^2≠0 by unfold endpointK;positivity)
  convert h using 1
  simp only [endpointG3,Pi.pow_apply,id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul]
  field_simp [show a^2+endpointK^2≠0 by unfold endpointK;positivity]
  <;>ring

noncomputable def endpointScalar (a : ℝ) : ℝ :=
  (a^2-a-endpointK)*Real.log a-(a^2-1)*Real.log (a-1)-
    endpointK*(a-2)/2*endpointG a+(endpointK+1)*(a-1)*Real.log endpointK+
    endpointK*(a-2)/2*Real.log 2+a*(a-endpointK)/2-(endpointK+1)
noncomputable def endpointScalar1 (a : ℝ) : ℝ :=
  (2*a-1)*Real.log a+(a^2-a-endpointK)/a-2*a*Real.log (a-1)-(a^2-1)/(a-1)-
    endpointK/2*endpointG a-endpointK*(a-2)/2*endpointG1 a+
    (endpointK+1)*Real.log endpointK+endpointK/2*Real.log 2+a-endpointK/2
noncomputable def endpointScalar2 (a : ℝ) : ℝ :=
  2*Real.log a+2*(2*a-1)/a-(a^2-a-endpointK)/a^2-
    2*Real.log (a-1)-4*a/(a-1)+(a^2-1)/(a-1)^2-
      endpointK*endpointG1 a-endpointK*(a-2)/2*endpointG2 a+1
noncomputable def endpointScalar3 (a : ℝ) : ℝ :=
  6/a-3*(2*a-1)/a^2+2*(a^2-a-endpointK)/a^3-
    6/(a-1)+6*a/(a-1)^2-2*(a^2-1)/(a-1)^3-
      3*endpointK/2*endpointG2 a-endpointK*(a-2)/2*endpointG3 a

theorem endpointScalar_deriv {a : ℝ} (ha : 1<a) :
    HasDerivAt endpointScalar (endpointScalar1 a) a := by
  have ha0 : a≠0:=by linarith only [ha]
  have ha1 : a-1≠0:=by linarith only [ha]
  have hI:=hasDerivAt_id a
  have hA:=((hI.pow 2).sub hI).sub_const endpointK
  have hB:=(hI.pow 2).sub_const 1
  have hC:=((hI.sub_const 2).const_mul endpointK).div_const 2
  have hL:=Real.hasDerivAt_log ha0
  have hH:=(hI.sub_const 1).log ha1
  have h:=((((((hA.mul hL).sub (hB.mul hH)).sub (hC.mul (endpointG_deriv a))).add
    ((hI.sub_const 1).const_mul ((endpointK+1)*Real.log endpointK))).add
      ((hI.sub_const 2).const_mul (endpointK/2*Real.log 2))).add
        ((hI.mul (hI.sub_const endpointK)).div_const 2)).sub_const (endpointK+1)
  convert h using 1 <;> (try funext x) <;>
    simp only [endpointScalar,endpointScalar1,endpointScalar2,endpointScalar3,
      Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.div_apply,Pi.pow_apply,id_eq,
      Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul] <;>
    field_simp [ha0,ha1] <;>ring
theorem endpointScalar1_deriv {a : ℝ} (ha : 1<a) :
    HasDerivAt endpointScalar1 (endpointScalar2 a) a := by
  have ha0 : a≠0:=by linarith only [ha]
  have ha1 : a-1≠0:=by linarith only [ha]
  have hI:=hasDerivAt_id a
  have hA:=((hI.pow 2).sub hI).sub_const endpointK
  have hB:=(hI.pow 2).sub_const 1
  have hC:=((hI.sub_const 2).const_mul endpointK).div_const 2
  have hL:=Real.hasDerivAt_log ha0
  have hH:=(hI.sub_const 1).log ha1
  have hA1:=(hI.const_mul 2).sub_const 1
  have hB1:=hI.const_mul 2
  have hL1:=hI.inv ha0
  have hH1:=(hI.sub_const 1).inv ha1
  have h:=(((((((((hA1.mul hL).add (hA.div hI ha0)).sub (hB1.mul hH)).sub
    (hB.div (hI.sub_const 1) ha1)).sub ((endpointG_deriv a).const_mul (endpointK/2))).sub
      (hC.mul (endpointG1_deriv a))).add_const ((endpointK+1)*Real.log endpointK)).add_const
        (endpointK/2*Real.log 2)).add hI).sub_const (endpointK/2)
  convert h using 1 <;> (try funext x) <;>
    simp only [endpointScalar,endpointScalar1,endpointScalar2,endpointScalar3,
      Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.div_apply,Pi.pow_apply,id_eq,
      Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul] <;>
    field_simp [ha0,ha1] <;>ring
theorem endpointScalar2_deriv {a : ℝ} (ha : 1<a) :
    HasDerivAt endpointScalar2 (endpointScalar3 a) a := by
  have ha0 : a≠0:=by linarith only [ha]
  have ha1 : a-1≠0:=by linarith only [ha]
  have hI:=hasDerivAt_id a
  have hA:=((hI.pow 2).sub hI).sub_const endpointK
  have hB:=(hI.pow 2).sub_const 1
  have hC:=((hI.sub_const 2).const_mul endpointK).div_const 2
  have hL:=Real.hasDerivAt_log ha0
  have hH:=(hI.sub_const 1).log ha1
  have hA1:=(hI.const_mul 2).sub_const 1
  have hL1:=hI.inv ha0
  have hH1:=(hI.sub_const 1).inv ha1
  have h:=((((((((hL.const_mul 2).add ((hA1.div hI ha0).const_mul 2)).sub
    (hA.div (hI.pow 2) (pow_ne_zero 2 ha0))).sub (hH.const_mul 2)).sub
      ((hI.div (hI.sub_const 1) ha1).const_mul 4)).add
        (hB.div ((hI.sub_const 1).pow 2) (pow_ne_zero 2 ha1))).sub
          ((endpointG1_deriv a).const_mul endpointK)).sub
            (hC.mul (endpointG2_deriv a))).add_const 1
  convert h using 1 <;> (try funext x) <;>
    simp only [endpointScalar,endpointScalar1,endpointScalar2,endpointScalar3,
      Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.div_apply,Pi.pow_apply,id_eq,
      Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul] <;>
    field_simp [ha0,ha1] <;>ring
noncomputable def endpointRemainder3 (a : ℝ) : ℝ :=
  endpointK^3*(3*a^5-24*a^4-6*a^3*endpointK^2-12*a^2*endpointK^2-a*endpointK^4-4*endpointK^4)/
    (a^3*(a^2+endpointK^2)^3)

theorem endpointScalar3_identity {a : ℝ} (ha : 1<a) :
    endpointScalar3 a=9*(a+2)/(7*a^3)+2*(2*a-1)/(a^3*(a-1)^2)+endpointRemainder3 a := by
  have ha0 : a≠0:=by linarith only [ha]
  have ha1 : a-1≠0:=by linarith only [ha]
  unfold endpointScalar3 endpointRemainder3 endpointG2 endpointG3
  field_simp [ha0,ha1,show a^2+endpointK^2≠0 by unfold endpointK;positivity]
  unfold endpointK
  ring

theorem endpointRemainder3_lower {a : ℝ} (ha : 2≤a) :
    -(1/2:ℝ)<a^3*endpointRemainder3 a := by
  let t:=a-2
  let C:=endpointK^3*(6+3*endpointK^2/2+3*endpointK^4/32)
  let Q:=29403*t^6/4802+183621*t^5/2401+44104722*t^4/117649+
    108142752*t^3/117649+6720203856*t^2/5764801+3956395136*t/5764801+
      34034150400/282475249
  have ht : 0≤t:=sub_nonneg.mpr ha
  have hQ : 0<Q:=by unfold Q;positivity
  have ha0 : a≠0:=by linarith only [ha]
  have hD : a^2+endpointK^2≠0:=by unfold endpointK;positivity
  have hId : a^3*endpointRemainder3 a+C=endpointK^3*Q/(a^2+endpointK^2)^3 := by
    unfold endpointRemainder3 C Q t
    field_simp [ha0,hD]
    unfold endpointK
    ring
  have hPos : 0<endpointK^3*Q/(a^2+endpointK^2)^3 := by unfold endpointK;positivity
  have hC : C<1/2 := by norm_num [C,endpointK]
  linarith only [hId,hPos,hC]

theorem endpointScalar3_lower {a : ℝ} (ha : 2≤a) : 8/a^3<endpointScalar3 a := by
  have ha₁ : 1<a:=by linarith only [ha]
  have ha0 : a≠0:=by linarith only [ha]
  have ha1 : a-1≠0:=by linarith only [ha]
  have hId : a^3*endpointScalar3 a-17/2-a^3*endpointRemainder3 a=
      ((a-3)^2*(18*(a-2)+25)+12*(a-2)+12)/(14*(a-1)^2) := by
    rw [endpointScalar3_identity ha₁]
    field_simp [ha0,ha1]
    ring
  have ht : 0≤a-2:=sub_nonneg.mpr ha
  have hPos : 0<((a-3)^2*(18*(a-2)+25)+12*(a-2)+12)/(14*(a-1)^2) := by positivity
  have hB:=endpointRemainder3_lower ha
  apply (div_lt_iff₀ (pow_pos (by linarith only [ha] : 0<a) 3)).mpr
  nlinarith only [hId,hPos,hB]

private theorem endpointScalar_initial :
    1/200<endpointScalar 2 ∧ 2/25<endpointScalar1 2 ∧ -(1/3:ℝ)<endpointScalar2 2 := by
  have hK : Real.log (2/7:ℝ)=Real.log 2-Real.log 7 := Real.log_div (by norm_num) (by norm_num)
  have hG : Real.log (200/49:ℝ)=3*Real.log 2+2*Real.log 5-2*Real.log 7 := by
    rw [show (200/49:ℝ)=2^3*5^2/7^2 by norm_num,
      Real.log_div (by norm_num) (by norm_num),Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow,Real.log_pow,Real.log_pow]
    norm_num
  have h0 : endpointScalar 2=(3+21*Real.log 2-9*Real.log 7)/7 := by
    norm_num [endpointScalar,endpointK,endpointG,hK,hG]
    ring
  have h1 : endpointScalar1 2= -Real.log 7-2*Real.log 5/7-2/7+4*Real.log 2 := by
    norm_num [endpointScalar1,endpointK,endpointG,endpointG1,hK,hG]
    ring
  have h2 : endpointScalar2 2= -299/175+2*Real.log 2 := by
    norm_num [endpointScalar2,endpointK,endpointG1,endpointG2]
    ring
  rw [h0,h1,h2]
  have hSeven:=affine_log_seven_bounds.2
  have hFive:=affine_log_five_bounds.2
  have hTwo:=Real.log_two_gt_d9
  constructor
  · linarith only [hSeven,hTwo]
  constructor <;> linarith only [hSeven,hFive,hTwo]

noncomputable def endpointSlopeBarrier (a : ℝ) := 2/25+2/3*(a-2)+4/a-2
private theorem endpointSlopeBarrier_deriv {a : ℝ} (ha : a≠0) :
    HasDerivAt endpointSlopeBarrier (2/3-4/a^2) a := by
  have h:=(((((hasDerivAt_id a).sub_const 2).const_mul (2/3)).const_add (2/25)).add
    (((hasDerivAt_id a).inv ha).const_mul 4)).sub_const 2
  convert h using 1 <;> simp only [endpointSlopeBarrier,id_eq,mul_one,one_mul] <;> field_simp [ha] <;>ring

private theorem endpointBarrierSecond_deriv {a : ℝ} (ha : a≠0) :
    HasDerivAt (fun a : ℝ=>2/3-4/a^2) (8/a^3) a := by
  have h:=((((hasDerivAt_id a).pow 2).inv (pow_ne_zero 2 ha)).const_mul 4).const_sub (2/3)
  convert h using 1
  simp only [id_eq,Pi.pow_apply,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul]
  field_simp [ha]
  <;>ring

theorem endpointScalar1_pos {a : ℝ} (ha : 2≤a) : 0<endpointScalar1 a := by
  have hFirst (x : ℝ) (hx : 2≤x) :
      HasDerivAt (fun x=>endpointScalar2 x-(2/3-4/x^2)) (endpointScalar3 x-8/x^3) x :=
    (endpointScalar2_deriv (by linarith only [hx])).sub
      (endpointBarrierSecond_deriv (by linarith only [hx]))
  have hMono : MonotoneOn (fun x=>endpointScalar2 x-(2/3-4/x^2)) (Ici 2) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · exact fun x hx=>(hFirst x hx).continuousAt.continuousWithinAt
    · exact fun x hx=>(hFirst x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hFirst x (interior_subset hx)).deriv]
      exact sub_nonneg.mpr (endpointScalar3_lower (interior_subset hx)).le
  have hPaid (x : ℝ) (hx : 2≤x) : 0<endpointScalar2 x-(2/3-4/x^2) := by
    have h:=hMono (by norm_num : (2:ℝ)∈Ici 2) hx hx
    norm_num at h
    linarith only [h,endpointScalar_initial.2.2]
  have hSecond (x : ℝ) (hx : 2≤x) :
      HasDerivAt (fun x=>endpointScalar1 x-endpointSlopeBarrier x)
        (endpointScalar2 x-(2/3-4/x^2)) x :=
    (endpointScalar1_deriv (by linarith only [hx])).sub
      (endpointSlopeBarrier_deriv (by linarith only [hx]))
  have hMono2 : MonotoneOn (fun x=>endpointScalar1 x-endpointSlopeBarrier x) (Ici 2) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · exact fun x hx=>(hSecond x hx).continuousAt.continuousWithinAt
    · exact fun x hx=>(hSecond x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hSecond x (interior_subset hx)).deriv]
      exact (hPaid x (interior_subset hx)).le
  have h:=hMono2 (by norm_num : (2:ℝ)∈Ici 2) ha ha
  norm_num [endpointSlopeBarrier] at h
  have ha0 : a≠0:=by linarith only [ha]
  have hId : a*endpointSlopeBarrier a=(2/3)*(a-61/25)^2+58/1875 := by
    unfold endpointSlopeBarrier
    field_simp [ha0]
    ring
  have hBarrier : 0<endpointSlopeBarrier a := by
    have hP : 0<(2/3)*(a-61/25)^2+58/1875:=by positivity
    have hPay : 0<a*endpointSlopeBarrier a:=hId.symm ▸ hP
    exact pos_of_mul_pos_right hPay (by linarith only [ha])
  dsimp only [endpointSlopeBarrier] at hBarrier
  linarith only [h,hBarrier,endpointScalar_initial.2.1]

theorem endpointScalar_pos {a : ℝ} (ha : 2≤a) : 0<endpointScalar a := by
  have hMono : MonotoneOn endpointScalar (Ici 2) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · intro x hx
      have hx' : 2≤x:=hx
      exact (endpointScalar_deriv (by linarith only [hx'])).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : 2≤x:=interior_subset hx
      exact (endpointScalar_deriv (by linarith only [hx'])).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : 2≤x:=interior_subset hx
      rw [(endpointScalar_deriv (by linarith only [hx'])).deriv]
      exact (endpointScalar1_pos hx').le
  exact (lt_trans (by norm_num : (0:ℝ)<1/200) endpointScalar_initial.1).trans_le
    (hMono (by norm_num : (2:ℝ)∈Ici 2) ha ha)

theorem endpointScalar_atom_identity {a : ℝ} (ha : 2≤a) :
    endpointScalar a=a*endpointEscortAtom (a+1) (endpointK/a) := by
  have ha₀ : 0<a:=by linarith only [ha]
  have ha₁ : 0<a-1:=by linarith only [ha]
  have hk : 0<endpointK:=by norm_num [endpointK]
  have hAk : a-endpointK≠0:=by norm_num [endpointK] at ha ⊢;linarith only [ha]
  have hC : endpointEscortCoefficient (a+1)=1/(a-endpointK) := by
    unfold endpointEscortCoefficient endpointK
    congr 2
    ring
  have hRho : endpointEscortDensity (a+1) (endpointK/a)=(a-1)/a := by
    unfold endpointEscortDensity escortDensity
    rw [hC]
    field_simp [ha₀.ne',hAk]
    ring
  have hLogu : Real.log (endpointK/a)=Real.log endpointK-Real.log a :=
    Real.log_div hk.ne' ha₀.ne'
  have hLogρ : Real.log ((a-1)/a)=Real.log (a-1)-Real.log a :=
    Real.log_div ha₁.ne' ha₀.ne'
  have hG : Real.log ((1+(endpointK/a)^2)/2)=endpointG a-2*Real.log a-Real.log 2 := by
    rw [show (1+(endpointK/a)^2)/2=(a^2+endpointK^2)/(a^2*2) by field_simp [ha₀.ne'] <;> ring,
      Real.log_div (by positivity) (by positivity),Real.log_mul (by positivity) (by norm_num),Real.log_pow]
    unfold endpointG
    push_cast
    ring
  unfold endpointEscortAtom escortAtom
  change endpointScalar a=a*(nativeEntropyCost (a+1) (endpointK/a)+
    endpointEscortDensity (a+1) (endpointK/a)*Real.log (endpointK/a)-
      (a+1)*endpointEscortDensity (a+1) (endpointK/a)*Real.log (endpointEscortDensity (a+1) (endpointK/a))-
        (1-(a+1)*endpointEscortCoefficient (a+1))*(endpointK/a-1))
  rw [hRho,hC]
  unfold nativeEntropyCost
  rw [hLogu,hLogρ,hG]
  unfold endpointScalar
  field_simp [ha₀.ne',hAk]
  ring

theorem endpointEscortAtom_low_endpoint_pos {P : ℝ} (hP : 3≤P) :
    0<endpointEscortAtom P (1/nativeSupportRatio P) := by
  have ha : 2≤P-1:=by linarith only [hP]
  have h:=endpointScalar_pos ha
  rw [endpointScalar_atom_identity ha,sub_add_cancel] at h
  have hAtom : 0<endpointEscortAtom P (endpointK/(P-1)) :=
    pos_of_mul_pos_right h (by linarith only [hP] : 0≤P-1)
  convert hAtom using 1
  unfold endpointK nativeSupportRatio
  field_simp [show P-1≠0 by linarith only [hP]]

private theorem endpoint_log_nine_half_lt : Real.log (9/2:ℝ)<151/100 := by
  have h:=Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤151/100) 6
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0:ℝ)<9/2)).mpr
  linarith only [h]

noncomputable def endpointUpperValue (a : ℝ) : ℝ :=
  (7*a+9)*Real.log (7*a/2)/2+
    7*a*(a-2)*(Real.log 2-Real.log (1+4/(49*a^2)))/4-
      7*a^2/4+a/2-9*(a+1)*Real.log (9/2)/2+9/2

theorem endpointUpperValue_pos {a : ℝ} (ha : 2≤a) (ha₄ : a≤4) :
    0<endpointUpperValue a := by
  let t:=(a-2)/2
  have ht : 0≤t:=by unfold t;linarith only [ha]
  have ht₁ : t≤1:=by unfold t;linarith only [ha₄]
  have ha₀ : 0<a:=by linarith only [ha]
  have hChord:=strictConcaveOn_log_Ioi.concaveOn.2
    (show (1:ℝ)∈Ioi 0 by norm_num) (show (2:ℝ)∈Ioi 0 by norm_num)
    (sub_nonneg.mpr ht₁) ht (by ring : (1-t)+t=1)
  simp only [smul_eq_mul,Real.log_one,mul_zero,zero_add] at hChord
  rw [show (1-t)*1+t*2=a/2 by unfold t;ring] at hChord
  have hLogR : Real.log 7+(a-2)/2*Real.log 2≤Real.log (7*a/2) := by
    rw [show 7*a/2=7*(a/2) by ring,Real.log_mul (by norm_num) (by positivity)]
    unfold t at hChord
    linarith only [hChord]
  have hSmall : Real.log (1+4/(49*a^2))≤4/(49*a^2) := by
    have h:=Real.log_le_sub_one_of_pos (show 0<1+4/(49*a^2) by positivity)
    linarith only [h]
  let Q:=(133/200)*(a-2)^2-(543/2800)*(a-2)+17/40
  let C:=(7*a+9)/2
  let J:=(a-2)*(14*a+9)/4
  let B:=7*a*(a-2)/4
  let D:=9*(a+1)/2
  have hC : 0<C:=by unfold C;positivity
  have hJ : 0≤J:=by unfold J;exact div_nonneg (mul_nonneg (sub_nonneg.mpr ha) (by positivity)) (by norm_num)
  have hB : 0≤B:=by unfold B;exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha₀.le) (sub_nonneg.mpr ha)) (by norm_num)
  have hD : 0<D:=by unfold D;positivity
  have h1:=mul_nonneg hC.le (sub_nonneg.mpr hLogR)
  have h2:=mul_pos hC (sub_pos.mpr affine_log_seven_bounds.1)
  have h3:=mul_nonneg hJ (sub_nonneg.mpr (by linarith only [Real.log_two_gt_d9] : (69/100:ℝ)≤Real.log 2))
  have h4:=mul_pos hD (sub_pos.mpr endpoint_log_nine_half_lt)
  have h5:=mul_nonneg hB (sub_nonneg.mpr hSmall)
  have h6 : 0≤(a-2)/14-(a-2)/(7*a) := by
    have hId : (a-2)/14-(a-2)/(7*a)=(a-2)^2/(14*a) := by field_simp [ha₀.ne'];ring
    rw [hId]
    positivity
  have hId : endpointUpperValue a-Q=
      C*(Real.log (7*a/2)- (Real.log 7+(a-2)/2*Real.log 2))+
      C*(Real.log 7-97/50)+J*(Real.log 2-69/100)+D*(151/100-Real.log (9/2))+
      B*(4/(49*a^2)-Real.log (1+4/(49*a^2)))+((a-2)/14-(a-2)/(7*a)) := by
    unfold endpointUpperValue Q C J D B
    field_simp [ha₀.ne']
    ring
  have hQ : 0<Q := by
    have hA : a-2≤2:=by linarith only [ha₄]
    unfold Q
    nlinarith only [hA,sq_nonneg (a-2)]
  linarith only [hId,h1,h2,h3,h4,h5,h6,hQ]

theorem endpointUpperValue_atom_identity {a : ℝ} (ha : 2≤a) :
    endpointUpperValue a=endpointEscortAtom (a+1) (7*a/2) := by
  have ha₀ : 0<a:=by linarith only [ha]
  have hAk : a-endpointK≠0:=by norm_num [endpointK] at ha ⊢;linarith only [ha]
  have hR : 0<7*a/2:=by positivity
  have hC : endpointEscortCoefficient (a+1)=1/(a-endpointK) := by
    unfold endpointEscortCoefficient endpointK
    congr 2
    ring
  have hRho : endpointEscortDensity (a+1) (7*a/2)=(9/2:ℝ) := by
    unfold endpointEscortDensity escortDensity
    rw [hC]
    field_simp [hAk]
    unfold endpointK
    ring
  have hSmall : 0<1+4/(49*a^2):=by positivity
  have hG : Real.log ((1+(7*a/2)^2)/2)=
      2*Real.log (7*a/2)+Real.log (1+4/(49*a^2))-Real.log 2 := by
    rw [show (1+(7*a/2)^2)/2=(7*a/2)^2*(1+4/(49*a^2))/2 by field_simp [ha₀.ne'] <;> ring,
      Real.log_div (by positivity) (by norm_num),Real.log_mul (by positivity) hSmall.ne',Real.log_pow]
    norm_num
  unfold endpointEscortAtom escortAtom
  change endpointUpperValue a=nativeEntropyCost (a+1) (7*a/2)+
    endpointEscortDensity (a+1) (7*a/2)*Real.log (7*a/2)-
      (a+1)*endpointEscortDensity (a+1) (7*a/2)*Real.log (endpointEscortDensity (a+1) (7*a/2))-
        (1-(a+1)*endpointEscortCoefficient (a+1))*(7*a/2-1)
  rw [hRho,hC]
  unfold nativeEntropyCost
  rw [hG]
  unfold endpointUpperValue
  field_simp [hAk]
  unfold endpointK
  ring

theorem endpointEscortAtom_upper_endpoint_pos {P : ℝ} (hP : 3≤P) (hP₅ : P≤5) :
    0<endpointEscortAtom P (nativeSupportRatio P) := by
  have ha : 2≤P-1:=by linarith only [hP]
  have h:=endpointUpperValue_pos ha (by linarith only [hP₅])
  rw [endpointUpperValue_atom_identity ha,sub_add_cancel] at h
  exact h

end ACS12.NativeCells

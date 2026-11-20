import ACS12.QuarticDebitWord
import ACS12.QuarticPayment
import ACS12.QuarticBaseTangent
import ACS12.QuarticSineTangents

namespace ACS12.NativeCells
open Set
open Pressure (massWeight massTotal massTotal_pos massWeight_sum_one)

private theorem entropy_atom_nonneg {u : ℝ} (hu : 0 < u) : 0 ≤ u*Real.log u-u+1 := by
  have h := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hu) hu.le
  rw [mul_sub,mul_one,mul_inv_cancel₀ hu.ne'] at h
  linarith

private theorem entropy_atom_pos {u : ℝ} (hu : 0 < u) (hne : u ≠ 1) : 0 < u*Real.log u-u+1 := by
  have h := mul_lt_mul_of_pos_left
    (Real.log_lt_sub_one_of_pos (inv_pos.mpr hu) (by simpa using hne)) hu
  rw [Real.log_inv,mul_sub,mul_one,mul_inv_cancel₀ hu.ne'] at h
  nlinarith

theorem quarticEntropy_pos {n : ℕ} (hn : 1 ≤ n) {w : Fin n → ℝ}
    (hw : ∀ i,0<w i) (hne : ¬ ∀ i,w i=1/(n:ℝ)) : 0 < quarticEntropy w := by
  have hN : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  obtain ⟨i,hi⟩ := not_forall.mp hne
  have hui : (n:ℝ)*w i ≠ 1 := by
    intro h
    apply hi
    exact (eq_div_iff hN.ne').mpr (by simpa [mul_comm] using h)
  apply div_pos _ hN
  apply Finset.sum_pos' (fun j _ => entropy_atom_nonneg (mul_pos hN (hw j)))
  exact ⟨i,Finset.mem_univ _,entropy_atom_pos (mul_pos hN (hw i)) hui⟩

private theorem quartic_payment_averages {n : ℕ} (hn : 5 ≤ n) {w : Fin n → ℝ}
    (hfloor : ∀ i,1/5 ≤ (n:ℝ)*w i) (hcap : ∀ i,w i≤1/4)
    (hne : ¬ ∀ i,w i=1/(n:ℝ)) :
    0 < (∑ i,quarticPaymentIntercept (1/(n:ℝ)) ((n:ℝ)*w i))/(n:ℝ) ∧
    0 ≤ (∑ i,quarticPaymentSlope (1/(n:ℝ)) ((n:ℝ)*w i))/(n:ℝ) := by
  have hN : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  have hN5 : (5:ℝ) ≤ n := by exact_mod_cast hn
  have hx : 0 < 1/(n:ℝ) := by positivity
  have hx5 : 1/(n:ℝ) ≤ 1/5 := (div_le_iff₀ hN).mpr (by linarith)
  have hc (i : Fin n) : (1/(n:ℝ))*((n:ℝ)*w i) ≤ 1/4 := by
    simpa [hN.ne'] using hcap i
  have hnon (i : Fin n) : 0 ≤ quarticPaymentIntercept (1/(n:ℝ)) ((n:ℝ)*w i) ∧
      0 ≤ quarticPaymentSlope (1/(n:ℝ)) ((n:ℝ)*w i) := by
    by_cases h : (n:ℝ)*w i=1
    · simp [h,quarticPaymentIntercept,quarticPaymentSlope]
    · exact ⟨(quarticPayment_pos hx hx5 (hfloor i) (hc i) h).1.le,
        (quarticPayment_pos hx hx5 (hfloor i) (hc i) h).2.le⟩
  obtain ⟨i,hi⟩ := not_forall.mp hne
  have hui : (n:ℝ)*w i ≠ 1 := by
    intro h
    exact hi ((eq_div_iff hN.ne').mpr (by simpa [mul_comm] using h))
  constructor
  · apply div_pos _ hN
    exact Finset.sum_pos' (fun j _ => (hnon j).1)
      ⟨i,Finset.mem_univ _,(quarticPayment_pos hx hx5 (hfloor i) (hc i) hui).1⟩
  · exact div_nonneg (Finset.sum_nonneg (fun j _ => (hnon j).2)) hN.le

theorem quartic_scalar_return {n : ℕ} (hn : 5 ≤ n) {w : Fin n → ℝ}
    (hw : ∀ i,0<w i) (hW : ∑ i,w i=1)
    (hfloor : ∀ i,1/5 ≤ (n:ℝ)*w i) (hcap : ∀ i,w i≤1/4)
    (hne : ¬ ∀ i,w i=1/(n:ℝ)) {t : ℝ} (ht : 0 ≤ t) :
    quarticEntropy w/50+(13/400)*(quarticDebitA w+quarticDebitB w/2)+
      t*(69/1250)*(quarticDebitA w+quarticDebitB w) < quarticBase w+t*quarticSineDeficit w := by
  let u (i : Fin n) := (n:ℝ)*w i
  let h (i : Fin n) := u i*Real.log (u i)-u i+1
  let b (i : Fin n) := u i-1-Real.log (u i)
  let v (i : Fin n) := (u i-1)^2/(n:ℝ)^2
  let avg (f : Fin n → ℝ) := (∑ i,f i)/(n:ℝ)
  let L (i : Fin n) := 3*h i-b i-(31/10)*(u i-1)^2/(n:ℝ)
  let D (i : Fin n) := h i-(43/24)*(u i-1)^2*(u i+2)/(n:ℝ)^2
  have hN : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  have avga (f g : Fin n → ℝ) : avg (fun i=>f i+g i)=avg f+avg g := by
    simp [avg,Finset.sum_add_distrib,add_div]
  have avgs (f g : Fin n → ℝ) : avg (fun i=>f i-g i)=avg f-avg g := by
    simp [avg,Finset.sum_sub_distrib,sub_div]
  have avgm (c : ℝ) (f : Fin n → ℝ) : avg (fun i=>c*f i)=c*avg f := by
    simp only [avg,← Finset.mul_sum]; ring
  have avgd (f : Fin n → ℝ) (c : ℝ) : avg (fun i=>f i/c)=avg f/c := by
    simp only [avg,← Finset.sum_div]; ring
  have avgb : avg b=quarticReverseEntropy w := (quarticReverseEntropy_eq hW).symm
  have avgh : avg h=quarticEntropy w := rfl
  have avgv : avg v=quarticWidthVariance w := by
    unfold avg quarticWidthVariance
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    dsimp [v,u]
    field_simp
  have hL : avg L ≤ quarticBase w := quarticBase_lower hn hw hcap hW
  have hD : avg D ≤ quarticSineDeficit w := quarticSineDeficit_lower hn hw hcap hW
  have hpoint (i : Fin n) : quarticPaymentIntercept (1/(n:ℝ)) (u i)+
      t*quarticPaymentSlope (1/(n:ℝ)) (u i) =
      L i+t*D i-h i/50-(13/400)*((7*b i+(23/2)*v i)+(b i+2*v i)/2)-
      t*(69/1250)*((7*b i+(23/2)*v i)+(b i+2*v i)) := by
    dsimp [quarticPaymentIntercept,quarticPaymentSlope,L,D,h,b,v]
    field_simp
    ring
  have hid := congrArg avg (funext hpoint)
  simp only [avga,avgs,avgm,avgd,avgb,avgh,avgv] at hid
  change avg (fun i=>quarticPaymentIntercept (1/(n:ℝ)) (u i))+
    t*avg (fun i=>quarticPaymentSlope (1/(n:ℝ)) (u i)) =
    avg L+t*avg D-quarticEntropy w/50-
      (13/400)*(quarticDebitA w+quarticDebitB w/2)-
      t*(69/1250)*(quarticDebitA w+quarticDebitB w) at hid
  have hpos := quartic_payment_averages hn hfloor hcap hne
  have htD := mul_le_mul_of_nonneg_left hD ht
  have hpos' : 0 < avg (fun i=>quarticPaymentIntercept (1/(n:ℝ)) (u i))+
      t*avg (fun i=>quarticPaymentSlope (1/(n:ℝ)) (u i)) :=
    add_pos_of_pos_of_nonneg hpos.1 (mul_nonneg ht hpos.2)
  linarith


theorem quartic_separation_of_defect {n : ℕ} (hn : 5 ≤ n) {p : ℝ} (hp : 4 ≤ p)
    {m : Fin n → ℝ} (hm : ∀ i, 0 < m i)
    (hfloor : ∀ i, 1/5 ≤ (n:ℝ)*massWeight m i)
    (hcap : ∀ i, massWeight m i ≤ 1/4)
    (hne : ¬ ∀ i, massWeight m i=1/(n:ℝ))
    (hZ : 0 < quarticZ p (massWeight m)) {I : ℝ}
    (hIp : I ≤ quarticRegularRatio p n)
    (hdef : quarticZ p (massWeight m)-quarticRegularRatio p n ≤
      quarticZ 4 (massWeight m)-1+I*((13/400)*
        (quarticDebitA (massWeight m)+quarticDebitB (massWeight m)/2)+
        (p-4)*(69/1250)*(quarticDebitA (massWeight m)+quarticDebitB (massWeight m)))) :
    quarticEntropy (massWeight m)/50+
      (1-quarticZ 4 (massWeight m))/quarticRegularRatio p n <
      Real.log (rootRow p m/quarticUpper p m) := by
  have hM := massTotal_pos (by omega : 1 ≤ n) hm
  have hw (i) : 0 < massWeight m i := div_pos (hm i) hM
  have hw₁ (i) : massWeight m i < 1 := lt_of_le_of_lt (hcap i) (by norm_num)
  have hW := massWeight_sum_one (by omega : 1 ≤ n) hm
  have hP : 0 < quarticRegularRatio p (n:ℝ) := quarticRegularRatio_pos (by linarith : 0 < p)
    (by exact_mod_cast (show 1 < n by omega))
  have hAB := quarticDebit_nonneg (by omega : 1 ≤ n) hw hW
  have hA := hAB.1
  have hB := hAB.2.1
  have ht : 0 ≤ p-4 := sub_nonneg.mpr hp
  let C : ℝ := (13/400)*(quarticDebitA (massWeight m)+quarticDebitB (massWeight m)/2)+
    (p-4)*(69/1250)*(quarticDebitA (massWeight m)+quarticDebitB (massWeight m))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hdef' : quarticZ p (massWeight m)-quarticRegularRatio p n ≤
      quarticZ 4 (massWeight m)-1+quarticRegularRatio p n*C :=
    le_trans hdef (add_le_add_right (mul_le_mul_of_nonneg_right hIp hC) _)
  have hlog := Real.log_le_sub_one_of_pos (div_pos hZ hP)
  have hdiv := (div_le_div_iff_of_pos_right hP).mpr hdef'
  have hid : (quarticZ 4 (massWeight m)-1+quarticRegularRatio p n*C)/
      quarticRegularRatio p n = -(1-quarticZ 4 (massWeight m))/quarticRegularRatio p n+C := by
    field_simp; ring
  rw [hid,sub_div,div_self hP.ne'] at hdiv
  have hscalar := quartic_scalar_return hn hw hW hfloor hcap hne (sub_nonneg.mpr hp)
  have hroot := quartic_log_rootComparison (by omega : 2 ≤ n) (by linarith : 0 < p) hm hw₁ hZ
  have hscalar' : quarticEntropy (massWeight m)/50+C <
      quarticBase (massWeight m)+(p-4)*quarticSineDeficit (massWeight m) := by
    simpa only [C,add_assoc] using hscalar
  simp only [neg_div] at hdiv
  linarith only [hdiv,hlog,hscalar',hroot]

end ACS12.NativeCells

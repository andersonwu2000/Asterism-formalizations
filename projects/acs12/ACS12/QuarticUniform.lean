import ACS12.QuarticRankEnergy
import ACS12.QuarticRankGeometry

/-! Equality of the original root and the quartic trial at a uniform word. -/
namespace ACS12.NativeCells

open Finset Set
open Pressure (massTotal massWeight periodicPathMass)

private theorem uniform_width_sum {n : ℕ} [NeZero n] :
    (∑ _i : Fin n, (1/(n:ℝ))) = 1 := by
  simp [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ne_zero.mpr (NeZero.ne n)]

private theorem quarticUniform_gap {n : ℕ} [NeZero n] (hn : 2 ≤ n) (i r : Fin n) (hr : r ≠ 0) :
    quarticActualGap (fun _ : Fin n => 1/(n:ℝ)) i (i+r) = quarticRegularGap r := by
  let w : Fin n → ℝ := fun _ => 1/(n:ℝ)
  have hN : 0 < (n:ℝ) := Nat.cast_pos.mpr (NeZero.pos n)
  have hW : (∑ i,w i)=1 := uniform_width_sum
  have hw (i : Fin n) : 0 < w i := one_div_pos.mpr hN
  have hji : i+r ≠ i := fun e => hr (add_left_cancel (e.trans (add_zero i).symm))
  have hK : 1 ≤ r.val := Nat.pos_of_ne_zero (fun e => hr (Fin.ext (e.trans (Fin.val_zero n).symm)))
  have hArc := quarticMidpoint_forward hw hW hji
  rw [quarticForwardPathLength_rank i r hr] at hArc
  have hI : quarticIntervening w i r.val = ((r.val-1:ℕ):ℝ)/(n:ℝ) := by
    simp [quarticIntervening,periodicPathMass,w,sum_const,card_range,nsmul_eq_mul,div_eq_mul_inv]
  have hArc' : halfArc (quarticCellAngle w) i (i+r) = Real.pi*(r:ℝ)/(n:ℝ) := by
    rw [hArc,hI,Nat.cast_sub hK,Nat.cast_one]
    change Real.pi*((1/(n:ℝ)+1/(n:ℝ))/2+((r.val:ℝ)-1)/(n:ℝ)) = Real.pi*(r.val:ℝ)/(n:ℝ)
    ring
  have hs : 0 < Real.sin (Real.pi/(n:ℝ)) := nearest_sine_pos hn
  change quarticActualGap w i (i+r) = _
  unfold quarticActualGap quarticRegularGap w
  rw [hArc',show Real.pi*(1/(n:ℝ))=Real.pi/(n:ℝ) by ring, ← pow_two,Real.sqrt_sq hs.le]

theorem quarticUniformZ_eq_regular {n : ℕ} [NeZero n] (hn : 2 ≤ n) {p : ℝ} (hp : 0 < p) :
    quarticZ p (fun _ : Fin n => 1/(n:ℝ)) = quarticRegularRatio p n := by
  let w : Fin n → ℝ := fun _ => 1/(n:ℝ)
  have hN : 0 < (n:ℝ) := Nat.cast_pos.mpr (NeZero.pos n)
  have hN₁ : (1:ℝ) < n := Nat.one_lt_cast.mpr (by omega)
  have hU (i : Fin n) : 0 < w i := one_div_pos.mpr hN
  have hW : (∑ i,w i)=1 := uniform_width_sum
  change quarticZ p w= _
  rw [quarticZ_rank_sum hn hp hU (fun _ => (div_lt_one hN).mpr hN₁) hW,quarticRegular_rank_sum hn hp]
  have hA (i j : Fin n) : quarticRankPrefactor w i j = 1 := by
    unfold quarticRankPrefactor w
    rw [← pow_two]
    change quarticRankScale n/quarticRankScale n=1
    exact div_self (quarticRankScale_pos hn).ne'
  have hSum (r : Fin n) (hr : r ∈ (univ : Finset (Fin n)).erase 0) :
      (∑ i, quarticRankPrefactor w i (i+r)*Real.exp (-p*quarticActualGap w i (i+r))) =
        (n:ℝ)*Real.exp (-p*quarticRegularGap r) := by
    simp only [hA,one_mul,w,quarticUniform_gap hn _ r (mem_erase.mp hr).1,
      sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [sum_congr rfl hSum,← mul_sum]
  ring

theorem quarticUniform_base_sine {n : ℕ} [NeZero n] :
    quarticBase (fun _ : Fin n => 1/(n:ℝ)) = 0 ∧
      quarticSineDeficit (fun _ : Fin n => 1/(n:ℝ)) = 0 := by
  have hN : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hMul : (n:ℝ)*(1/(n:ℝ))=1 := mul_one_div_cancel hN
  constructor
  · unfold quarticBase
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,one_div,inv_inv]
    field_simp [hN]
    ring
  · unfold quarticSineDeficit
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [show Real.pi*(1/(n:ℝ))=Real.pi/(n:ℝ) by ring,← mul_assoc,hMul,one_mul,sub_self]

theorem quarticUniform_root_eq_upper {n : ℕ} (hn : 2 ≤ n) {p c : ℝ} (hp : 0 < p) (hc : 0 < c) :
    rootRow p (fun _ : Fin n => c) = quarticUpper p (fun _ : Fin n => c) := by
  letI : NeZero n := ⟨by omega⟩
  let x := 1/(n:ℝ)
  let m : Fin n → ℝ := fun _ => c
  let s := Real.sin (Real.pi/(n:ℝ))
  let v := quarticGauge p x
  let T := analyticRow 4 (n:ℝ)
  have hN : 0 < (n:ℝ) := Nat.cast_pos.mpr (NeZero.pos n)
  have hN₁ : (1:ℝ) < n := Nat.one_lt_cast.mpr (by omega)
  have hx : 0 < x := one_div_pos.mpr hN
  have hx₁ : x < 1 := (div_lt_one hN).mpr hN₁
  have hT : 0 < T := analyticRow_pos (by norm_num) hN₁
  have hs : 0 < s := nearest_sine_pos hn
  have hv : 0 < v := quarticGauge_pos hx hx₁
  have hM : massTotal m=(n:ℝ)*c := by
    simp [massTotal,m,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hWeight : massWeight m=(fun _ : Fin n => x) := by
    funext i
    unfold massWeight
    rw [hM]
    change c/((n:ℝ)*c)=1/(n:ℝ)
    field_simp [hN.ne',hc.ne']
  have hMean : Rank.meanRoot p m = c ^ (1/(p+1)) := by
    unfold Rank.meanRoot m
    rw [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_div_cancel_left₀ _ hN.ne']
  have hR : rootRow p m=analyticRow p (n:ℝ)*c := by
    unfold rootRow
    rw [hMean,← Real.rpow_mul hc.le,one_div_mul_cancel (show p+1 ≠ 0 by positivity),Real.rpow_one]
  have hvSq : v^2=x/T*s^(p-4) := by
    unfold v quarticGauge
    rw [mul_pow,Real.sq_sqrt (div_nonneg hx.le (analyticRow_pos (by norm_num) ((one_lt_inv₀ hx).mpr hx₁)).le),
      show x⁻¹=(n:ℝ) by simp [x],show Real.pi*x=Real.pi/(n:ℝ) by unfold x; ring]
    change x/T*(s^((p-4)/2))^2 = _
    rw [← Real.rpow_natCast,← Real.rpow_mul hs.le]
    congr 2
    push_cast
    ring
  have hE : Real.exp (2*Real.log (c/v))=(c/v)^2 := by
    rw [show (2:ℝ)=((2:ℕ):ℝ) by norm_num,Real.exp_nat_mul,Real.exp_log (div_pos hc hv)]
  have hU : quarticUpper p m=analyticRow p (n:ℝ)*c := by
    unfold quarticUpper
    rw [hM,hWeight,show quarticZ p (fun _ : Fin n => x) = quarticRegularRatio p (n:ℝ) from
      quarticUniformZ_eq_regular hn hp]
    change quarticRegularRatio p (n:ℝ)/((n:ℝ)*c)*Real.exp (2*(∑ _i : Fin n,x*Real.log (c/v))) = _
    rw [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hNX : (n:ℝ)*x=1 := mul_one_div_cancel hN.ne'
    have hArg : 2*((n:ℝ)*(x*Real.log (c/v))) = 2*Real.log (c/v) := by
      rw [← mul_assoc (n:ℝ) x,hNX,one_mul]
    rw [hArg,hE,div_pow,hvSq]
    unfold quarticRegularRatio
    change (analyticRow p (n:ℝ)/T*s^(p-4))/((n:ℝ)*c) * (c^2/(x/T*s^(p-4))) = _
    unfold x
    field_simp [hN.ne',hc.ne',hT.ne',(Real.rpow_pos_of_pos hs _).ne']
  exact hR.trans hU.symm

end ACS12.NativeCells

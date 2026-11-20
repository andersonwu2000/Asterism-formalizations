import ACS12.QuarticRankGap
import ACS12.QuarticRankMoments
import ACS12.PressureMidpointPaths
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

/-! Exact cyclic midpoint geometry and the two intervening mass words. -/
namespace ACS12.NativeCells

open Finset Set
open Pressure (forwardPathLength periodicPathMass)

noncomputable def quarticArcLog (y : ℝ) : ℝ := Real.log (Real.sin (Real.pi*y))

theorem quarticArcSin_pos {y : ℝ} (hy : y ∈ Ioo (0:ℝ) 1) : 0 < Real.sin (Real.pi*y) :=
  Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hy.1) (by
    simpa only [mul_one] using mul_lt_mul_of_pos_left hy.2 Real.pi_pos)

theorem quarticArcLog_complement (y : ℝ) : quarticArcLog (1-y) = quarticArcLog y := by
  unfold quarticArcLog
  rw [show Real.pi*(1-y)=Real.pi-Real.pi*y by ring,Real.sin_pi_sub]

theorem quarticArcLog_concave : ConcaveOn ℝ (Ioo (0:ℝ) 1) quarticArcLog := by
  refine ⟨convex_Ioo _ _,?_⟩
  intro x hx y hy a b ha hb hab
  have hm := (convex_Ioo (0:ℝ) 1) hx hy ha hb hab
  simp only [smul_eq_mul] at hm ⊢
  have h := strictConcaveOn_sin_Icc.concaveOn.2
    (show Real.pi*x ∈ Icc 0 Real.pi from ⟨(mul_pos Real.pi_pos hx.1).le,by simpa only [mul_one] using mul_le_mul_of_nonneg_left hx.2.le Real.pi_pos.le⟩)
    (show Real.pi*y ∈ Icc 0 Real.pi from ⟨(mul_pos Real.pi_pos hy.1).le,by simpa only [mul_one] using mul_le_mul_of_nonneg_left hy.2.le Real.pi_pos.le⟩) ha hb hab
  simp only [smul_eq_mul] at h
  rw [show a*(Real.pi*x)+b*(Real.pi*y)=Real.pi*(a*x+b*y) by ring] at h
  have hL := strictConcaveOn_log_Ioi.concaveOn.2 (quarticArcSin_pos hx) (quarticArcSin_pos hy) ha hb hab
  simp only [smul_eq_mul] at hL
  have hA : 0 < a*Real.sin (Real.pi*x)+b*Real.sin (Real.pi*y) := by
    rcases ha.eq_or_lt with h0 | ha'
    · have hb' : 0 < b := by linarith only [hab,h0]
      exact add_pos_of_nonneg_of_pos (mul_nonneg ha (quarticArcSin_pos hx).le) (mul_pos hb' (quarticArcSin_pos hy))
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' (quarticArcSin_pos hx)) (mul_nonneg hb (quarticArcSin_pos hy).le)
  unfold quarticArcLog
  exact hL.trans (Real.log_le_log hA h)

noncomputable def quarticIntervening {n : ℕ} [NeZero n] (w : Fin n → ℝ) (i : Fin n) (k : ℕ) : ℝ :=
  ∑ l ∈ range (k-1), periodicPathMass w (i.val+(l+1))

private theorem periodicPathMass_add_fin {n : ℕ} [NeZero n] (w : Fin n → ℝ) (i : Fin n) (l : ℕ) :
    periodicPathMass w (i.val+l) = w (i + ⟨l%n,Nat.mod_lt l (NeZero.pos n)⟩) := by
  unfold periodicPathMass
  congr 1
  apply Fin.ext
  rw [Fin.val_add]
  exact (Nat.add_mod_mod _ _ _).symm

theorem quarticForwardPathLength_rank {n : ℕ} [NeZero n] (i r : Fin n) (hr : r ≠ 0) :
    forwardPathLength i (i+r) = r.val := by
  have hi := i.isLt
  have hr_lt := r.isLt
  have hr0 : 0 < r.val := Nat.pos_of_ne_zero (fun e => hr (Fin.ext (e.trans (Fin.val_zero n).symm)))
  unfold forwardPathLength
  by_cases h : n ≤ i.val+r.val
  · have hVal : (i+r).val = i.val+r.val-n := by
      rw [Fin.val_add,Nat.mod_eq_sub_mod h,Nat.mod_eq_of_lt (by omega)]
    have hiR : ¬ i < i+r := by change ¬ i.val < (i+r).val; omega
    rw [if_neg hiR,hVal]
    omega
  · have hVal : (i+r).val = i.val+r.val := by rw [Fin.val_add,Nat.mod_eq_of_lt (by omega)]
    have hiR : i < i+r := by change i.val < (i+r).val; omega
    rw [if_pos hiR,hVal]
    omega

theorem quarticMidpoint_forward {n : ℕ} [NeZero n] {w : Fin n → ℝ} (hw : ∀ i, 0 < w i)
    (hW : ∑ i,w i=1) {i j : Fin n} (hij : j ≠ i) :
    halfArc (quarticCellAngle w) i j =
      Real.pi*((w i+w j)/2+quarticIntervening w i (forwardPathLength i j)) := by
  have hM : Pressure.massTotal w=1 := hW
  have hWeights : Pressure.massWeight w=w := funext fun i => by simp [Pressure.massWeight,hM]
  have h := Pressure.midpoint_forwardPath_eq hw hij
  dsimp only at h
  rw [hM,hWeights] at h
  unfold Pressure.pathMassDistance at h
  simp only [Nat.add_zero, Pressure.periodicPathMass_in_range w i.isLt, Pressure.forwardPathMass_last] at h
  change (1/Real.pi)*(2*halfArc (quarticCellAngle w) i j) =
    w i+w j+2*quarticIntervening w i (forwardPathLength i j) at h
  field_simp [Real.pi_ne_zero] at h
  linear_combination h/2

private theorem quarticIntervening_nonneg {n : ℕ} [NeZero n] {w : Fin n→ℝ} (hw : ∀ i, 0 < w i)
    (i : Fin n) (k : ℕ) : 0 ≤ quarticIntervening w i k :=
  sum_nonneg fun _ _ => (hw _).le

theorem quarticIntervening_pos {n : ℕ} [NeZero n] {w : Fin n→ℝ} (hw : ∀ i, 0 < w i)
    (i : Fin n) {k : ℕ} (hk : 2 ≤ k) : 0 < quarticIntervening w i k :=
  sum_pos (fun _ _ => hw _) ⟨0,mem_range.mpr (by omega)⟩

theorem quarticIntervening_sum {n : ℕ} [NeZero n] {w : Fin n→ℝ} (hW : ∑ i,w i=1) (k : ℕ) :
    (∑ i, quarticIntervening w i k) = ((k-1 : ℕ):ℝ) := by
  unfold quarticIntervening
  rw [sum_comm]
  have h (l : ℕ) : (∑ i : Fin n,periodicPathMass w (i.val+(l+1))) = 1 := by
    simp_rw [periodicPathMass_add_fin]
    let j : Fin n := ⟨(l+1)%n,Nat.mod_lt (l+1) (NeZero.pos n)⟩
    exact (Equiv.sum_comp (Equiv.addRight j) w).trans hW
  simp [h]

theorem quarticIntervening_log_pay {n : ℕ} [NeZero n] {w : Fin n→ℝ} (hw : ∀ i, 0 < w i)
    (k : ℕ) (hk : 2 ≤ k) :
    (∑ i, Real.log (quarticIntervening w i k / (((k-1:ℕ):ℝ)/(n:ℝ)))) ≥
      (∑ i,Real.log ((n:ℝ)*w i)) := by
  let S := range (k-1)
  let N := (n:ℝ)
  let m := ((k-1:ℕ):ℝ)
  have hm : 0 < m := Nat.cast_pos.mpr (by omega)
  have hN : 0 < N := Nat.cast_pos.mpr (NeZero.pos n)
  let v (i : Fin n) (l : ℕ) := N*periodicPathMass w (i.val+(l+1))
  have hPoint (i : Fin n) : (1/m)*(∑ l ∈ S,Real.log (v i l)) ≤
      Real.log (quarticIntervening w i k/(m/N)) := by
    have h := strictConcaveOn_log_Ioi.concaveOn.le_map_sum (t := S) (w := fun _ => 1/m) (p := v i)
      (fun _ _ => (one_div_pos.mpr hm).le)
      (by simp [S, nsmul_eq_mul, m, hm.ne'])
      (fun l _ => mul_pos hN (hw _))
    simp only [smul_eq_mul,← mul_sum] at h
    have hE : (1/m)*(∑ l ∈ S,v i l) = quarticIntervening w i k/(m/N) := by
      unfold v S quarticIntervening
      rw [← mul_sum]
      field_simp [hm.ne',hN.ne']
    rwa [hE] at h
  have h := sum_le_sum (s := (univ : Finset (Fin n))) (fun i _ => hPoint i)
  rw [← mul_sum,sum_comm] at h
  have hShift (l : ℕ) : (∑ i : Fin n,Real.log (v i l)) = ∑ i,Real.log (N*w i) := by
    unfold v
    simp_rw [periodicPathMass_add_fin]
    let j : Fin n := ⟨(l+1)%n,Nat.mod_lt (l+1) (NeZero.pos n)⟩
    exact Equiv.sum_comp (Equiv.addRight j) (fun i => Real.log (N*w i))
  rw [sum_congr rfl (fun l _ => hShift l),sum_const,nsmul_eq_mul] at h
  rw [show ((S.card:ℕ):ℝ)=m by simp [S,m]] at h
  change (1/m)*(m*(∑ i,Real.log (N*w i))) ≤ _ at h
  rw [← mul_assoc,one_div,inv_mul_cancel₀ hm.ne',one_mul] at h
  exact h

theorem quarticRankFar_sizes {n : ℕ} [NeZero n] (hn : 5 ≤ n) {r : Fin n}
    (hr : r ∈ quarticFarRanks n) : 2 ≤ r.val ∧ 2 ≤ (-r).val ∧ r.val + (-r).val = n := by
  have hN : ((1:Fin n):ℕ)=1 := (Fin.val_one' n).trans (Nat.mod_eq_of_lt (by omega))
  have hM : ((-1:Fin n):ℕ)=n-1 := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp
  have hrM := (mem_erase.mp hr).1
  have hr1 := (mem_erase.mp (mem_erase.mp hr).2).1
  have hr0 := (mem_erase.mp (mem_erase.mp (mem_erase.mp hr).2).2).1
  have hR1 : r.val ≠ 1 := fun h => hr1 (Fin.ext (h.trans hN.symm))
  have hR0 : r.val ≠ 0 := fun h => hr0 (Fin.ext (h.trans (Fin.val_zero n).symm))
  have hRM : r.val ≠ n-1 := fun h => hrM (Fin.ext (h.trans hM.symm))
  have hr' := r.isLt
  have hrNeg : (-r).val = n-r.val := by
    rw [Fin.val_neg,if_neg hr0]
  omega

theorem quarticMidpoint_receipt {n : ℕ} [NeZero n] {w : Fin n→ℝ} (hw : ∀ i, 0 < w i)
    (hcap : ∀ i, w i ≤ 1/4) (hW : ∑ i,w i=1) {i j : Fin n} (hij : j ≠ i) :
    let T := (w i+w j)/2
    let I := quarticIntervening w i (forwardPathLength i j)
    let J := quarticIntervening w j (forwardPathLength j i)
    0 < T ∧ 0 ≤ I ∧ 0 ≤ J ∧ 2*T+I+J=1 ∧
      quarticArcLog (T+I)-quarticArcLog T ≤ quarticActualGap w i j := by
  let T := (w i+w j)/2
  let I := quarticIntervening w i (forwardPathLength i j)
  let J := quarticIntervening w j (forwardPathLength j i)
  have hT : 0 < T := by unfold T; positivity [hw i,hw j]
  have hI := quarticIntervening_nonneg hw i (forwardPathLength i j)
  have hJ := quarticIntervening_nonneg hw j (forwardPathLength j i)
  have hF := quarticMidpoint_forward hw hW hij
  have hB := quarticMidpoint_forward hw hW hij.symm
  have hRev := halfArc_reverse (quarticCellAngle w) hij.symm
  have hSum : 2*T+I+J=1 := by
    change halfArc (quarticCellAngle w) i j = Real.pi*(T+I) at hF
    change halfArc (quarticCellAngle w) j i = Real.pi*((w j+w i)/2+J) at hB
    rw [hF,hB] at hRev
    have hE : (w j+w i)/2=T := by unfold T; ring
    rw [hE] at hRev
    apply mul_left_cancel₀ Real.pi_ne_zero
    linear_combination hRev
  have hwi : w i ∈ Ioo (0:ℝ) 1 := ⟨hw i,(hcap i).trans_lt (by norm_num)⟩
  have hwj : w j ∈ Ioo (0:ℝ) 1 := ⟨hw j,(hcap j).trans_lt (by norm_num)⟩
  have hX : T+I ∈ Ioo (0:ℝ) 1 := by constructor <;> linarith only [hT,hI,hJ,hSum]
  have hP := mul_pos (quarticArcSin_pos hwi) (quarticArcSin_pos hwj)
  have hConc := quarticArcLog_concave.2 hwi hwj (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)+1/2=1)
  simp only [smul_eq_mul,show (1/2:ℝ)*w i+(1/2)*w j=T by unfold T; ring] at hConc
  refine ⟨hT,hI,hJ,hSum,?_⟩
  unfold quarticActualGap
  rw [hF, Real.log_div (quarticArcSin_pos hX).ne' (Real.sqrt_pos.mpr hP).ne',
    Real.log_sqrt hP.le,Real.log_mul (quarticArcSin_pos hwi).ne' (quarticArcSin_pos hwj).ne']
  change quarticArcLog (T+I)-quarticArcLog T ≤ quarticArcLog (T+I) - (quarticArcLog (w i)+quarticArcLog (w j))/2
  linarith only [hConc]

theorem quarticActualGap_nonneg {n : ℕ} [NeZero n] {w : Fin n→ℝ} (hw : ∀ i, 0 < w i)
    (hcap : ∀ i,w i≤1/4) (hW : ∑ i,w i=1) {i j : Fin n} (hij : j≠i) : 0 ≤ quarticActualGap w i j := by
  let T := (w i+w j)/2
  let I := quarticIntervening w i (forwardPathLength i j)
  let J := quarticIntervening w j (forwardPathLength j i)
  obtain ⟨hT,hI,hJ,hS,hGap⟩ := quarticMidpoint_receipt hw hcap hW hij
  change 0 < T at hT
  change 0 ≤ I at hI
  change 0 ≤ J at hJ
  change 2*T+I+J=1 at hS
  change quarticArcLog (T+I)-quarticArcLog T ≤ _ at hGap
  have hU : T ∈ Ioo (0:ℝ) 1 := ⟨hT,by linarith only [hS,hI,hJ,hT]⟩
  have hV : 1-T ∈ Ioo (0:ℝ) 1 := ⟨by linarith only [hU.2],by linarith only [hT]⟩
  have hP := quarticArcLog_concave.min_le_of_mem_Icc hU hV
    (show T+I ∈ Icc T (1-T) from ⟨by linarith only [hI],by linarith only [hS,hJ]⟩)
  rw [quarticArcLog_complement,min_self] at hP
  exact (sub_nonneg.mpr hP).trans hGap

end ACS12.NativeCells

import ACS12.QuarticArcReceipt

/-! The two-intervening-arc receipt on a complete cyclic nonneighbor rank. -/
namespace ACS12.NativeCells

open Finset Set

/-- Both arcs contribute their actual positive intervening mass and the
resulting logarithmic receipt retains the same cyclic endpoints. -/
theorem quartic_rank_receipt {n : ℕ} [NeZero n] (hn : 5 ≤ n) {w : Fin n → ℝ}
    (hw : ∀ i, 0 < w i) (hcap : ∀ i, w i ≤ 1/4) (hW : ∑ i, w i = 1)
    {r : Fin n} (hr : r ∈ quarticFarRanks n) :
    (∀ i, 0 < quarticActualGap w i (i+r)) ∧
      (∑ i, Real.log (quarticActualGap w i (i+r) / quarticRegularGap r)) ≥
        2*(∑ i, Real.log ((n:ℝ)*w i)) := by
  obtain ⟨hrL,hrR,hrSum⟩ := quarticRankFar_sizes hn hr
  let N := (n:ℝ)
  let T (i : Fin n) := (w i+w (i+r))/2
  let I (i : Fin n) := quarticIntervening w i r.val
  let J (i : Fin n) := quarticIntervening w (i+r) (-r).val
  let T₀ := 1/N
  let I₀ := ((r.val-1:ℕ):ℝ)/N
  let J₀ := (((-r).val-1:ℕ):ℝ)/N
  have hN : 0 < N := Nat.cast_pos.mpr (NeZero.pos n)
  have hNR : 1 < N := Nat.one_lt_cast.mpr (by omega)
  have hT₀ : 0 < T₀ := one_div_pos.mpr hN
  have hI₀ : 0 < I₀ := div_pos (Nat.cast_pos.mpr (by omega)) hN
  have hJ₀ : 0 < J₀ := div_pos (Nat.cast_pos.mpr (by omega)) hN
  have hr₀ : r ≠ 0 := by intro e; subst r; simp at hrL
  have hr₀' : -r ≠ 0 := neg_ne_zero.mpr hr₀
  have hS₀ : 2*T₀+I₀+J₀=1 := by
    have hR : (r.val:ℝ)+((-r).val:ℝ)=N := by
      unfold N
      rw [← Nat.cast_add,hrSum]
    unfold T₀ I₀ J₀
    rw [Nat.cast_sub (by omega : 1 ≤ r.val), Nat.cast_sub (by omega : 1 ≤ (-r).val),Nat.cast_one]
    field_simp [hN.ne']
    linarith only [hR]
  have hCase (i : Fin n) : 0 < T i ∧ 2*T i+I i+J i=1 ∧
      quarticArcLog (T i+I i)-quarticArcLog (T i) ≤ quarticActualGap w i (i+r) := by
    have hji : i+r ≠ i := fun h => hr₀ (add_left_cancel (h.trans (add_zero i).symm))
    have hF := quarticForwardPathLength_rank i r hr₀
    have hR : Pressure.forwardPathLength (i+r) i = (-r).val := by
      simpa only [add_neg_cancel_right] using quarticForwardPathLength_rank (i+r) (-r) hr₀'
    have h := quarticMidpoint_receipt hw hcap hW hji
    dsimp only at h
    rw [hF,hR] at h
    exact ⟨h.1,h.2.2.2.1,h.2.2.2.2⟩
  have hI (i : Fin n) : 0 < I i := quarticIntervening_pos hw i hrL
  have hJ (i : Fin n) : 0 < J i := quarticIntervening_pos hw (i+r) hrR
  have hMeanT : (∑ i,T i)=N*T₀ := by
    unfold T T₀
    rw [← sum_div,sum_add_distrib,show (∑ i:Fin n,w (i+r))=∑ i,w i from Equiv.sum_comp (Equiv.addRight r) w,
      hW,one_add_one_eq_two,div_self (by norm_num : (2:ℝ)≠0), mul_one_div_cancel hN.ne']
  have hMeanI : (∑ i,I i)=N*I₀ := by
    unfold I I₀
    rw [quarticIntervening_sum hW]
    field_simp [hN.ne']
  have hMeanJ : (∑ i,J i)=N*J₀ := by
    unfold J J₀
    rw [show (∑ i:Fin n,quarticIntervening w (i+r) (-r).val) = ∑ i,quarticIntervening w i (-r).val from
      Equiv.sum_comp (Equiv.addRight r) (fun i => quarticIntervening w i (-r).val),quarticIntervening_sum hW]
    field_simp [hN.ne']
  have hRef : quarticRegularGap r = quarticArcLog (T₀+I₀)-quarticArcLog T₀ := by
    have hU : T₀ ∈ Ioo (0:ℝ) 1 := ⟨hT₀,(div_lt_one hN).mpr hNR⟩
    have hX : T₀+I₀ ∈ Ioo (0:ℝ) 1 := ⟨add_pos hT₀ hI₀,by linarith only [hT₀,hJ₀,hS₀]⟩
    have hE : T₀+I₀=(r:ℝ)/N := by
      unfold T₀ I₀
      rw [← add_div,Nat.cast_sub (by omega : 1 ≤ r.val),Nat.cast_one]
      change (1+((r.val:ℝ)-1))/N=(r.val:ℝ)/N
      ring
    have hR : Real.pi*(T₀+I₀)=Real.pi*(r:ℝ)/(n:ℝ) := by rw [hE]; unfold N; ring
    have hT : Real.pi*T₀=Real.pi/(n:ℝ) := by unfold T₀ N; ring
    unfold quarticRegularGap quarticArcLog
    rw [← hR, ← hT,Real.log_div (quarticArcSin_pos hX).ne' (quarticArcSin_pos hU).ne']
  have hRec := quarticInterveningArc_log_receipt (fun i => (hCase i).1) hI hJ
    (fun i => (hCase i).2.1) hT₀ hI₀ hJ₀ hS₀ hMeanT hMeanI hMeanJ (fun i => (hCase i).2.2) hRef
  have hPayI : (∑ i, Real.log (N*w i)) ≤ ∑ i, Real.log (I i/I₀) :=
    quarticIntervening_log_pay hw r.val hrL
  have hPayJ : (∑ i, Real.log (N*w i)) ≤ ∑ i, Real.log (J i/J₀) := by
    unfold J
    rw [show (∑ i:Fin n,Real.log (quarticIntervening w (i+r) (-r).val/J₀)) =
        ∑ i,Real.log (quarticIntervening w i (-r).val/J₀) from
      Equiv.sum_comp (Equiv.addRight r) (fun i => Real.log (quarticIntervening w i (-r).val/J₀))]
    exact quarticIntervening_log_pay hw (-r).val hrR
  refine ⟨hRec.1,?_⟩
  change 2*(∑ i,Real.log (N*w i)) ≤ _
  linarith only [hRec.2,hPayI,hPayJ]

end ACS12.NativeCells

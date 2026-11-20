import ACS12.SourceMassMoment
import ACS12.PressureMaxPacking

/-! The normalized period forced by the same original physical masses. -/
namespace ACS12.Pressure

open Set CenteredCircle.AllN

theorem source_massTotal_le_period {n : ℕ} (hn : 2 ≤ n) (S : AnchoredCircleSource (Fin n))
    (hCaps : S.HasCircularMassCaps) : (∑ i, S.mass i) ≤ S.period := by
  let o : Fin n := ⟨0,by omega⟩
  let σ := Tuple.sort S.coordinate
  let t (j : ℕ) := if h : j < n then S.coordinate (σ ⟨j,h⟩) else S.coordinate (σ o) + S.period
  have ht : StrictMono (S.coordinate ∘ σ) :=
    (Tuple.monotone_sort S.coordinate).strictMono_of_injective (S.coordinate_injective.comp σ.injective)
  change StrictMono (fun j => S.coordinate (σ j)) at ht
  have hStep (j : Fin n) : S.mass (σ j) ≤ t (j.val + 1) - t j.val := by
    unfold t
    rw [dif_pos j.isLt]
    split_ifs with h
    · have hj : j < (⟨j.val + 1,h⟩ : Fin n) := Nat.lt_succ_self _
      have h₁ := (hCaps (σ j) (σ ⟨j.val + 1,h⟩) (σ.injective.ne hj.ne)).1
      rw [abs_of_pos (sub_pos.mpr (ht hj))] at h₁
      exact h₁
    · have hj : o < j := by change 0 < j.val; have := j.isLt; omega
      have h₁ := (hCaps (σ j) (σ o) (σ.injective.ne hj.ne')).2
      rw [abs_of_neg (sub_neg.mpr (ht hj))] at h₁
      linarith only [h₁]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hStep j)
  have hMass : (∑ j : Fin n, S.mass (σ j)) = ∑ j : Fin n, S.mass j := Equiv.sum_comp σ S.mass
  have hTel : (∑ j : Fin n, (t (j.val + 1) - t j.val)) = t n - t 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun j => t (j + 1) - t j)]
    calc
      _ = -(∑ j ∈ Finset.range n, (t j - t (j + 1))) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [Finset.sum_range_sub',neg_sub]
  rw [hMass,hTel] at h
  have h0 : t 0 = S.coordinate (σ o) := dif_pos (by omega)
  have hN : t n = S.coordinate (σ o) + S.period := dif_neg (lt_irrefl n)
  rwa [h0,hN,add_sub_cancel_left] at h

private theorem diameterChordSq_eq_one_antipodal {n : ℕ} {p : ℝ}
    (F : Configuration n p) (i j : Fin n) (h : F.diameterChordSq i j=1) :
    F.position j-F.center=-(F.position i-F.center) := by
  have hR:=F.radius_pos
  have hChord : ‖F.position j-F.position i‖^2=(2*F.radius)^2 := by
    unfold Configuration.diameterChordSq at h
    rw [div_pow] at h
    exact (div_eq_one_iff_eq (pow_ne_zero 2 (mul_pos zero_lt_two hR).ne')).mp h
  have hPar : ‖(F.position j-F.center)+(F.position i-F.center)‖^2+
      ‖(F.position j-F.center)-(F.position i-F.center)‖^2=
      2*‖F.position j-F.center‖^2+2*‖F.position i-F.center‖^2 := by
    simp only [←Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.add_re,Complex.add_im,
      Complex.sub_re,Complex.sub_im]
    ring
  rw [sub_sub_sub_cancel_right,F.on_circle,F.on_circle,hChord] at hPar
  have hSum : ‖(F.position j-F.center)+(F.position i-F.center)‖^2=0 := by nlinarith only [hPar]
  exact eq_neg_of_add_eq_zero_left (norm_eq_zero.mp (sq_eq_zero_iff.mp hSum))

theorem original_massTotal_gt_twice {n : ℕ} {p : ℝ} (F : Configuration n p)
    (hn : 3≤n) (i : Fin n) : 2*F.mass i<massTotal F.mass := by
  let e:=(Finset.univ : Finset (Fin n)).erase i
  have he : 1<e.card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i),Finset.card_univ,Fintype.card_fin]
    omega
  obtain ⟨a,ha,b,hb,hab⟩:=Finset.one_lt_card.mp he
  have hSome : ∃ j∈e,F.diameterChordSq i j<1 := by
    by_contra! hNo
    have hA:=le_antisymm (F.diameterChordSq_le_one i a) (hNo a ha)
    have hB:=le_antisymm (F.diameterChordSq_le_one i b) (hNo b hb)
    have hEq:= (diameterChordSq_eq_one_antipodal F i a hA).trans
      (diameterChordSq_eq_one_antipodal F i b hB).symm
    have hPos : F.position a=F.position b := by linear_combination hEq
    exact hab (F.distinct hPos)
  have hStrict : (∑ j∈e,F.mass j*F.diameterChordSq i j)<∑ j∈e,F.mass j := by
    apply Finset.sum_lt_sum
    · exact fun j _=>mul_le_of_le_one_right (F.mass_pos j).le (F.diameterChordSq_le_one i j)
    · obtain ⟨j,hj,hlt⟩:=hSome
      exact ⟨j,hj,mul_lt_of_lt_one_right (F.mass_pos j) hlt⟩
  have hMoment:=F.diameterChordSq_centered_sum i i
  have hTerm (j : Fin n) : F.mass j*F.diameterChordSq i j=
      F.mass i*((F.mass j/F.mass i)*F.diameterChordSq i j) := by
    field_simp [(F.mass_pos i).ne']
  simp_rw [hTerm] at hStrict
  rw [←Finset.mul_sum,hMoment] at hStrict
  have hCancel : F.mass i*(massTotal F.mass/F.mass i/2)=massTotal F.mass/2 := by
    field_simp [(F.mass_pos i).ne']
  rw [hCancel,Finset.sum_erase_eq_sub (Finset.mem_univ i)] at hStrict
  change massTotal F.mass/2<massTotal F.mass-F.mass i at hStrict
  linarith only [hStrict]

theorem high_original_normalized_period_gt_two {n : ℕ} {p : ℝ} (hn : 3≤n)
    (F : Configuration n p) (C : NormalizedCircleChart F.phase F.mass (2*Real.pi)) (i : Fin n) :
    2<C.source.period/C.source.mass i := by
  have hm:=F.mass_pos C.source.root
  have hMass : 2<massTotal F.mass/F.mass i :=
    (lt_div_iff₀ (F.mass_pos i)).mpr (original_massTotal_gt_twice F hn i)
  have hScale : (∑ j,C.source.mass j)/C.source.mass i=massTotal F.mass/F.mass i := by
    simp_rw [C.mass_eq]
    rw [←Finset.sum_div]
    unfold massTotal
    field_simp [hm.ne']
  have hPack:=(div_le_div_iff_of_pos_right (C.source.mass_pos i)).mpr
    (source_massTotal_le_period (by omega) C.source C.circular_caps)
  rw [hScale] at hPack
  exact hMass.trans_le hPack

end ACS12.Pressure

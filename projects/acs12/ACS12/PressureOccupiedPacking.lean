import ACS12.PressureIncidentRay

/-! Occupied ray caps at every actual site, with the cyclic wrap retained. -/
namespace ACS12.Pressure

open Set CenteredCircle.AllN

theorem mass_add_bose {m s : ℝ} (hm : 0 < m) (hs : 0 < s) :
    m + pressureBose m s = m / periodicDen m s := by
  unfold pressureBose
  field_simp [(periodicDen_pos hm hs).ne']
  unfold periodicDen
  ring

private theorem mass_add_bose_mono {s a b : ℝ} (hs : 0 < s) (ha : 0 < a) (hab : a ≤ b) :
    a + pressureBose a s ≤ b + pressureBose b s := by
  have hb := ha.trans_le hab
  rw [mass_add_bose ha hs,mass_add_bose hb hs]
  have h := strictMonoOn_expHeadFactor.monotoneOn (show s * a ∈ Ioi 0 from mul_pos hs ha)
    (show s * b ∈ Ioi 0 from mul_pos hs hb) (mul_le_mul_of_nonneg_left hab hs.le)
  apply (mul_le_mul_iff_right₀ hs).mp
  simpa only [expHeadFactor,periodicDen,← mul_div_assoc,neg_mul] using h

private theorem pressureBose_anti {s a b : ℝ} (hs : 0 < s) (ha : 0 < a) (hab : a ≤ b) :
    pressureBose b s ≤ pressureBose a s := by
  have hb := ha.trans_le hab
  rw [pressureBose_eq ha hs,pressureBose_eq hb hs]
  have h := strictAntiOn_expTailFactor.antitoneOn (show s * a ∈ Ioi 0 from mul_pos hs ha)
    (show s * b ∈ Ioi 0 from mul_pos hs hb) (mul_le_mul_of_nonneg_left hab hs.le)
  apply (mul_le_mul_iff_right₀ hs).mp
  simpa only [scaledExpTail,expTailFactor,← mul_div_assoc] using h

private theorem exp_mul_mass_add_bose {s a b g : ℝ} (hs : 0 < s) (ha : 0 < a) (hb : 0 < b)
    (hag : a ≤ g) (hbg : b ≤ g) :
    Real.exp (-s * g) * (b + pressureBose b s) ≤ pressureBose a s := by
  have hE (m : ℝ) (hm : 0 < m) :
      Real.exp (-s * m) * (m + pressureBose m s) = pressureBose m s := by
    rw [mass_add_bose hm hs]
    unfold pressureBose
    ring
  rcases le_total b a with h | h
  · calc
      _ ≤ Real.exp (-s * a) * (b + pressureBose b s) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hag (neg_nonpos.mpr hs.le)))
          (add_nonneg hb.le (pressureBose_pos hb hs).le)
      _ ≤ Real.exp (-s * a) * (a + pressureBose a s) :=
        mul_le_mul_of_nonneg_left (mass_add_bose_mono hs hb h) (Real.exp_pos _).le
      _ = _ := hE a ha
  · calc
      _ ≤ Real.exp (-s * b) * (b + pressureBose b s) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hbg (neg_nonpos.mpr hs.le)))
          (add_nonneg hb.le (pressureBose_pos hb hs).le)
      _ = pressureBose b s := hE b hb
      _ ≤ _ := pressureBose_anti hs ha h

theorem exists_cyclic_nearest {n : ℕ} (hn : 2 ≤ n) (d : Fin n → Fin n → ℝ) (i : Fin n) :
    ∃ j, j ≠ i ∧ ∀ k, k ≠ i → d i j ≤ d i k := by
  have hOther : ∃ j : Fin n, j ≠ i := by
    by_contra! h
    have h₀ : (⟨0,by omega⟩ : Fin n) = i := h _
    have h₁ : (⟨1,by omega⟩ : Fin n) = i := h _
    exact Nat.zero_ne_one (congrArg Fin.val (h₀.trans h₁.symm))
  obtain ⟨j,hj⟩ := hOther
  have hW : (Finset.univ.erase i).Nonempty := ⟨j,Finset.mem_erase.mpr ⟨hj,Finset.mem_univ _⟩⟩
  obtain ⟨k,hk,hMin⟩ := (Finset.univ.erase i).exists_min_image (d i) hW
  exact ⟨k,(Finset.mem_erase.mp hk).1,fun j hj => hMin j (Finset.mem_erase.mpr ⟨hj,Finset.mem_univ _⟩)⟩

private theorem occupied_ray_le_bose {n : ℕ} (hn : 2 ≤ n) {L s : ℝ} (hL : 0 < L) (hs : 0 < s)
    (m : Fin n → ℝ) (hm : ∀ i, 0 < m i) (d : Fin n → Fin n → ℝ)
    (hSelf : ∀ i, d i i = L)
    (hCap : ∀ i j, i ≠ j → m i ≤ d i j ∧ m j ≤ d i j)
    (hSplit : ∀ i j, j ≠ i → (∀ k, k ≠ i → d i j ≤ d i k) →
      ∀ k, k ≠ j → d i k = d j k + d i j) (i : Fin n) :
    rayWeight L m (d i) s ≤ pressureBose (m i) s := by
  let R (j : Fin n) := rayWeight L m (d j) s / pressureBose (m j) s
  have hW : (Finset.univ : Finset (Fin n)).Nonempty := ⟨i,Finset.mem_univ _⟩
  obtain ⟨k,_,hMax⟩ := Finset.univ.exists_max_image R hW
  have hR (j : Fin n) : rayWeight L m (d j) s ≤ R k * pressureBose (m j) s :=
    (div_le_iff₀ (pressureBose_pos (hm j) hs)).mp (hMax j (Finset.mem_univ _))
  by_contra! h
  have hMk : 1 < R k := ((one_lt_div (pressureBose_pos (hm i) hs)).mpr h).trans_le
    (hMax i (Finset.mem_univ _))
  obtain ⟨j,hj,hNear⟩ := exists_cyclic_nearest hn d k
  have hT := rayWeight_shift hL hs m (d j) (d k) j (hSelf j) rfl (hSplit k j hj hNear)
  obtain ⟨h₁,h₂⟩ := hCap k j hj.symm
  have hC := exp_mul_mass_add_bose hs (hm k) (hm j) h₁ h₂
  have hE : rayWeight L m (d k) s = R k * pressureBose (m k) s := by
    unfold R
    rw [div_mul_cancel₀ _ (pressureBose_pos (hm k) hs).ne']
  have hLt : rayWeight L m (d k) s < R k * pressureBose (m k) s := by
    rw [hT]
    calc
      _ ≤ Real.exp (-s * d k j) * (R k * pressureBose (m j) s + m j) :=
        mul_le_mul_of_nonneg_left (add_le_add_left (hR j) _) (Real.exp_pos _).le
      _ < Real.exp (-s * d k j) * (R k * (m j + pressureBose (m j) s)) := by
        apply mul_lt_mul_of_pos_left _ (Real.exp_pos _)
        nlinarith only [mul_lt_mul_of_pos_right hMk (hm j)]
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left hC (zero_le_one.trans hMk.le)
        linarith only [h]
  exact hLt.ne hE

theorem cyclic_forward_split {n : ℕ} (S : AnchoredCircleSource (Fin n)) (i j : Fin n) (hj : j ≠ i)
    (hNear : ∀ k, k ≠ i → S.forwardDistance i j ≤ S.forwardDistance i k)
    (k : Fin n) (hk : k ≠ j) :
    S.forwardDistance i k = S.forwardDistance j k + S.forwardDistance i j := by
  by_cases hk' : k = i
  · subst k
    rw [S.forwardDistance_self,S.forwardDistance_flip hj.symm]
    ring
  · exact S.forwardDistance_adjacent_split hj.symm (Ne.symm hk')
      (lt_of_le_of_ne (hNear k hk') ((S.forwardDistance_injective i).ne hk.symm))

theorem cyclic_backward_split {n : ℕ} (S : AnchoredCircleSource (Fin n)) (i j : Fin n) (hj : j ≠ i)
    (hNear : ∀ k, k ≠ i → S.forwardDistance j i ≤ S.forwardDistance k i)
    (k : Fin n) (hk : k ≠ j) :
    S.forwardDistance k i = S.forwardDistance k j + S.forwardDistance j i := by
  by_cases hk' : k = i
  · subst k
    rw [S.forwardDistance_self,S.forwardDistance_flip hj]
    ring
  · have hJ := S.forwardDistance_flip hj.symm
    have hK := S.forwardDistance_flip (Ne.symm hk')
    have hLt := lt_of_le_of_ne (hNear k hk') ((S.backwardDistance_injective i).ne hk.symm)
    have h := S.forwardDistance_adjacent_split (Ne.symm hk') hj.symm (by linarith only [hLt,hJ,hK])
    linarith only [h,hJ,hK]

theorem occupied_rays_le_bose {n : ℕ} (hn : 2 ≤ n) (S : AnchoredCircleSource (Fin n))
    (hCap : S.HasCircularMassCaps) (i : Fin n) {s : ℝ} (hs : 0 < s) :
    leftRay S i s ≤ pressureBose (S.mass i) s ∧ rightRay S i s ≤ pressureBose (S.mass i) s := by
  exact ⟨occupied_ray_le_bose hn S.period_pos hs S.mass S.mass_pos
      (fun i j => S.forwardDistance j i) S.forwardDistance_self
      (fun i j h => (S.forwardDistance_caps hCap h.symm).symm) (cyclic_backward_split S) i,
    occupied_ray_le_bose hn S.period_pos hs S.mass S.mass_pos S.forwardDistance
      S.forwardDistance_self (fun _ _ => S.forwardDistance_caps hCap) (cyclic_forward_split S) i⟩

end ACS12.Pressure

import ACS12.Angular
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

/-! The two finite inequalities in the rank and root-moment bound. -/

namespace ACS12.Rank

open scoped BigOperators
open CenteredCircle.AllN (positiveAngle_range)
set_option backward.isDefEq.respectTransparency false

/-- For any positive masses and positive chord lengths, the weighted power
mean controls the sum of the mass-weighted inverse powers. -/
theorem root_bound {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    {a : ℝ} (ha : 0 ≤ a) (m d : ι → ℝ)
    (hm : ∀ i ∈ s, 0 < m i) (hd : ∀ i ∈ s, 0 < d i) :
    (∑ i ∈ s, m i ^ (1 / (a + 1))) ^ (a + 1) / (∑ i ∈ s, d i) ^ a ≤
      ∑ i ∈ s, m i / d i ^ a := by
  let D := ∑ i ∈ s, d i
  have hD : 0 < D := Finset.sum_pos hd hs
  let w : ι → ℝ := fun i => d i / D
  let z : ι → ℝ := fun i => m i ^ (1 / (a + 1)) / d i
  have hw (i : ι) (hi : i ∈ s) : 0 ≤ w i := (div_pos (hd i hi) hD).le
  have hz (i : ι) (hi : i ∈ s) : 0 ≤ z i :=
    (div_pos (Real.rpow_pos_of_pos (hm i hi) _) (hd i hi)).le
  have hw1 : (∑ i ∈ s, w i) = 1 := by
    simp only [w, ← Finset.sum_div]
    exact div_self hD.ne'
  have h := Real.rpow_arith_mean_le_arith_mean_rpow s w z hw hw1 hz (p := a + 1) (by linarith)
  have hterm (i : ι) (hi : i ∈ s) : w i * z i = m i ^ (1 / (a + 1)) / D := by
    dsimp only [w, z]
    field_simp [(hd i hi).ne']
  have hterm' (i : ι) (hi : i ∈ s) :
      w i * z i ^ (a + 1) = (m i / d i ^ a) / D := by
    dsimp only [w, z]
    rw [Real.div_rpow (Real.rpow_nonneg (hm i hi).le _) (hd i hi).le,
      ← Real.rpow_mul (hm i hi).le, one_div_mul_cancel (by linarith : a + 1 ≠ 0), Real.rpow_one,
      Real.rpow_add (hd i hi) a 1, Real.rpow_one]
    field_simp [(hd i hi).ne', (Real.rpow_pos_of_pos (hd i hi) a).ne']
  rw [Finset.sum_congr rfl hterm, Finset.sum_congr rfl hterm',
    ← Finset.sum_div, ← Finset.sum_div,
    Real.div_rpow (Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hm i hi).le _) hD.le,
    Real.rpow_add hD a 1, Real.rpow_one, ← div_div] at h
  exact (div_le_div_iff_of_pos_right hD).mp h

/-- Jensen's bound for the chord sine on an entire cyclic rank. -/
theorem sine_sum_bound {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (t : ι → ℝ)
    (ht : ∀ i ∈ s, t i ∈ Set.Icc 0 Real.pi) :
    (∑ i ∈ s, Real.sin (t i)) ≤ (s.card : ℝ) * Real.sin ((∑ i ∈ s, t i) / s.card) := by
  have hsR : 0 < (s.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hs)
  have h := ConcaveOn.le_map_sum (StrictConcaveOn.concaveOn strictConcaveOn_sin_Icc)
    (t := s) (w := fun _ => 1 / (s.card : ℝ)) (p := t)
    (fun _ _ => (one_div_pos.mpr hsR).le)
    (by rw [Finset.sum_const, nsmul_eq_mul, mul_one_div_cancel hsR.ne'])
    ht
  simp only [smul_eq_mul, one_div_mul_eq_div, ← Finset.sum_div] at h
  simpa only [mul_comm] using (div_le_iff₀ hsR).mp h

private theorem uniform_halfArc (n : ℕ) [NeZero n] (i k : Fin n) :
    halfArc (fun j => 2 * Real.pi * (j : ℝ) / (n : ℝ)) i (i + k) =
      Real.pi * (k : ℝ) / (n : ℝ) := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hi := i.isLt
  have hk := k.isLt
  by_cases h : n ≤ i.val + k.val
  · have hv : (i + k).val = i.val + k.val - n := by
      rw [Fin.val_add, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    have hwrap : i + k < i := by
      change (i + k).val < i.val
      omega
    have hreal : ((i + k : Fin n) : ℝ) = (i : ℝ) + (k : ℝ) - (n : ℝ) := by
      apply eq_sub_iff_add_eq.mpr
      exact_mod_cast (show (i + k).val + n = i.val + k.val by omega)
    simp only [halfArc, if_pos hwrap, hreal]
    field_simp [hn]
    ring
  · have hv : (i + k).val = i.val + k.val := by
      rw [Fin.val_add, Nat.mod_eq_of_lt (by omega)]
    have hwrap : ¬ i + k < i := by
      change ¬ (i + k).val < i.val
      omega
    have hreal : ((i + k : Fin n) : ℝ) = (i : ℝ) + (k : ℝ) := by exact_mod_cast hv
    simp only [halfArc, if_neg hwrap, hreal, add_zero]
    ring

theorem halfArc_rank_sum (n : ℕ) [NeZero n] (a : Fin n → ℝ) (k : Fin n) :
    (∑ i, halfArc a i (i + k)) = (n : ℝ) * (Real.pi * (k : ℝ) / (n : ℝ)) := by
  let b : Fin n → ℝ := fun j => 2 * Real.pi * (j : ℝ) / (n : ℝ)
  have hterm (i : Fin n) : halfArc a i (i + k) =
      halfArc b i (i + k) + ((a (i + k) - b (i + k)) - (a i - b i)) / 2 := by
    unfold halfArc
    ring
  have hperm : (∑ i : Fin n, (a (i + k) - b (i + k))) = ∑ i : Fin n, (a i - b i) :=
    Equiv.sum_comp (Equiv.addRight k) (fun i => a i - b i)
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, ← Finset.sum_div,
    Finset.sum_sub_distrib, hperm, sub_self, zero_div, add_zero]
  simp only [b, uniform_halfArc, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

noncomputable def meanRoot {n : ℕ} (α : ℝ) (m : Fin n → ℝ) : ℝ :=
  (∑ i, m i ^ (1 / (α + 1))) / (n : ℝ)

noncomputable def referenceRow {n : ℕ} [NeZero n] (α R : ℝ) (m : Fin n → ℝ) : ℝ :=
  ∑ k ∈ (Finset.univ : Finset (Fin n)).erase 0,
    meanRoot α m ^ (α + 1) / (2 * R * Real.sin (Real.pi * (k : ℝ) / (n : ℝ))) ^ α

/-- The complete original radial row dominates the regular rank comparison.
Every nonzero rank, including the even antipodal rank, is included once. -/
theorem referenceRow_le {n : ℕ} [NeZero n] {α : ℝ} (hα : 0 ≤ α) (F : Configuration n α) :
    referenceRow α F.radius F.mass ≤ 2 * F.coefficient * F.radius ^ 2 := by
  classical
  let σ := Tuple.sort F.phase
  let a : Fin n → ℝ := F.phase ∘ σ
  have ha : StrictMono a := (Tuple.monotone_sort F.phase).strictMono_of_injective
    (F.phase_injective.comp σ.injective)
  have ha0 (i : Fin n) : 0 ≤ a i := (positiveAngle_range _).1
  have ha2π (i : Fin n) : a i < 2 * Real.pi := (positiveAngle_range _).2
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hR := F.radius_pos
  let f : Fin n → Fin n → ℝ := fun i j =>
    F.mass (σ j) / ‖F.position (σ j) - F.position (σ i)‖ ^ α
  have hrow (i : Fin n) : (∑ j ∈ Finset.univ.erase i, f i j) = 2 * F.coefficient * F.radius ^ 2 := by
    let g : Fin n → ℝ := fun j => F.mass j / ‖F.position j - F.position (σ i)‖ ^ α
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    change (∑ j, g (σ j)) - g (σ i) = _
    rw [Equiv.sum_comp σ g, ← Finset.sum_erase_eq_sub (Finset.mem_univ (σ i))]
    exact F.radial_row (σ i)
  have hreindex (i : Fin n) :
      (∑ k ∈ (Finset.univ : Finset (Fin n)).erase 0, f i (i + k)) =
        ∑ j ∈ Finset.univ.erase i, f i j := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ 0), Finset.sum_erase_eq_sub (Finset.mem_univ i),
      add_zero]
    exact congrArg (fun x => x - f i i) (Equiv.sum_comp (Equiv.addLeft i) (f i))
  have hs : (Finset.univ : Finset (Fin n)).Nonempty := ⟨0, Finset.mem_univ 0⟩
  have hrank (k : Fin n) (hk : k ∈ (Finset.univ : Finset (Fin n)).erase 0) :
      (n : ℝ) * (meanRoot α F.mass ^ (α + 1) /
        (2 * F.radius * Real.sin (Real.pi * (k : ℝ) / (n : ℝ))) ^ α) ≤
        ∑ i : Fin n, f i (i + k) := by
    let t : Fin n → ℝ := fun i => halfArc a i (i + k)
    let d : Fin n → ℝ := fun i => ‖F.position (σ (i + k)) - F.position (σ i)‖
    let D := 2 * F.radius * Real.sin (Real.pi * (k : ℝ) / (n : ℝ))
    have hk0 : k ≠ 0 := (Finset.mem_erase.mp hk).1
    have hki (i : Fin n) : i + k ≠ i := fun he => hk0 (add_left_cancel (he.trans (add_zero i).symm))
    have ht (i : Fin n) : t i ∈ Set.Ioo 0 Real.pi := halfArc_mem ha ha0 ha2π (hki i)
    have hd (i : Fin n) : 0 < d i := F.chord_pos (σ.injective.ne (hki i))
    have heq (i : Fin n) : d i = 2 * F.radius * Real.sin (t i) :=
      F.chord_eq_halfArc a σ (fun i => F.phase_eq (σ i)) (ht i)
    have hsum : (∑ i, d i) ≤ (n : ℝ) * D := by
      have hb := sine_sum_bound Finset.univ hs t (fun i _ => Set.Ioo_subset_Icc_self (ht i))
      rw [Finset.card_univ, Fintype.card_fin, show (∑ i, t i) = _ from halfArc_rank_sum n a k,
        mul_div_cancel_left₀ _ hn.ne'] at hb
      rw [Finset.sum_congr rfl (fun i _ => heq i), ← Finset.mul_sum]
      calc
        _ ≤ (2 * F.radius) * ((n : ℝ) * Real.sin (Real.pi * (k : ℝ) / (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
        _ = _ := by dsimp [D]; ring
    have hS : 0 < (∑ i, d i) := Finset.sum_pos (fun i _ => hd i) hs
    have hD : 0 < D := by
      have hh : 0 < (n : ℝ) * D := hS.trans_le hsum
      exact pos_of_mul_pos_right hh hn.le
    have hx : 0 ≤ meanRoot α F.mass :=
      div_nonneg (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (F.mass_pos i).le _) hn.le
    have hmass : (∑ i : Fin n, F.mass (σ (i + k)) ^ (1 / (α + 1))) =
        (n : ℝ) * meanRoot α F.mass := by
      calc
        _ = ∑ i : Fin n, F.mass i ^ (1 / (α + 1)) :=
          Equiv.sum_comp ((Equiv.addRight k).trans σ) (fun i => F.mass i ^ (1 / (α + 1)))
        _ = _ := by unfold meanRoot; rw [← mul_div_assoc, mul_div_cancel_left₀ _ hn.ne']
    have hbound := root_bound Finset.univ hs hα (fun i => F.mass (σ (i + k))) d
      (fun i _ => F.mass_pos _) (fun i _ => hd i)
    rw [hmass] at hbound
    apply le_trans _ hbound
    calc
      _ = ((n : ℝ) * meanRoot α F.mass) ^ (α + 1) / ((n : ℝ) * D) ^ α := by
        change (n : ℝ) * (meanRoot α F.mass ^ (α + 1) / D ^ α) = _
        rw [Real.mul_rpow hn.le hx, Real.mul_rpow hn.le hD.le,
          Real.rpow_add hn α 1, Real.rpow_one]
        field_simp [(Real.rpow_pos_of_pos hn α).ne', (Real.rpow_pos_of_pos hD α).ne']
      _ ≤ _ := by
        exact div_le_div_of_nonneg_left (Real.rpow_nonneg (mul_nonneg hn.le hx) _)
          (Real.rpow_pos_of_pos hS _) (Real.rpow_le_rpow hS.le hsum hα)
  apply (mul_le_mul_iff_right₀ hn).mp
  calc
    (n : ℝ) * referenceRow α F.radius F.mass =
        ∑ k ∈ (Finset.univ : Finset (Fin n)).erase 0,
          (n : ℝ) * (meanRoot α F.mass ^ (α + 1) /
            (2 * F.radius * Real.sin (Real.pi * (k : ℝ) / (n : ℝ))) ^ α) := by
      rw [referenceRow, Finset.mul_sum]
    _ ≤ ∑ k ∈ (Finset.univ : Finset (Fin n)).erase 0, ∑ i : Fin n, f i (i + k) :=
      Finset.sum_le_sum hrank
    _ = (n : ℝ) * (2 * F.coefficient * F.radius ^ 2) := by
      rw [Finset.sum_comm]
      simp only [hreindex, hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_comm]

end ACS12.Rank

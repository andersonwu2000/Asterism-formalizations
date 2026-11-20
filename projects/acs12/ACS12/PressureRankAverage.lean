import ACS12.PressureWordCoefficient
import ACS12.PressureOriginalDebit

/-! Full cyclic rank profiles before taking the concave tangent. -/
namespace ACS12.Pressure

open Set CenteredCircle.AllN
open NativeCells (analyticRow analyticRow_pos analyticRow_integer meanMass)

noncomputable def regularRankArc {n : ℕ} (k : Fin n) : ℝ := Real.pi * (k : ℝ) / (n : ℝ)

noncomputable def regularRankWeight {n : ℕ} (p : ℝ) (k : Fin n) : ℝ :=
  angularCost p (regularRankArc k) / analyticRow p (n : ℝ)

private theorem regularRankArc_mem {n : ℕ} {k : Fin n} [NeZero n] (hk : k ≠ 0) :
    regularRankArc k ∈ Ioo 0 Real.pi := by
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hk₀ : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (fun h => hk (Fin.ext h)))
  have hk₁ : (k : ℝ) < (n : ℝ) := Nat.cast_lt.mpr k.isLt
  refine ⟨div_pos (mul_pos Real.pi_pos hk₀) hn,?_⟩
  apply (div_lt_iff₀ hn).mpr
  exact mul_lt_mul_of_pos_left hk₁ Real.pi_pos

private theorem regularRankWeight_zero {n : ℕ} [NeZero n] {p : ℝ} (hp : 0 < p) :
    regularRankWeight p (0 : Fin n) = 0 := by
  simp [regularRankWeight,regularRankArc,angularCost,Real.zero_rpow hp.ne']

private theorem regularRankWeight_sum_one {n : ℕ} [NeZero n] {p : ℝ} (hp : 0 < p)
    (hn : 2 ≤ n) : (∑ k : Fin n, regularRankWeight p k) = 1 := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin n)),regularRankWeight_zero hp,add_zero]
  unfold regularRankWeight regularRankArc
  rw [← Finset.sum_div,← analyticRow_integer hn hp]
  exact div_self (analyticRow_pos hp (Nat.one_lt_cast.mpr (by omega))).ne'

noncomputable def pressureRankWeight {n : ℕ} [NeZero n] (p : ℝ) (i j : Fin n) : ℝ :=
  regularRankWeight p (j - i)

noncomputable def pressureRankMean {n : ℕ} [NeZero n] (p : ℝ) (f : Fin n → Fin n → ℝ) : ℝ :=
  (∑ i : Fin n, ∑ j : Fin n, pressureRankWeight p i j * f i j) / (n : ℝ)

private theorem pressureRankMean_cyclic {n : ℕ} [NeZero n] (p : ℝ) (f : Fin n → Fin n → ℝ) :
    pressureRankMean p f =
      ∑ k : Fin n, regularRankWeight p k * ((∑ i : Fin n, f i (i + k)) / (n : ℝ)) := by
  unfold pressureRankMean
  have hShift (i : Fin n) : (∑ j : Fin n, pressureRankWeight p i j * f i j) =
      ∑ k : Fin n, regularRankWeight p k * f i (i + k) := by
    calc
      _ = ∑ k : Fin n, pressureRankWeight p i (i + k) * f i (i + k) :=
        (Equiv.sum_comp (Equiv.addLeft i) (fun j => pressureRankWeight p i j * f i j)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        simp only [pressureRankWeight,add_comm i k,add_sub_cancel_right]
  simp only [hShift]
  rw [Finset.sum_comm,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.mul_sum,mul_div_assoc]

/-- The full rank mean for any positive symmetric source matrix. -/
theorem pressureRankMean_rpow_le {n : ℕ} [NeZero n] {p : ℝ} (hp : 0 < p) (hn : 2 ≤ n)
    (F : Configuration n p) (b : Fin n → Fin n → ℝ) (hb : ∀ i j, 0 < b i j)
    (hArc : ∀ k : Fin n, (∑ i, halfArc (sortedPressureAngle F) i (i + k)) =
      (n : ℝ) * regularRankArc k) :
    pressureRankMean p (fun i j => b i j ^ (1 / (p + 1))) ^ (p + 1) ≤
      (∑ i : Fin n, ∑ j : Fin n, b i j * angularCost p (halfArc (sortedPressureAngle F) i j)) /
        ((n : ℝ) * analyticRow p (n : ℝ)) := by
  let θ := sortedPressureAngle F
  let S := analyticRow p (n : ℝ)
  let a := 1 / (p + 1)
  let f (k : Fin n) := (∑ i, b i (i + k) ^ a) / (n : ℝ)
  let ω := regularRankWeight (n := n) p
  let c (i j : Fin n) := b i j * angularCost p (halfArc θ i j)
  have hN : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hS : 0 < S := analyticRow_pos hp (Nat.one_lt_cast.mpr (by omega))
  have hF (k : Fin n) : 0 ≤ f k :=
    div_nonneg (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hb i (i + k)).le _) hN.le
  have hW (k : Fin n) : 0 ≤ ω k := by
    by_cases h : k = 0
    · subst k
      exact (regularRankWeight_zero hp).ge
    have h := regularRankArc_mem h
    exact div_nonneg (div_nonneg zero_le_one
      (Real.rpow_nonneg (Real.sin_pos_of_pos_of_lt_pi h.1 h.2).le _)) hS.le
  have hJ := Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ ω f (fun k _ => hW k)
    (regularRankWeight_sum_one hp hn) (fun k _ => hF k) (p := p + 1) (by linarith only [hp])
  have hK (k : Fin n) : ω k * f k ^ (p + 1) ≤ (∑ i : Fin n, c i (i + k)) / ((n : ℝ) * S) := by
    by_cases h : k = 0
    · subst k
      simp [ω,regularRankWeight_zero hp,c,halfArc_self,angularCost,Real.zero_rpow hp.ne']
    let d (i : Fin n) := Real.sin (halfArc θ i (i + k))
    let D := Real.sin (regularRankArc k)
    have hK (i : Fin n) : i + k ≠ i := fun e => h (add_left_cancel (e.trans (add_zero i).symm))
    have hT (i : Fin n) := sortedPressureAngle_mem F (hK i)
    have hd (i : Fin n) : 0 < d i := Real.sin_pos_of_pos_of_lt_pi (hT i).1 (hT i).2
    have hD : 0 < D := Real.sin_pos_of_pos_of_lt_pi (regularRankArc_mem h).1 (regularRankArc_mem h).2
    have hNon : (Finset.univ : Finset (Fin n)).Nonempty := ⟨0,Finset.mem_univ _⟩
    have hSum := Rank.sine_sum_bound Finset.univ hNon (fun i => halfArc θ i (i + k))
      (fun i _ => Ioo_subset_Icc_self (hT i))
    rw [Finset.card_univ,Fintype.card_fin,hArc k,mul_div_cancel_left₀ _ hN.ne'] at hSum
    have hSD : 0 < ∑ i, d i := Finset.sum_pos (fun i _ => hd i) hNon
    have hB := Rank.root_bound Finset.univ hNon hp.le (fun i => b i (i + k)) d
      (fun i _ => hb i (i + k)) (fun i _ => hd i)
    have hRoot : (n : ℝ) * f k ^ (p + 1) / D ^ p ≤ ∑ i : Fin n, c i (i + k) := by
      have hM : (∑ i, b i (i + k) ^ a) = (n : ℝ) * f k := by
        unfold f
        rw [← mul_div_assoc,mul_div_cancel_left₀ _ hN.ne']
      have hQ : ((n : ℝ) * f k) ^ (p + 1) / ((n : ℝ) * D) ^ p =
          (n : ℝ) * f k ^ (p + 1) / D ^ p := by
        rw [Real.mul_rpow hN.le (hF k),Real.mul_rpow hN.le hD.le,
          Real.rpow_add hN,Real.rpow_one]
        field_simp [(Real.rpow_pos_of_pos hN p).ne',(Real.rpow_pos_of_pos hD p).ne']
      rw [← hQ,← hM]
      have hNum : 0 ≤ (∑ i : Fin n, b i (i + k) ^ a) ^ (p + 1) :=
        Real.rpow_nonneg (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hb i (i + k)).le a) _
      have hR := div_le_div_of_nonneg_left hNum
        (Real.rpow_pos_of_pos hSD p) (Real.rpow_le_rpow hSD.le hSum hp.le)
      exact hR.trans (by simpa only [a,c,d,angularCost,div_eq_mul_inv,one_mul] using hB)
    apply (le_div_iff₀ (mul_pos hN hS)).mpr
    change (1 / D ^ p / S * f k ^ (p + 1)) * ((n : ℝ) * S) ≤ _
    have hEq : (1 / D ^ p / S * f k ^ (p + 1)) * ((n : ℝ) * S) =
        (n : ℝ) * f k ^ (p + 1) / D ^ p := by
      field_simp [hS.ne',(Real.rpow_pos_of_pos hD p).ne'] <;> ring
    exact hEq.le.trans hRoot
  have hReindex : (∑ k : Fin n, ∑ i : Fin n, c i (i + k)) = ∑ i : Fin n, ∑ j : Fin n, c i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    exact Equiv.sum_comp (Equiv.addLeft i) (c i)
  rw [pressureRankMean_cyclic]
  refine hJ.trans ?_
  have h := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin n))) => hK k)
  rwa [← Finset.sum_div,hReindex] at h

private theorem pressureRankMean_pair_mean {n : ℕ} [NeZero n] {p : ℝ} (hp : 0 < p) (hn : 2 ≤ n)
    (u : Fin n → ℝ) :
    pressureRankMean p (fun i j => (u i + u j) / 2) = (∑ i, u i) / (n : ℝ) := by
  rw [pressureRankMean_cyclic]
  have hU (k : Fin n) : (∑ i : Fin n, (u i + u (i + k)) / 2) = ∑ i, u i := by
    rw [← Finset.sum_div,Finset.sum_add_distrib,show (∑ i, u (i + k)) = ∑ i, u i from
      Equiv.sum_comp (Equiv.addRight k) u,← two_mul,mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  simp only [hU,← Finset.sum_mul,regularRankWeight_sum_one hp hn,one_mul]

private theorem pressureRankMean_sub {n : ℕ} [NeZero n] (p : ℝ) (f g : Fin n → Fin n → ℝ) :
    pressureRankMean p (fun i j => f i j - g i j) = pressureRankMean p f - pressureRankMean p g := by
  simp only [pressureRankMean,mul_sub,Finset.sum_sub_distrib,sub_div]

private theorem pressureRankMean_add {n : ℕ} [NeZero n] (p : ℝ) (f g : Fin n → Fin n → ℝ) :
    pressureRankMean p (fun i j => f i j + g i j) = pressureRankMean p f + pressureRankMean p g := by
  simp only [pressureRankMean,mul_add,Finset.sum_add_distrib,add_div]

private theorem pressureRank_source_sum {n : ℕ} {p : ℝ} (hp : 0 < p) (F : Configuration n p)
    (u : Fin n → ℝ) :
    let m := sortedPressureMass F
    let θ := sortedPressureAngle F
    (∑ i : Fin n, ∑ j : Fin n, ((u i * m j + u j * m i) / 2) *
      angularCost p (halfArc θ i j)) = (∑ i, u i) * originalPressureRow F := by
  dsimp only
  let m := sortedPressureMass F
  let θ := sortedPressureAngle F
  let K (i j : Fin n) := angularCost p (halfArc θ i j)
  have hSym (i j : Fin n) : K j i = K i j := by
    by_cases h : i = j
    · subst j
      rfl
    unfold K
    rw [halfArc_reverse θ h,angularCost,Real.sin_pi_sub,angularCost]
  have hOne : (∑ i : Fin n, ∑ j : Fin n, u i * (m j * K i j)) = (∑ i, u i) * originalPressureRow F := by
    simp only [← Finset.mul_sum,show ∀ i : Fin n, (∑ j, m j * K i j) = originalPressureRow F from
      sortedPressure_radial hp F,← Finset.sum_mul]
  have hTwo : (∑ i : Fin n, ∑ j : Fin n, u j * (m i * K i j)) = (∑ i, u i) * originalPressureRow F := by
    rw [Finset.sum_comm]
    simp only [hSym]
    exact hOne
  have hEq (i j : Fin n) :
      ((u i * m j + u j * m i) / 2) * K i j = (u i * (m j * K i j) + u j * (m i * K i j)) / 2 := by ring
  change (∑ i : Fin n, ∑ j : Fin n, ((u i * m j + u j * m i) / 2) * K i j) = _
  simp only [hEq,← Finset.sum_div,Finset.sum_add_distrib,hOne,hTwo]
  ring

theorem pressureRank_original_profiles {n : ℕ} [NeZero n] {p : ℝ} (hp : 0 < p) (hn : 2 ≤ n)
    (F : Configuration n p)
    (hArc : ∀ k : Fin n, (∑ i, halfArc (sortedPressureAngle F) i (i + k)) =
      (n : ℝ) * regularRankArc k) :
    let m := sortedPressureMass F
    let a := 1 / (p + 1)
    let U := pressureMeanPower p m
    let E := pressureRankE F
    Rank.meanRoot p m + pressureRankMean p (fun i j => originalGapG p (m i) (m j)) ≤ E ^ a ∧
      U - pressureRankMean p (fun i j => originalGapD p (m i) (m j)) ≤ U ^ a * E ^ a := by
  dsimp only
  let m := sortedPressureMass F
  let u (i : Fin n) := m i ^ (1 / p)
  let U := pressureMeanPower p m
  let A := Rank.meanRoot p m
  let E := pressureRankE F
  let S := analyticRow p (n : ℝ)
  let C := originalPressureRow F
  let a := 1 / (p + 1)
  let bG (i j : Fin n) := (m j + m i) / 2
  let bD (i j : Fin n) := (u i * m j + u j * m i) / 2
  let G (i j : Fin n) := originalGapG p (m i) (m j)
  let D (i j : Fin n) := originalGapD p (m i) (m j)
  have hm (i : Fin n) : 0 < m i := F.mass_pos _
  have hu (i : Fin n) : 0 < u i := Real.rpow_pos_of_pos (hm i) _
  have hBG (i j : Fin n) : 0 < bG i j := div_pos (add_pos (hm j) (hm i)) (by norm_num)
  have hBD (i j : Fin n) : 0 < bD i j :=
    div_pos (add_pos (mul_pos (hu i) (hm j)) (mul_pos (hu j) (hm i))) (by norm_num)
  have hN : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hS : 0 < S := analyticRow_pos hp (Nat.one_lt_cast.mpr (by omega))
  have hC : 0 < C := originalPressureRow_pos hn F
  have ha : 0 < a := by unfold a; positivity
  have hInv : (p + 1) * a = 1 := by unfold a; field_simp
  have hU : 0 < U := div_pos (Finset.sum_pos (fun i _ => hu i) ⟨0,Finset.mem_univ _⟩) hN
  have hE : 0 < E := div_pos hC hS
  have hOne := pressureRankMean_rpow_le hp hn F bG hBG hArc
  have hTwo := pressureRankMean_rpow_le hp hn F bD hBD hArc
  have hEqG : (∑ i, ∑ j, bG i j * angularCost p (halfArc (sortedPressureAngle F) i j)) = (n : ℝ) * C := by
    have h := pressureRank_source_sum hp F (fun _ => 1)
    simpa only [bG,C,one_mul,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,mul_one] using h
  have hEqD : (∑ i, ∑ j, bD i j * angularCost p (halfArc (sortedPressureAngle F) i j)) = (n : ℝ) * U * C := by
    have h := pressureRank_source_sum hp F u
    change (∑ i, ∑ j, bD i j * angularCost p (halfArc (sortedPressureAngle F) i j)) = _
    rw [h,show (n : ℝ) * U = ∑ i, u i by unfold U pressureMeanPower u; rw [← mul_div_assoc,mul_div_cancel_left₀ _ hN.ne']]
  rw [hEqG] at hOne
  rw [hEqD] at hTwo
  have hEG : (n : ℝ) * C / ((n : ℝ) * S) = E := by change _ = C / S; field_simp [hN.ne',hS.ne']
  have hED : (n : ℝ) * U * C / ((n : ℝ) * S) = U * E := by change _ = U * (C / S); field_simp [hN.ne',hS.ne']
  rw [hEG] at hOne
  rw [hED] at hTwo
  have hMeanPos (f : Fin n → Fin n → ℝ) (hf : ∀ i j, 0 ≤ f i j) : 0 ≤ pressureRankMean p f := by
    rw [pressureRankMean_cyclic]
    apply Finset.sum_nonneg
    intro k _
    have hK : 0 ≤ regularRankWeight p k := by
      by_cases h : k = 0
      · subst k; exact (regularRankWeight_zero hp).ge
      · have ht := regularRankArc_mem h
        exact div_nonneg (div_nonneg zero_le_one (Real.rpow_nonneg (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2).le _)) hS.le
    exact mul_nonneg hK (div_nonneg (Finset.sum_nonneg fun i _ => hf i (i + k)) hN.le)
  let FG := pressureRankMean p (fun i j => bG i j ^ a)
  let FD := pressureRankMean p (fun i j => bD i j ^ a)
  have hFG : 0 ≤ FG := hMeanPos _ fun i j => Real.rpow_nonneg (hBG i j).le _
  have hFD : 0 ≤ FD := hMeanPos _ fun i j => Real.rpow_nonneg (hBD i j).le _
  have hG := Real.rpow_le_rpow (Real.rpow_nonneg hFG _) hOne ha.le
  have hD := Real.rpow_le_rpow (Real.rpow_nonneg hFD _) hTwo ha.le
  change (FG ^ (p + 1)) ^ a ≤ E ^ a at hG
  change (FD ^ (p + 1)) ^ a ≤ (U * E) ^ a at hD
  rw [← Real.rpow_mul hFG,hInv,Real.rpow_one] at hG
  rw [← Real.rpow_mul hFD,hInv,Real.rpow_one,Real.mul_rpow hU.le hE.le] at hD
  have hFG' : FG = A + pressureRankMean p G := by
    unfold FG
    rw [show (fun i j => bG i j ^ a) = fun i j => (m i ^ a + m j ^ a) / 2 + G i j by
      funext i j; unfold G originalGapG bG a; ring,
      pressureRankMean_add,pressureRankMean_pair_mean hp hn]
    rfl
  have hFD' : FD = U - pressureRankMean p D := by
    unfold FD
    rw [show (fun i j => bD i j ^ a) = fun i j => (u i + u j) / 2 - D i j by
      funext i j; unfold D originalGapD bD a u; ring,
      pressureRankMean_sub,pressureRankMean_pair_mean hp hn]
    rfl
  rw [hFG'] at hG
  rw [hFD'] at hD
  exact ⟨hG,hD⟩

theorem weightedPressureRank_necessary {n : ℕ} [NeZero n] {p lam : ℝ} (hp : 1 < p) (hp₂ : p ≤ 2)
    (hlam : 0 ≤ lam) (hn : 2 ≤ n) (F : Configuration n p)
    (hArc : ∀ k : Fin n, (∑ i, halfArc (sortedPressureAngle F) i (i + k)) =
      (n : ℝ) * regularRankArc k)
    (hGap : ∀ i j, originalGapD p (sortedPressureMass F i) (sortedPressureMass F j) ≤
      lam * originalGapG p (sortedPressureMass F i) (sortedPressureMass F j)) :
    let m := sortedPressureMass F
    let a := 1 / (p + 1)
    let U := pressureMeanPower p m
    pairFlatTotal F * (lam * Rank.meanRoot p m + U) ≤ (lam + U ^ a) * pressureW F := by
  dsimp only
  let m := sortedPressureMass F
  let a := 1 / (p + 1)
  let U := pressureMeanPower p m
  let A := Rank.meanRoot p m
  let E := pressureRankE F
  let Q := pairFlatTotal F
  let W := pressureW F
  let S := analyticRow p (n : ℝ)
  have hp₀ := zero_lt_one.trans hp
  have hQ := zero_lt_one.trans_le (pairFlatTotal_ge_one hp₀ hn F)
  have hS := analyticRow_pos hp₀ (Nat.one_lt_cast.mpr (show 1 < n by omega))
  have hE : 0 < E := div_pos (originalPressureRow_pos hn F) hS
  have ha : 0 < a := by unfold a; positivity
  have hU : 0 ≤ U := by
    unfold U pressureMeanPower
    exact div_nonneg (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (F.mass_pos _).le _) (Nat.cast_nonneg _)
  have hB : 0 ≤ lam + U ^ a := add_nonneg hlam (Real.rpow_nonneg hU _)
  have hCell := pressure_pristine_le hp hp₂ hn F
  have hCell' : E * Q ^ (p + 1) ≤ geometricPressureRow F / S := by
    change originalPressureRow F / S * Q ^ (p + 1) ≤ _
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hCell hS.le
  have hRoot := Real.rpow_le_rpow (mul_nonneg hE.le (Real.rpow_nonneg hQ.le _)) hCell' ha.le
  change (E * Q ^ (p + 1)) ^ a ≤ W at hRoot
  rw [Real.mul_rpow hE.le (Real.rpow_nonneg hQ.le _),← Real.rpow_mul hQ.le,
    show (p + 1) * a = 1 by unfold a; field_simp,Real.rpow_one] at hRoot
  have hDebit : pressureRankMean p (fun i j => originalGapD p (m i) (m j)) ≤
      lam * pressureRankMean p (fun i j => originalGapG p (m i) (m j)) := by
    simp only [pressureRankMean_cyclic,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    have hK : 0 ≤ regularRankWeight p k := by
      by_cases h : k = 0
      · subst k; exact (regularRankWeight_zero hp₀).ge
      · have ht := regularRankArc_mem h
        exact div_nonneg (div_nonneg zero_le_one (Real.rpow_nonneg (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2).le _)) hS.le
    apply le_trans (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
      (Finset.sum_le_sum (fun i _ => hGap i (i + k))) (Nat.cast_nonneg _)) hK)
    rw [← Finset.mul_sum]
    unfold m
    ring_nf
    exact le_rfl
  obtain ⟨hG,hD⟩ := pressureRank_original_profiles hp₀ hn F hArc
  have hRank : lam * A + U ≤ (lam + U ^ a) * E ^ a := by
    have hG' := mul_le_mul_of_nonneg_left hG hlam
    linarith only [hG',hD,hDebit]
  calc
    _ ≤ Q * ((lam + U ^ a) * E ^ a) := mul_le_mul_of_nonneg_left hRank hQ.le
    _ = (lam + U ^ a) * (E ^ a * Q) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hRoot hB

end ACS12.Pressure

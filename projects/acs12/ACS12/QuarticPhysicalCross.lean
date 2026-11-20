import ACS12.QuarticArcKernel
import ACS12.HighPhysicalArc
import ACS12.HighPhysicalRectangle
import ACS12.QuarticCrossPrice

/-! Apply both occupied half-arcs to the original nonincident current of one cut. -/
namespace ACS12.Configuration

open Finset HighCurrent
set_option backward.isDefEq.respectTransparency false

noncomputable def shorterHalfAngle {n : ℕ} {p : ℝ} (F : Configuration n p) (r j : Fin n) : ℝ :=
  min (halfArc F.currentAngles r j) (Real.pi - halfArc F.currentAngles r j)

theorem shorterHalfAngle_range {n : ℕ} {p : ℝ} (F : Configuration n p)
    {r j : Fin n} (hj : j ≠ r) :
    0 < F.shorterHalfAngle r j ∧ F.shorterHalfAngle r j ≤ Real.pi / 2 := by
  have h := halfArc_mem F.currentAngles_strictMono F.currentAngles_nonneg F.currentAngles_lt_two_pi hj
  refine ⟨lt_min h.1 (sub_pos.mpr h.2), ?_⟩
  rw [shorterHalfAngle]
  by_cases hθ : halfArc F.currentAngles r j ≤ Real.pi / 2
  · exact (min_le_left _ _).trans hθ
  · exact (min_le_right _ _).trans (by linarith only [le_of_not_ge hθ])

theorem shorterHalfAngle_chord {n : ℕ} {p : ℝ} (F : Configuration n p)
    {r j : Fin n} (hj : j ≠ r) :
    F.currentChord r j = (2 * F.radius) * Real.sin (F.shorterHalfAngle r j) := by
  have h := halfArc_mem F.currentAngles_strictMono F.currentAngles_nonneg F.currentAngles_lt_two_pi hj
  rw [currentChord, F.chord_eq_halfArc F.currentAngles F.currentOrder (fun k => F.phase_eq (F.currentOrder k)) h]
  unfold shorterHalfAngle
  rcases le_total (halfArc F.currentAngles r j) (Real.pi - halfArc F.currentAngles r j) with hOrd | hOrd
  · rw [min_eq_left hOrd]
  · rw [min_eq_right hOrd, Real.sin_pi_sub]

variable {n : ℕ} {p : ℝ} (F : Configuration n p)

private theorem nonincident_cut_le_arc_sum (r : Fin n) :
    let D := 2 * F.radius
    let E := (univ : Finset (Fin n)).erase r
    let A := E.filter (fun i => Real.pi / 2 < halfArc F.currentAngles r i)
    let B := E.filter (fun j => halfArc F.currentAngles r j < Real.pi / 2)
    let t (i : Fin n) := Real.pi - halfArc F.currentAngles r i
    let s (j : Fin n) := halfArc F.currentAngles r j
    let m := F.currentMasses
    F.nonincidentCurrent r ≤ D ^ 2 / D ^ (p + 1) *
      ∑ i ∈ A, ∑ j ∈ B, (m i / D) * (m j / D) * quarticArcKernel p (t i + s j) := by
  dsimp only
  let D := 2 * F.radius
  let E := (univ : Finset (Fin n)).erase r
  let t (i : Fin n) := Real.pi - halfArc F.currentAngles r i
  let s (j : Fin n) := halfArc F.currentAngles r j
  let m := F.currentMasses
  let g (i j : Fin n) :=
    D ^ 2 / D ^ (p + 1) * ((m i / D) * (m j / D) * quarticArcKernel p (t i + s j))
  have hD : 0 < D := mul_pos zero_lt_two F.radius_pos
  have hArc (j : Fin n) (hj : j ∈ E) : s j ∈ Set.Ioo 0 Real.pi :=
    halfArc_mem F.currentAngles_strictMono F.currentAngles_nonneg F.currentAngles_lt_two_pi (mem_erase.mp hj).1
  have hNon (i j : Fin n) (hi : i ∈ E) (hj : j ∈ E) : 0 ≤ g i j := by
    have ht : 0 < t i := sub_pos.mpr (hArc i hi).2
    have hs := (hArc j hj).1
    have hK := quarticArcKernel_nonneg p (add_pos ht hs)
    have hm₁ : 0 < m i := F.mass_pos _
    have hm₂ : 0 < m j := F.mass_pos _
    unfold g
    positivity
  have hPair (i : Fin n) (hi : i ∈ E) (j : Fin n) (hj : j ∈ E) :
      F.currentEdges i j * cutIndicator (F.currentAngles i) (F.currentAngles j) (F.currentAngles r) ≤
        if Real.pi / 2 < s i then (if s j < Real.pi / 2 then g i j else 0) else 0 := by
    have hR : 0 ≤ if Real.pi / 2 < s i then (if s j < Real.pi / 2 then g i j else 0) else 0 := by
      split_ifs <;> first | exact hNon i j hi hj | exact le_rfl
    by_cases hij : i = j
    · rw [hij, F.currentEdges_diagonal, zero_mul]
      simpa only [hij] using hR
    by_cases hShort : halfArc F.currentAngles i j < Real.pi / 2
    · rcases cutIndicator_zero_or_one (F.currentAngles i) (F.currentAngles j) (F.currentAngles r) with h | h
      · rwa [h, mul_zero]
      · have hGeo := crossing_cut_halfArcs F.currentAngles F.currentAngles_strictMono
          F.currentAngles_nonneg F.currentAngles_lt_two_pi (mem_erase.mp hi).1 (mem_erase.mp hj).1 hij hShort h
        have hArcIJ := halfArc_mem F.currentAngles_strictMono F.currentAngles_nonneg
          F.currentAngles_lt_two_pi (Ne.symm hij)
        have hθ : t i + s j = halfArc F.currentAngles i j := hGeo.2.2.symm
        rw [h, mul_one, if_pos hGeo.1, if_pos hGeo.2.1, F.currentEdge_chord hij hShort,
          F.chord_eq_halfArc F.currentAngles F.currentOrder (fun k => F.phase_eq (F.currentOrder k)) hArcIJ]
        unfold g
        rw [hθ, quarticArcKernel_value p hArcIJ.1 hShort.le, Real.mul_rpow hD.le
          (Real.sin_pos_of_pos_of_lt_pi hArcIJ.1 hArcIJ.2).le]
        change m i * m j * Real.cos (halfArc F.currentAngles i j) /
            (D ^ (p + 1) * Real.sin (halfArc F.currentAngles i j) ^ (p + 1)) ≤ _
        have hSi := Real.rpow_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi hArcIJ.1 hArcIJ.2) (p + 1)
        have hDp := Real.rpow_pos_of_pos hD (p + 1)
        apply le_of_eq
        field_simp [hD.ne', hDp.ne', hSi.ne']
    · have hZero : F.currentEdges i j = 0 := by
        unfold currentEdges shorterCurrent
        rw [if_neg hij, if_neg hShort]
      rwa [hZero, zero_mul]
  have h := sum_le_sum (s := E) (fun i hi => sum_le_sum (s := E) (fun j hj => hPair i hi j hj))
  have hSum (i : Fin n) :
      (∑ j ∈ E, if Real.pi / 2 < s i then (if s j < Real.pi / 2 then g i j else 0) else 0) =
        if Real.pi / 2 < s i then ∑ j ∈ E.filter (fun j => s j < Real.pi / 2), g i j else 0 := by
    split_ifs <;> simp only [sum_filter, sum_const_zero]
  simp_rw [hSum, ← sum_filter] at h
  change F.nonincidentCurrent r ≤ _
  convert h using 1
  unfold g s
  simp only [mul_sum]
  rfl

/-- Every nonincident crossing is paid from the full radial row of the marked label. -/
theorem radialUnitSource_quartic_crossing (hn : 2 ≤ n) (hp : 4 ≤ p)
    (o : Fin n) (hMax : ∀ j, F.mass j ≤ F.mass o) (r : Fin n) :
    let G := F.radialUnitSource hn o
    2 * G.nonincidentCurrent r ≤ ∑ j ∈ univ.erase r,
      G.currentMasses j / G.currentChord r j ^ p * quarticCrossPrice p (G.shorterHalfAngle r j) := by
  let G := F.radialUnitSource hn o
  let D := 2 * G.radius
  let L := Real.pi / 2
  let K := quarticArcKernel p
  let E := (univ : Finset (Fin n)).erase r
  let s (j : Fin n) := halfArc G.currentAngles r j
  let t (j : Fin n) := Real.pi - s j
  let A := E.filter (fun j => L < s j)
  let B := E.filter (fun j => s j < L)
  let m (j : Fin n) := G.currentMasses j / D
  let C := D ^ 2 / D ^ (p + 1)
  have hD : 0 < D := mul_pos zero_lt_two G.radius_pos
  have hL : 0 < L := by dsimp only [L]; positivity
  have hp₁ : 1 ≤ p := by linarith only [hp]
  have hp₀ := zero_lt_one.trans_le hp₁
  have hArc (j : Fin n) (hj : j ∈ E) : s j ∈ Set.Ioo 0 Real.pi :=
    halfArc_mem G.currentAngles_strictMono G.currentAngles_nonneg G.currentAngles_lt_two_pi (mem_erase.mp hj).1
  have hA (j : Fin n) (hj : j ∈ A) : t j ∈ Set.Icc 0 L := by
    have h := mem_filter.mp hj
    exact ⟨(sub_pos.mpr (hArc j h.1).2).le, by dsimp [t, L] at *; linarith only [h.2]⟩
  have hB (j : Fin n) (hj : j ∈ B) : s j ∈ Set.Icc 0 L :=
    ⟨(hArc j (mem_filter.mp hj).1).1.le, (mem_filter.mp hj).2.le⟩
  have hFirstA (j : Fin n) (hj : j ∈ A) : m j ≤ t j := by
    have hjr : j ≠ r := (mem_erase.mp (mem_filter.mp hj).1).1
    apply (div_le_iff₀ hD).mpr
    rw [mul_comm _ D]
    exact (F.radialUnitSource_mass_le_chord hn hp₁ o hMax _ _ (G.currentOrder.injective.ne hjr)).trans
      (G.currentBackwardArc_root_chord hjr)
  have hFirstB (j : Fin n) (hj : j ∈ B) : m j ≤ s j := by
    have hjr : j ≠ r := (mem_erase.mp (mem_filter.mp hj).1).1
    apply (div_le_iff₀ hD).mpr
    rw [mul_comm _ D]
    exact (F.radialUnitSource_mass_le_chord hn hp₁ o hMax _ _ (G.currentOrder.injective.ne hjr)).trans
      (G.currentForwardArc_root_chord hjr)
  have hPackA (i : Fin n) (_ : i ∈ A) (j : Fin n) (_ : j ∈ A) (hij : i ≠ j) :
      m i ≤ |t i - t j| := by
    apply (div_le_iff₀ hD).mpr
    have h := (F.radialUnitSource_mass_le_chord hn hp₁ o hMax _ _ (G.currentOrder.injective.ne hij)).trans
      (G.currentBackwardArc_pair_chord r i j)
    have hEq : G.currentBackwardArc r i - G.currentBackwardArc r j = D * (t i - t j) := by
      dsimp only [currentBackwardArc, t, s, D]
      ring
    rw [hEq, abs_mul, abs_of_pos hD, mul_comm D] at h
    exact h
  have hPackB (i : Fin n) (_ : i ∈ B) (j : Fin n) (_ : j ∈ B) (hij : i ≠ j) :
      m i ≤ |s i - s j| := by
    apply (div_le_iff₀ hD).mpr
    have h := (F.radialUnitSource_mass_le_chord hn hp₁ o hMax _ _ (G.currentOrder.injective.ne hij)).trans
      (G.currentForwardArc_pair_chord r i j)
    have hEq : G.currentForwardArc r i - G.currentForwardArc r j = D * (s i - s j) := by
      dsimp only [currentForwardArc, s, D]
      ring
    rw [hEq, abs_mul, abs_of_pos hD, mul_comm D] at h
    exact h
  have hP := quartic_crossing_primitive A B t s m hL.le (quarticArcKernel_convex hp₀.le)
    (quarticArcKernel_continuousOn hp₀.le) (fun _ hz => quarticArcKernel_nonneg p hz)
    (quarticArcKernel_antitone hp₀.le) (fun j _ => div_pos (G.mass_pos _) hD)
    hA hB hFirstA hFirstB hPackA hPackB
  have hPaid := (nonincident_cut_le_arc_sum G r).trans
    (mul_le_mul_of_nonneg_left hP (show 0 ≤ C by dsimp only [C]; positivity))
  let f (j : Fin n) := m j * ∫ v in (0 : ℝ)..L, crossSlice K (G.shorterHalfAngle r j) v
  have hEqA (j : Fin n) (hj : j ∈ A) : G.shorterHalfAngle r j = t j := by
    unfold shorterHalfAngle
    have h := (mem_filter.mp hj).2
    change L < s j at h
    exact min_eq_right (by dsimp only [t, L] at *; linarith only [h])
  have hEqB (j : Fin n) (hj : j ∈ B) : G.shorterHalfAngle r j = s j := by
    unfold shorterHalfAngle
    have h := (mem_filter.mp hj).2
    change s j < L at h
    exact min_eq_left (by dsimp only [L] at *; linarith only [h])
  have hAd : Disjoint A B := disjoint_left.mpr (fun j hj hjB =>
    lt_asymm (mem_filter.mp hj).2 (mem_filter.mp hjB).2)
  have hSubset : A ∪ B ⊆ E := Finset.union_subset (filter_subset _ _) (filter_subset _ _)
  have hf (j : Fin n) (hj : j ∈ E) : 0 ≤ f j := by
    have hθ := (G.shorterHalfAngle_range (mem_erase.mp hj).1).1
    exact mul_nonneg (div_pos (G.mass_pos _) hD).le (intervalIntegral.integral_nonneg hL.le
      (fun v _ => crossSlice_nonneg (fun y hy => quarticArcKernel_nonneg p hy) (quarticArcKernel_antitone hp₀.le) hθ))
  have hAll : G.nonincidentCurrent r ≤ C * ∑ j ∈ E, f j := by
    have hC : 0 ≤ C := div_nonneg (sq_nonneg D) (Real.rpow_nonneg hD.le _)
    refine hPaid.trans (mul_le_mul_of_nonneg_left ?_ hC)
    have hAA : (∑ i ∈ A, m i * ∫ v in (0 : ℝ)..L, crossSlice K (t i) v) = ∑ j ∈ A, f j :=
      sum_congr rfl (fun i hi => by dsimp only [f]; rw [hEqA i hi])
    have hBB : (∑ i ∈ B, m i * ∫ v in (0 : ℝ)..L, crossSlice K (s i) v) = ∑ j ∈ B, f j :=
      sum_congr rfl (fun i hi => by dsimp only [f]; rw [hEqB i hi])
    rw [hAA, hBB, ← sum_union hAd]
    exact sum_le_sum_of_subset_of_nonneg hSubset (fun i hi _ => hf i hi)
  have hTerm (j : Fin n) (hj : j ∈ E) :
      (2 * C) * f j = G.currentMasses j / G.currentChord r j ^ p * quarticCrossPrice p (G.shorterHalfAngle r j) := by
    let θ := G.shorterHalfAngle r j
    have hθ := G.shorterHalfAngle_range (mem_erase.mp hj).1
    have hSin := Real.sin_pos_of_pos_of_lt_pi hθ.1 (hθ.2.trans_lt (by linarith only [Real.pi_pos]))
    have hSlice := quarticArcKernel_slice_eq hp₀ hθ.1 hθ.2
    change 2 * (∫ v in (0 : ℝ)..L, crossSlice K θ v) =
      Real.sin θ ^ (-p) * quarticCrossPrice p θ at hSlice
    change 2 * C * (m j * ∫ v in (0 : ℝ)..L, crossSlice K θ v) = _
    rw [show ∀ I : ℝ, 2 * C * (m j * I) = (C * m j) * (2 * I) from fun I => by ring, hSlice,
      G.shorterHalfAngle_chord (mem_erase.mp hj).1, Real.mul_rpow hD.le hSin.le,
      Real.rpow_neg hSin.le]
    dsimp only [C, m]
    rw [Real.rpow_add hD, Real.rpow_one]
    field_simp [hD.ne', (Real.rpow_pos_of_pos hD p).ne', (Real.rpow_pos_of_pos hSin p).ne']
    ring
  have h := mul_le_mul_of_nonneg_left hAll (show (0 : ℝ) ≤ 2 by norm_num)
  rw [← mul_assoc, mul_sum, sum_congr rfl hTerm] at h
  exact h

end ACS12.Configuration

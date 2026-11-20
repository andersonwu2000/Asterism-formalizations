import ACS12.GammaTorque

/-! Transport of both complete periodic rays across an original occupied gap. -/
namespace ACS12.Pressure

open CenteredCircle.AllN Set

noncomputable def periodicDen (L s : ℝ) : ℝ := 1 - Real.exp (-s * L)

theorem periodicDen_pos {L s : ℝ} (hL : 0 < L) (hs : 0 < s) : 0 < periodicDen L s :=
  sub_pos.mpr (Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hs) hL))

noncomputable def rayWeight {n : ℕ} (L : ℝ) (m d : Fin n → ℝ) (s : ℝ) : ℝ :=
  ∑ j, m j * (Real.exp (-s * d j) / periodicDen L s)

theorem shifted_ray_eq {n : ℕ} (L : ℝ) (m d : Fin n → ℝ) (s : ℝ) :
    Real.exp (-s) * rayWeight L m d s = rayWeight L m (fun i => d i + 1) s := by
  unfold rayWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_add,Real.exp_add,mul_one]
  ring


noncomputable def leftRay {n : ℕ} (S : AnchoredCircleSource (Fin n)) (i : Fin n) (s : ℝ) : ℝ :=
  rayWeight S.period S.mass (fun j => S.forwardDistance j i) s

noncomputable def rightRay {n : ℕ} (S : AnchoredCircleSource (Fin n)) (i : Fin n) (s : ℝ) : ℝ :=
  rayWeight S.period S.mass (S.forwardDistance i) s

theorem rayWeight_shift {n : ℕ} {L s d : ℝ} (hL : 0 < L) (hs : 0 < s)
    (m a b : Fin n → ℝ) (i : Fin n) (ha : a i = L) (hb : b i = d)
    (h : ∀ j ≠ i, b j = a j + d) :
    rayWeight L m b s = Real.exp (-s * d) * (rayWeight L m a s + m i) := by
  have hDen := (periodicDen_pos hL hs).ne'
  have hEntry (j : Fin n) (hj : j ∈ Finset.univ.erase i) :
      m j * (Real.exp (-s * b j) / periodicDen L s) =
        Real.exp (-s * d) * (m j * (Real.exp (-s * a j) / periodicDen L s)) := by
    rw [h j (Finset.mem_erase.mp hj).1, mul_add, Real.exp_add]
    ring
  have hI : m i * (Real.exp (-s * d) / periodicDen L s) =
      Real.exp (-s * d) * (m i * (Real.exp (-s * L) / periodicDen L s) + m i) := by
    field_simp [hDen]
    unfold periodicDen
    ring
  unfold rayWeight
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), ← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    ha,hb,Finset.sum_congr rfl hEntry,← Finset.mul_sum,hI]
  ring

theorem consecutive_ray_transport {n : ℕ} (S : AnchoredCircleSource (Fin n)) {i j : Fin n}
    (hij : S.coordinate i < S.coordinate j)
    (h : ∀ k, ¬(S.coordinate i < S.coordinate k ∧ S.coordinate k < S.coordinate j))
    {s : ℝ} (hs : 0 < s) :
    leftRay S j s = Real.exp (-s * S.forwardDistance i j) * (leftRay S i s + S.mass i) ∧
    rightRay S i s = Real.exp (-s * S.forwardDistance i j) * (rightRay S j s + S.mass j) := by
  have hne : i ≠ j := fun he => hij.ne (congrArg S.coordinate he)
  constructor
  · apply rayWeight_shift S.period_pos hs S.mass (fun k => S.forwardDistance k i)
      (fun k => S.forwardDistance k j) i (S.forwardDistance_self i) rfl
    intro k hk
    by_cases hk' : k = j
    · subst k
      rw [S.forwardDistance_self j, S.forwardDistance_flip hne]
      ring
    · exact (S.consecutive_distance_split hij h hk hk').2
  · apply rayWeight_shift S.period_pos hs S.mass (S.forwardDistance j)
      (S.forwardDistance i) j (S.forwardDistance_self j) rfl
    intro k hk
    by_cases hk' : k = i
    · subst k
      rw [S.forwardDistance_self i, S.forwardDistance_flip hne]
      ring
    · exact (S.consecutive_distance_split hij h hk' hk).1

theorem consecutive_ray_product {n : ℕ} (S : AnchoredCircleSource (Fin n)) {i j : Fin n}
    (hij : S.coordinate i < S.coordinate j)
    (h : ∀ k, ¬(S.coordinate i < S.coordinate k ∧ S.coordinate k < S.coordinate j))
    {s : ℝ} (hs : 0 < s) :
    (leftRay S i s + S.mass i) * rightRay S i s =
      leftRay S j s * (rightRay S j s + S.mass j) := by
  obtain ⟨hL,hR⟩ := consecutive_ray_transport S hij h hs
  rw [hL,hR]
  ring

end ACS12.Pressure

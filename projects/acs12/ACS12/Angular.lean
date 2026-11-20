import ACS12.Converse
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Data.Fin.Tuple.Sort

/-! For a common mass, compare the angular rows with those of a regular polygon.
At an index of maximal angular displacement every oriented arc is at most its
regular counterpart. Strict decrease of the torque kernel forces equality. -/

namespace ACS12

open scoped BigOperators
open CenteredCircle.AllN
set_option backward.isDefEq.respectTransparency false

noncomputable def angularKernel (α t : ℝ) : ℝ :=
  Real.cos t / Real.sin t ^ (α + 1)

theorem angularKernel_strictAnti (α : ℝ) (hα : 0 ≤ α) :
    StrictAntiOn (angularKernel α) (Set.Ioo 0 Real.pi) := by
  have hderiv (x : ℝ) (hx : x ∈ Set.Ioo 0 Real.pi) :
      HasDerivAt (angularKernel α)
        (-(Real.sin x ^ 2 + (α + 1) * Real.cos x ^ 2) /
          (Real.sin x * Real.sin x ^ (α + 1))) x := by
    have hs := Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
    have hp := Real.rpow_pos_of_pos hs (α + 1)
    have h := (Real.hasDerivAt_cos x).div
      ((Real.hasDerivAt_sin x).rpow_const (p := α + 1) (Or.inl hs.ne'))
      hp.ne'
    rw [Real.rpow_sub hs, Real.rpow_one] at h
    convert h using 1
    field_simp [hs.ne', hp.ne']; ring
  apply strictAntiOn_of_deriv_neg (convex_Ioo _ _)
  · exact fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  · intro x hx
    have hmem : x ∈ Set.Ioo 0 Real.pi := interior_subset hx
    have hs := Real.sin_pos_of_pos_of_lt_pi hmem.1 hmem.2
    rw [(hderiv x hmem).deriv]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (add_pos_of_pos_of_nonneg (sq_pos_of_pos hs)
      (mul_nonneg (by linarith) (sq_nonneg _)))) (mul_pos hs (Real.rpow_pos_of_pos hs _))

noncomputable def halfArc {n : ℕ} (a : Fin n → ℝ) (i j : Fin n) : ℝ :=
  (a j - a i + if j < i then 2 * Real.pi else 0) / 2

theorem halfArc_mem {n : ℕ} {a : Fin n → ℝ}
    (ha : StrictMono a) (ha0 : ∀ i, 0 ≤ a i) (ha2π : ∀ i, a i < 2 * Real.pi)
    {i j : Fin n} (hji : j ≠ i) : halfArc a i j ∈ Set.Ioo 0 Real.pi := by
  have hi0 := ha0 i
  have hj0 := ha0 j
  have hiπ := ha2π i
  have hjπ := ha2π j
  unfold halfArc
  rw [Set.mem_Ioo]
  split_ifs with h
  · have := ha h
    constructor <;> linarith
  · have := ha (lt_of_le_of_ne (le_of_not_gt h) hji.symm)
    constructor <;> linarith

theorem halfArc_phase {n : ℕ} (a : Fin n → ℝ) (i j : Fin n) :
    unitRay (2 * halfArc a i j) = unitRay (a j - a i) := by
  have h : 2 * halfArc a i j = a j - a i + if j < i then 2 * Real.pi else 0 := by
    unfold halfArc
    ring
  rw [h]
  split_ifs
  · exact unitRay_periodic _
  · rw [add_zero]

namespace Configuration

variable {n : ℕ} {α : ℝ} (F : Configuration n α)

theorem chord_eq_halfArc (a : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (hphase : ∀ i, F.position (σ i) = F.center + (F.radius : ℂ) * unitRay (a i))
    {i j : Fin n} (ht : halfArc a i j ∈ Set.Ioo 0 Real.pi) :
    ‖F.position (σ j) - F.position (σ i)‖ = (2 * F.radius) * Real.sin (halfArc a i j) := by
  have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
  have hnorm : ‖(F.radius : ℂ)‖ = F.radius := by
    rw [Complex.norm_real, Real.norm_of_nonneg F.radius_pos.le]
  rw [hphase j, hphase i]
  have h := rotated_pair_norm F.center (F.radius : ℂ) true (a i) (a j)
  simp only [orientedPhase, if_true, hnorm] at h
  rw [h, ← halfArc_phase, unitRay_chord, show 2 * halfArc a i j / 2 = halfArc a i j by ring,
    abs_of_pos hs]
  ring

private theorem angular_pair (a : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (hphase : ∀ i, F.position (σ i) = F.center + (F.radius : ℂ) * unitRay (a i))
    {i j : Fin n} (ht : halfArc a i j ∈ Set.Ioo 0 Real.pi) :
    (F.mass (σ j) / ‖F.position (σ j) - F.position (σ i)‖ ^ (α + 2)) *
      ((F.position (σ j) - F.position (σ i)) * star (F.position (σ i) - F.center)).im =
      (2 * F.radius ^ 2 / (2 * F.radius) ^ (α + 2)) *
        (F.mass (σ j) * angularKernel α (halfArc a i j)) := by
  let t := halfArc a i j
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
  have hR := F.radius_pos
  have hnorm : ‖(F.radius : ℂ)‖ = F.radius := by
    rw [Complex.norm_real, Real.norm_of_nonneg hR.le]
  have hangle : Real.sin (a j - a i) = Real.sin (2 * t) := by
    simpa only [unitRay_im] using (congrArg Complex.im (halfArc_phase a i j)).symm
  have hd : ‖F.position (σ j) - F.position (σ i)‖ = (2 * F.radius) * Real.sin t :=
    F.chord_eq_halfArc a σ hphase ht
  have him :
      ((F.position (σ j) - F.position (σ i)) * star (F.position (σ i) - F.center)).im =
        F.radius ^ 2 * Real.sin (2 * t) := by
    rw [hphase j, hphase i]
    have h := rotated_pair_torque F.center (F.radius : ℂ) true (a i) (a j)
    simpa only [orientedPhase, if_true, orientationSign, hnorm, mul_one, hangle] using h
  change _ = (2 * F.radius ^ 2 / (2 * F.radius) ^ (α + 2)) *
    (F.mass (σ j) * angularKernel α t)
  rw [hd, him, Real.mul_rpow (by positivity) hs.le, Real.sin_two_mul, angularKernel]
  rw [show (Real.sin t) ^ (α + 2) = Real.sin t ^ (α + 1) * Real.sin t by
    rw [show α + 2 = (α + 1) + 1 by ring, Real.rpow_add hs, Real.rpow_one]]
  field_simp [hs.ne', (Real.rpow_pos_of_pos hs (α + 1)).ne',
    (Real.rpow_pos_of_pos (show 0 < 2 * F.radius by positivity) (α + 2)).ne']

theorem weighted_angular_row (a : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (ha : StrictMono a) (ha0 : ∀ i, 0 ≤ a i) (ha2π : ∀ i, a i < 2 * Real.pi)
    (hphase : ∀ i, F.position (σ i) = F.center + (F.radius : ℂ) * unitRay (a i)) (i : Fin n) :
    (∑ j ∈ Finset.univ.erase i, F.mass (σ j) * angularKernel α (halfArc a i j)) = 0 := by
  let f : Fin n → ℝ := fun j =>
    (F.mass j / ‖F.position j - F.position (σ i)‖ ^ (α + 2)) *
      ((F.position j - F.position (σ i)) * star (F.position (σ i) - F.center)).im
  have hz : f (σ i) = 0 := by simp [f]
  have h : (∑ j ∈ Finset.univ.erase i, f (σ j)) = 0 := by
    calc
      _ = ∑ j, f (σ j) := by rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), hz, sub_zero]
      _ = ∑ j, f j := Equiv.sum_comp σ f
      _ = ∑ j ∈ Finset.univ.erase (σ i), f j := by
        rw [Finset.sum_erase_eq_sub (Finset.mem_univ (σ i)), hz, sub_zero]
      _ = 0 := F.tangential_row (σ i)
  have hterm (j : Fin n) (hj : j ∈ Finset.univ.erase i) :
      f (σ j) = (2 * F.radius ^ 2 / (2 * F.radius) ^ (α + 2)) *
        (F.mass (σ j) * angularKernel α (halfArc a i j)) :=
    F.angular_pair a σ hphase (halfArc_mem ha ha0 ha2π (Finset.mem_erase.mp hj).1)
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum] at h
  have hR := F.radius_pos
  exact (mul_eq_zero.mp h).resolve_left (ne_of_gt (by positivity))

private theorem angular_row (a : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (ha : StrictMono a) (ha0 : ∀ i, 0 ≤ a i) (ha2π : ∀ i, a i < 2 * Real.pi)
    (hphase : ∀ i, F.position (σ i) = F.center + (F.radius : ℂ) * unitRay (a i))
    {m : ℝ} (hm : 0 < m) (hmass : ∀ i, F.mass i = m) (i : Fin n) :
    (∑ j ∈ Finset.univ.erase i, angularKernel α (halfArc a i j)) = 0 := by
  have h := F.weighted_angular_row a σ ha ha0 ha2π hphase i
  simp only [hmass, ← Finset.mul_sum] at h
  exact (mul_eq_zero.mp h).resolve_left hm.ne'

noncomputable def phase (i : Fin n) : ℝ :=
  positiveAngle (F.radius⁻¹ • (F.position i - F.center))

theorem phase_eq (i : Fin n) :
    F.position i = F.center + (F.radius : ℂ) * unitRay (F.phase i) := by
  have hu : ‖F.radius⁻¹ • (F.position i - F.center)‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr F.radius_pos.le), F.on_circle]
    exact inv_mul_cancel₀ F.radius_pos.ne'
  rw [phase, positiveAngle_ray hu, ← Complex.real_smul, smul_smul,
    mul_inv_cancel₀ F.radius_pos.ne', one_smul]
  abel

theorem phase_injective : Function.Injective F.phase := by
  intro i j hij
  apply F.distinct
  rw [F.phase_eq i, F.phase_eq j, hij]

/-- Equal positive masses and the original individual torques force one common
angular displacement from a regular polygon. -/
theorem equal_mass_regular (hn : 2 ≤ n) (hα : 0 ≤ α)
    {m : ℝ} (hm : 0 < m) (hmass : ∀ i, F.mass i = m) : IsEqualMassRegular F := by
  let σ := Tuple.sort F.phase
  let a : Fin n → ℝ := F.phase ∘ σ
  have ha : StrictMono a := by
    exact (Tuple.monotone_sort F.phase).strictMono_of_injective
      (F.phase_injective.comp σ.injective)
  have ha0 (i : Fin n) : 0 ≤ a i := (positiveAngle_range _).1
  have ha2π (i : Fin n) : a i < 2 * Real.pi := (positiveAngle_range _).2
  have haRow := F.angular_row a σ ha ha0 ha2π (fun i => F.phase_eq (σ i)) hm hmass
  let b : Fin n → ℝ := fun i => 2 * Real.pi * (i : ℝ) / (n : ℝ)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hb : StrictMono b := by
    intro i j hij
    have hcast : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
    exact (div_lt_div_iff_of_pos_right hnR).mpr
      (mul_lt_mul_of_pos_left hcast (by positivity))
  have hb0 (i : Fin n) : 0 ≤ b i := by dsimp [b]; positivity
  have hb2π (i : Fin n) : b i < 2 * Real.pi := by
    apply (div_lt_iff₀ hnR).mpr
    exact mul_lt_mul_of_pos_left (by exact_mod_cast i.isLt) (by positivity)
  letI : NeZero n := ⟨by omega⟩
  let G := regularConfiguration hn α 0 m 1 0 hm one_pos
  have hbRow := G.angular_row b (Equiv.refl _) hb hb0 hb2π
    (fun i => by
      change regularPosition n 0 1 0 i = 0 + (1 : ℂ) * unitRay (b i)
      simp only [regularPosition_phase, zero_add, Complex.ofReal_one, b]) hm (fun _ => rfl)
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun j : Fin n => a j - b j)
    (show (Finset.univ : Finset (Fin n)).Nonempty from ⟨⟨0, by omega⟩, Finset.mem_univ _⟩)
  have harc (j : Fin n) : halfArc a i j ≤ halfArc b i j := by
    have h := hi j (Finset.mem_univ j)
    unfold halfArc
    linarith
  have heq (j : Fin n) : a j - b j = a i - b i := by
    by_cases hji : j = i
    · rw [hji]
    by_contra! hne
    have hlt : halfArc a i j < halfArc b i j := by
      have h := lt_of_le_of_ne (hi j (Finset.mem_univ j)) hne
      unfold halfArc
      linarith
    have hsum : (∑ k ∈ Finset.univ.erase i, angularKernel α (halfArc b i k)) <
        ∑ k ∈ Finset.univ.erase i, angularKernel α (halfArc a i k) := by
      apply Finset.sum_lt_sum
      · intro k hk
        have hk' := (Finset.mem_erase.mp hk).1
        exact (angularKernel_strictAnti α hα).antitoneOn
          (halfArc_mem ha ha0 ha2π hk') (halfArc_mem hb hb0 hb2π hk') (harc k)
      · exact ⟨j, Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩,
          angularKernel_strictAnti α hα (halfArc_mem ha ha0 ha2π hji)
            (halfArc_mem hb hb0 hb2π hji) hlt⟩
    rw [haRow i, hbRow i] at hsum
    exact (lt_irrefl 0) hsum
  refine ⟨⟨m, hm, hmass⟩, a i - b i, σ, ?_⟩
  intro j
  rw [F.phase_eq (σ j)]
  have hj : F.phase (σ j) = (a i - b i) + 2 * Real.pi * (j : ℝ) / (n : ℝ) := by
    change a j = a i - b i + b j
    linarith [heq j]
  rw [hj]

end Configuration

/-- The zero exponent uses the logarithmic force law. -/
theorem logarithmic {n : ℕ} (hn : 2 ≤ n) (F : Configuration n 0) :
    IsEqualMassRegular F := by
  have radial (i : Fin n) :
      ∑ j ∈ Finset.univ.erase i, F.mass j = 2 * F.coefficient * F.radius ^ 2 := by
    simpa only [Real.rpow_zero, div_one] using F.radial_row i
  have total (i : Fin n) :
      (∑ j, F.mass j) = 2 * F.coefficient * F.radius ^ 2 + F.mass i := by
    rw [← radial i]
    exact (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
  let i : Fin n := ⟨0, by omega⟩
  apply F.equal_mass_regular hn le_rfl (F.mass_pos i)
  intro j
  linarith [total i, total j]

end ACS12

import ACS12.Anchored

namespace ACS12

open scoped BigOperators
open Set
set_option backward.isDefEq.respectTransparency false

noncomputable def angularCost (α t : ℝ) : ℝ := 1 / Real.sin t ^ α

theorem hasDerivAt_angularCost (α : ℝ) {t : ℝ} (ht : t ∈ Ioo 0 Real.pi) :
    HasDerivAt (angularCost α) (-α * angularKernel α t) t := by
  have hfun : circlePower α Real.pi = angularCost α := by
    funext x
    rw [circlePower, angularCost, div_self Real.pi_pos.ne', Real.one_rpow,
      mul_div_cancel_left₀ _ Real.pi_pos.ne']
  have h := hasDerivAt_circlePower α Real.pi_pos ht.1 ht.2
  simpa only [hfun, circleTorque, div_self Real.pi_pos.ne', Real.one_rpow, mul_one,
    mul_div_cancel_left₀ _ Real.pi_pos.ne'] using h

theorem angularCost_tangent_strict {α x y : ℝ} (hα : 0 < α)
    (hx : x ∈ Ioo 0 Real.pi) (hy : y ∈ Ioo 0 Real.pi) (hxy : x ≠ y) :
    -α * angularKernel α x * (y - x) < angularCost α y - angularCost α x := by
  have hmv {a b : ℝ} (ha : a ∈ Ioo 0 Real.pi) (hb : b ∈ Ioo 0 Real.pi) (hab : a < b) :
      ∃ c ∈ Ioo a b, -α * angularKernel α c = (angularCost α b - angularCost α a) / (b - a) := by
    have hcc : Icc a b ⊆ Ioo 0 Real.pi := fun _ hz => ⟨ha.1.trans_le hz.1, hz.2.trans_lt hb.2⟩
    obtain ⟨c, hc, h⟩ := exists_deriv_eq_slope (angularCost α) hab
      (fun z hz => (hasDerivAt_angularCost α (hcc hz)).continuousAt.continuousWithinAt)
      (fun z hz => (hasDerivAt_angularCost α (hcc (Ioo_subset_Icc_self hz))).differentiableAt.differentiableWithinAt)
    exact ⟨c, hc, (hasDerivAt_angularCost α (hcc (Ioo_subset_Icc_self hc))).deriv.symm.trans h⟩
  have hmono : StrictMonoOn (fun t => -α * angularKernel α t) (Ioo 0 Real.pi) := by
    intro a ha b hb hab
    exact mul_lt_mul_of_neg_left (angularKernel_strictAnti α hα.le ha hb hab) (neg_lt_zero.mpr hα)
  rcases lt_or_gt_of_ne hxy with h | h
  · obtain ⟨c, hc, hder⟩ := hmv hx hy h
    have hc' : c ∈ Ioo 0 Real.pi := ⟨hx.1.trans hc.1, hc.2.trans hy.2⟩
    exact (lt_div_iff₀ (sub_pos.mpr h)).mp ((hmono hx hc' hc.1).trans_eq hder)
  · obtain ⟨c, hc, hder⟩ := hmv hy hx h
    have hc' : c ∈ Ioo 0 Real.pi := ⟨hy.1.trans hc.1, hc.2.trans hx.2⟩
    have hlt := (div_lt_iff₀ (sub_pos.mpr h)).mp (hder.symm.trans_lt (hmono hc' hx hc.2))
    linarith

theorem halfArc_self {n : ℕ} (a : Fin n → ℝ) (i : Fin n) : halfArc a i i = 0 := by
  simp [halfArc]

theorem halfArc_reverse {n : ℕ} (a : Fin n → ℝ) {i j : Fin n} (hij : i ≠ j) :
    halfArc a j i = Real.pi - halfArc a i j := by
  rcases lt_or_gt_of_ne hij with h | h
  · simp only [halfArc, if_pos h, if_neg (not_lt_of_gt h)]
    ring
  · simp only [halfArc, if_pos h, if_neg (not_lt_of_gt h)]
    ring

private theorem kernel_reverse {n : ℕ} {α : ℝ} (hα : 0 < α) (a : Fin n → ℝ) (i j : Fin n) :
    angularKernel α (halfArc a j i) = -angularKernel α (halfArc a i j) := by
  by_cases h : i = j
  · subst j
    rw [halfArc_self, angularKernel, Real.sin_zero, Real.zero_rpow (by linarith : α + 1 ≠ 0),
      div_zero, neg_zero]
  · rw [halfArc_reverse a h, angularKernel, Real.sin_pi_sub, Real.cos_pi_sub, neg_div]
    rfl

noncomputable def angularEnergy {n : ℕ} (α : ℝ) (m a : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, m i * m j * angularCost α (halfArc a i j)

theorem cyclicWork_zero {n : ℕ} (m d : Fin n → ℝ) (K : Fin n → Fin n → ℝ)
    (hK : ∀ i j, K j i = -K i j)
    (hrow : ∀ i, (∑ j, m j * K i j) = 0) :
    (∑ i, ∑ j, m i * m j * K i j * (d j - d i)) = 0 := by
  let w (i j : Fin n) := m i * m j * K i j
  have hw (i j : Fin n) : w j i = -w i j := by
    dsimp only [w]
    rw [hK i j]
    ring
  have hleft : (∑ i, ∑ j, w i j * d i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    calc
      _ = m i * d i * ∑ j, m j * K i j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [w]
        ring
      _ = 0 := by rw [hrow, mul_zero]
  have hright : (∑ i, ∑ j, w i j * d j) = 0 := by
    have hs (i : Fin n) : (∑ j, w j i * d i) = -(∑ j, w i j * d i) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun j _ => by rw [hw i j, neg_mul])
    rw [Finset.sum_comm, Finset.sum_congr rfl (fun i _ => hs i), Finset.sum_neg_distrib, hleft, neg_zero]
  change (∑ i, ∑ j, w i j * (d j - d i)) = 0
  simp only [mul_sub, Finset.sum_sub_distrib, hleft, hright, sub_self]

theorem torque_work_zero {n : ℕ} {α : ℝ} (hα : 0 < α) (m a d : Fin n → ℝ)
    (hrow : ∀ i, (∑ j, m j * angularKernel α (halfArc a i j)) = 0) :
    (∑ i, ∑ j, m i * m j * angularKernel α (halfArc a i j) * (d j - d i)) = 0 :=
  cyclicWork_zero m d (fun i j => angularKernel α (halfArc a i j)) (kernel_reverse hα a) hrow

noncomputable def cyclicCostEnergy {n : ℕ} (K : ℝ → ℝ) (m a : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, m i * m j * K (halfArc a i j)

/-- A stationary cyclic word minimizes every strictly supported pair cost. -/
theorem cyclicCost_minimum {n : ℕ} (K D : ℝ → ℝ) (m a b : Fin n → ℝ)
    (hm : ∀ i, 0 < m i)
    (ha : ∀ i j, j ≠ i → halfArc a i j ∈ Ioo 0 Real.pi)
    (hb : ∀ i j, j ≠ i → halfArc b i j ∈ Ioo 0 Real.pi)
    (hD : ∀ i j, D (halfArc a j i) = -D (halfArc a i j))
    (hrow : ∀ i, (∑ j, m j * D (halfArc a i j)) = 0)
    (hTangent : ∀ {x y}, x ∈ Ioo 0 Real.pi → y ∈ Ioo 0 Real.pi → x ≠ y →
      D x * (y - x) < K y - K x) :
    cyclicCostEnergy K m a ≤ cyclicCostEnergy K m b ∧
      (cyclicCostEnergy K m a = cyclicCostEnergy K m b → ∀ i j, halfArc a i j = halfArc b i j) := by
  let d : Fin n → ℝ := fun i => b i - a i
  let w (i j : Fin n) : ℝ := m i * m j * D (halfArc a i j) * (d j - d i)
  have hw : (∑ i, ∑ j, w i j) = 0 := cyclicWork_zero m d (fun i j => D (halfArc a i j)) hD hrow
  let r (i j : Fin n) : ℝ := m i * m j *
    (K (halfArc b i j) - K (halfArc a i j)) - (1 / 2) * w i j
  have hdiff (i j : Fin n) :
      halfArc b i j - halfArc a i j = (d j - d i) / 2 := by
    dsimp only [halfArc, d]
    ring
  have hr_strict (i j : Fin n) (hneq : halfArc a i j ≠ halfArc b i j) : 0 < r i j := by
    have hij : j ≠ i := by
      intro h
      subst j
      exact hneq (by rw [halfArc_self, halfArc_self])
    have h := hTangent (ha i j hij) (hb i j hij) hneq
    rw [hdiff] at h
    have h' := mul_lt_mul_of_pos_left h (mul_pos (hm i) (hm j))
    dsimp only [r, w]
    linarith only [h']
  have hr (i j : Fin n) : 0 ≤ r i j := by
    by_cases he : halfArc a i j = halfArc b i j
    · have hd : d j - d i = 0 := by linarith only [hdiff i j, he]
      simp only [r, w, he, sub_self, hd, mul_zero, le_refl]
    · exact (hr_strict i j he).le
  have hsum : (∑ i, ∑ j, r i j) = cyclicCostEnergy K m b - cyclicCostEnergy K m a := by
    simp only [r, mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum,
      hw, mul_zero, sub_zero, cyclicCostEnergy]
  refine ⟨sub_nonneg.mp (hsum ▸ Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hr i j),
    ?_⟩
  intro he i j
  by_contra hneq
  have hpos : 0 < (∑ i', ∑ j', r i' j') :=
    Finset.sum_pos' (fun i' _ => Finset.sum_nonneg fun j' _ => hr i' j') ⟨i, Finset.mem_univ _,
      Finset.sum_pos' (fun j' _ => hr i j') ⟨j, Finset.mem_univ _, hr_strict i j hneq⟩⟩
  rw [hsum, he, sub_self] at hpos
  exact (lt_irrefl 0) hpos


/-- The complete angular energy is minimized at a stationary cyclic word.
If one ordered arc changes, the inequality is strict. -/
theorem angularEnergy_minimum {n : ℕ} {α : ℝ} (hα : 0 < α) (m a b : Fin n → ℝ)
    (hm : ∀ i, 0 < m i)
    (ha : ∀ i j, j ≠ i → halfArc a i j ∈ Ioo 0 Real.pi)
    (hb : ∀ i j, j ≠ i → halfArc b i j ∈ Ioo 0 Real.pi)
    (hrow : ∀ i, (∑ j ∈ Finset.univ.erase i, m j * angularKernel α (halfArc a i j)) = 0) :
    angularEnergy α m a ≤ angularEnergy α m b ∧
      (angularEnergy α m a = angularEnergy α m b → ∀ i j, halfArc a i j = halfArc b i j) := by
  have hfull (i : Fin n) : (∑ j, m j * angularKernel α (halfArc a i j)) = 0 := by
    have h := hrow i
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)] at h
    simpa only [halfArc_self, angularKernel, Real.sin_zero, div_zero, mul_zero, sub_zero,
      Real.zero_rpow (by linarith : α + 1 ≠ 0)] using h

  apply cyclicCost_minimum (angularCost α) (fun t => -α * angularKernel α t) m a b hm ha hb
  · intro i j
    rw [kernel_reverse hα a i j]
    ring
  · intro i
    calc
      _ = -α * ∑ j, m j * angularKernel α (halfArc a i j) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = 0 := by rw [hfull,mul_zero]
  · exact angularCost_tangent_strict hα

end ACS12

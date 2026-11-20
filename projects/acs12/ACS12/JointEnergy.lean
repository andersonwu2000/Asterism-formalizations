import ACS12.PhysicalAngularRows

/-! The exact-source joint log-mass and angular trial energy comparison. -/

namespace ACS12

open scoped BigOperators
open Set
open CenteredCircle.AllN (unitRay)
set_option backward.isDefEq.respectTransparency false

private noncomputable def angularLogCost (α t : ℝ) : ℝ :=
  -α * Real.log (Real.sin t)

private theorem exp_logCost {α t : ℝ} (ht : t ∈ Ioo 0 Real.pi) :
    Real.exp (angularLogCost α t) = angularCost α t := by
  have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
  rw [angularLogCost, angularCost, neg_mul, Real.exp_neg, one_div,
    Real.rpow_def_of_pos hs, mul_comm]

private theorem logCost_deriv (α : ℝ) {t : ℝ} (ht : t ∈ Ioo 0 Real.pi) :
    HasDerivAt (angularLogCost α) (-α * angularKernel 0 t) t := by
  have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
  have h := ((Real.hasDerivAt_sin t).log hs.ne').const_mul (-α)
  simpa only [angularLogCost, angularKernel, zero_add, Real.rpow_one] using h

private theorem logCost_tangent {α x y : ℝ} (hα : 0 < α)
    (hx : x ∈ Ioo 0 Real.pi) (hy : y ∈ Ioo 0 Real.pi) :
    -α * angularKernel 0 x * (y - x) ≤ angularLogCost α y - angularLogCost α x := by
  have hmv {a b : ℝ} (ha : a ∈ Ioo 0 Real.pi) (hb : b ∈ Ioo 0 Real.pi) (hab : a < b) :
      ∃ c ∈ Ioo a b, -α * angularKernel 0 c = (angularLogCost α b - angularLogCost α a) / (b - a) := by
    have hcc : Icc a b ⊆ Ioo 0 Real.pi := fun _ hz => ⟨ha.1.trans_le hz.1, hz.2.trans_lt hb.2⟩
    obtain ⟨c, hc, h⟩ := exists_deriv_eq_slope (angularLogCost α) hab
      (fun z hz => (logCost_deriv α (hcc hz)).continuousAt.continuousWithinAt)
      (fun z hz => (logCost_deriv α (hcc (Ioo_subset_Icc_self hz))).differentiableAt.differentiableWithinAt)
    exact ⟨c, hc, (logCost_deriv α (hcc (Ioo_subset_Icc_self hc))).deriv.symm.trans h⟩
  have hmono : StrictMonoOn (fun t => -α * angularKernel 0 t) (Ioo 0 Real.pi) := by
    intro a ha b hb hab
    exact mul_lt_mul_of_neg_left (angularKernel_strictAnti 0 le_rfl ha hb hab) (neg_lt_zero.mpr hα)
  rcases lt_trichotomy x y with h | rfl | h
  · obtain ⟨c, hc, hder⟩ := hmv hx hy h
    have hc' : c ∈ Ioo 0 Real.pi := ⟨hx.1.trans hc.1, hc.2.trans hy.2⟩
    exact ((lt_div_iff₀ (sub_pos.mpr h)).mp ((hmono hx hc' hc.1).trans_eq hder)).le
  · simp
  · obtain ⟨c, hc, hder⟩ := hmv hy hx h
    have hc' : c ∈ Ioo 0 Real.pi := ⟨hy.1.trans hc.1, hc.2.trans hx.2⟩
    have hlt := (div_lt_iff₀ (sub_pos.mpr h)).mp (hder.symm.trans_lt (hmono hc' hx hc.2))
    linarith

private theorem angularCost_symm {n : ℕ} (α : ℝ) (a : Fin n → ℝ) (i j : Fin n) :
    angularCost α (halfArc a j i) = angularCost α (halfArc a i j) := by
  by_cases h : i = j
  · subst j; rfl
  · rw [halfArc_reverse a h, angularCost, Real.sin_pi_sub, angularCost]

private theorem cost_mul_cot {α t : ℝ} (ht : t ∈ Ioo 0 Real.pi) :
    angularCost α t * angularKernel 0 t = angularKernel α t := by
  have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
  rw [angularCost, angularKernel, angularKernel, zero_add, Real.rpow_one,
    Real.rpow_add hs, Real.rpow_one]
  ring

/-- The exact joint trial inequality. The row and torque hypotheses refer
to the same source and the log-mass displacement has zero original mass mean. -/
theorem angularEnergy_joint_min {n : ℕ} {α C : ℝ} (hα : 0 < α) (m v a b : Fin n → ℝ)
    (hm : ∀ i, 0 < m i) (hv : ∀ i, 0 < v i)
    (ha : ∀ i j, j ≠ i → halfArc a i j ∈ Ioo 0 Real.pi)
    (hb : ∀ i j, j ≠ i → halfArc b i j ∈ Ioo 0 Real.pi)
    (hRad : ∀ i, (∑ j, m j * angularCost α (halfArc a i j)) = C)
    (hTorque : ∀ i, (∑ j ∈ Finset.univ.erase i, m j * angularKernel α (halfArc a i j)) = 0)
    (hBalanced : (∑ i, m i * Real.log (v i / m i)) = 0) :
    angularEnergy α m a ≤ angularEnergy α v b := by
  let ell (i : Fin n) := Real.log (v i / m i)
  let d (i : Fin n) := b i - a i
  let e (i j : Fin n) := m i * m j * angularCost α (halfArc a i j)
  let T (i j : Fin n) := m i * m j * angularKernel α (halfArc a i j) * (d j - d i)
  have hFull (i : Fin n) : (∑ j, m j * angularKernel α (halfArc a i j)) = 0 := by
    have h := hTorque i
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)] at h
    simpa only [halfArc_self, angularKernel, Real.sin_zero, Real.zero_rpow (by linarith : α + 1 ≠ 0),
      div_zero, mul_zero, sub_zero] using h
  have hT : (∑ i, ∑ j, T i j) = 0 := torque_work_zero hα m a d hFull
  have hMleft : (∑ i, ∑ j, e i j * ell i) = 0 := by
    have hterm (i : Fin n) : (∑ j, e i j * ell i) = C * (m i * ell i) := by
      have hh : (∑ j, e i j * ell i) = (m i * ell i) * ∑ j, m j * angularCost α (halfArc a i j) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by dsimp only [e]; ring)
      rw [hh, hRad, mul_comm]
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum, show (∑ i, m i * ell i) = 0 from hBalanced,
      mul_zero]
  have hMright : (∑ i, ∑ j, e i j * ell j) = 0 := by
    rw [Finset.sum_comm]
    have hh (i j : Fin n) : e j i = e i j := by
      dsimp only [e]
      rw [angularCost_symm α a i j, mul_comm (m j)]
    exact (Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
      congrArg (· * ell i) (hh i j)))).trans hMleft
  have hpair (i j : Fin n) :
      e i j + e i j * ell i + e i j * ell j - α / 2 * T i j ≤
        v i * v j * angularCost α (halfArc b i j) := by
    by_cases hji : j = i
    · subst j
      simp only [e, T, halfArc_self, angularCost, Real.sin_zero, Real.zero_rpow hα.ne',
        div_zero, mul_zero, zero_mul, add_zero, sub_self, le_refl]
    have ht := ha i j hji
    have ht' := hb i j hji
    let x := halfArc a i j
    let y := halfArc b i j
    let L := ell i + ell j + (angularLogCost α y - angularLogCost α x)
    have hd : y - x = (d j - d i) / 2 := by
      dsimp only [x, y, d, halfArc]
      ring
    have hlin : 1 + ell i + ell j - α * angularKernel 0 x * (y - x) ≤ Real.exp L := by
      have h := logCost_tangent hα ht ht'
      dsimp only [L]
      linarith only [h, Real.add_one_le_exp (ell i + ell j + (angularLogCost α y - angularLogCost α x))]
    have hbase : 0 < e i j := mul_pos (mul_pos (hm i) (hm j))
      (one_div_pos.mpr (Real.rpow_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2) α))
    have hEq : e i j * Real.exp L = v i * v j * angularCost α y := by
      dsimp only [e, L, ell]
      rw [Real.exp_add, Real.exp_add, Real.exp_sub, exp_logCost ht, exp_logCost ht',
        Real.exp_log (div_pos (hv i) (hm i)), Real.exp_log (div_pos (hv j) (hm j))]
      have hC : angularCost α x ≠ 0 :=
        (one_div_pos.mpr (Real.rpow_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2) α)).ne'
      change m i * m j * angularCost α x * ((v i / m i * (v j / m j)) *
        (angularCost α y / angularCost α x)) = _
      field_simp [(hm i).ne', (hm j).ne', hC]
    have h := mul_le_mul_of_nonneg_left hlin hbase.le
    rw [hEq, hd] at h
    have hcost : angularCost α x * angularKernel 0 x = angularKernel α x := cost_mul_cot ht
    calc
      _ = e i j * (1 + ell i + ell j - α * angularKernel 0 x * ((d j - d i) / 2)) := by
        change m i * m j * angularCost α x + m i * m j * angularCost α x * ell i +
          m i * m j * angularCost α x * ell j -
          α / 2 * (m i * m j * angularKernel α x * (d j - d i)) = _
        rw [← hcost]
        dsimp only [e, x]
        ring
      _ ≤ _ := h
  have hh := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) fun j _ => hpair i j
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hMleft, hMright,
    hT, mul_zero, add_zero, sub_zero] at hh
  exact hh

namespace Configuration

variable {n : ℕ} {α : ℝ} (F : Configuration n α)

/-- The physical source is minimal among ordered joint trials whose log-mass
increment has zero mean under the original mass weights. -/
theorem joint_trial_energy_le (hα : 0 < α) (a b v : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (ha : StrictMono a) (ha0 : ∀ i, 0 ≤ a i) (ha2π : ∀ i, a i < 2 * Real.pi)
    (hphase : ∀ i, F.position (σ i) = F.center + (F.radius : ℂ) * unitRay (a i))
    (hb : StrictMono b) (hb0 : ∀ i, 0 ≤ b i) (hb2π : ∀ i, b i < 2 * Real.pi)
    (hv : ∀ i, 0 < v i) (hBalanced : (∑ i, F.mass (σ i) * Real.log (v i / F.mass (σ i))) = 0) :
    angularEnergy α (F.mass ∘ σ) a ≤ angularEnergy α v b := by
  exact angularEnergy_joint_min hα (F.mass ∘ σ) v a b (fun i => F.mass_pos _) hv
    (fun _ _ h => halfArc_mem ha ha0 ha2π h) (fun _ _ h => halfArc_mem hb hb0 hb2π h)
    (F.weighted_radial_row hα a σ ha ha0 ha2π hphase)
    (F.weighted_angular_row a σ ha ha0 ha2π hphase) hBalanced

end Configuration

end ACS12

import ACS12.PhysicalAngularRows
import ACS12.MassExchange
import ACS12.AlternatingSquare

/-! The opposite-site exchange needed by the finite force theorem. -/
namespace ACS12.Configuration

open Set CenteredCircle.AllN

private theorem reflected_cost {n : ℕ} {p c : ℝ} {a b : Fin n → ℝ}
    {τ : Equiv.Perm (Fin n)} (ha : StrictMono a) (ha₀ : ∀ k, 0 ≤ a k) (haU : ∀ k, a k < 2 * Real.pi)
    (hb : StrictMono b) (hb₀ : ∀ k, 0 ≤ b k) (hbU : ∀ k, b k < 2 * Real.pi)
    (hR : ∀ k, unitRay (b k) = unitRay (c - a (τ k))) (k l : Fin n) :
    angularCost p (halfArc b k l) = angularCost p (halfArc a (τ k) (τ l)) := by
  by_cases h : l = k
  · simp only [h,halfArc_self]
  have h₁ := halfArc_mem ha ha₀ haU (τ.injective.ne h)
  have h₂ := halfArc_mem hb hb₀ hbU h
  have hPhase : unitRay (2 * halfArc b k l) = unitRay (-(2 * halfArc a (τ k) (τ l))) := by
    rw [halfArc_phase,unitRay_neg_congr (halfArc_phase a (τ k) (τ l)),
      sub_eq_add_neg (b l),unitRay_add,hR l,unitRay_neg_congr (hR k),← unitRay_add]
    congr 1
    ring
  have hNorm := congrArg (fun z : ℂ => ‖z - 1‖) hPhase
  dsimp only at hNorm
  rw [unitRay_neg_chord,unitRay_chord,unitRay_chord,
    mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0),mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0),
    abs_of_pos (Real.sin_pos_of_pos_of_lt_pi h₂.1 h₂.2),
    abs_of_pos (Real.sin_pos_of_pos_of_lt_pi h₁.1 h₁.2)] at hNorm
  unfold angularCost
  rw [(mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) hNorm)]

private theorem reflected_exchange {n : ℕ} {p c : ℝ} (F : Configuration n p)
    (hp : 0 < p) (σ : Equiv.Perm (Fin n)) {a b : Fin n → ℝ}
    (ha : StrictMono a) (ha₀ : ∀ k, 0 ≤ a k) (haU : ∀ k, a k < 2 * Real.pi)
    (hphase : ∀ k, F.position (σ k) = F.center + (F.radius : ℂ) * unitRay (a k))
    (hb : StrictMono b) (hb₀ : ∀ k, 0 ≤ b k) (hbU : ∀ k, b k < 2 * Real.pi)
    {i j : Fin n} (hij : i ≠ j)
    (hR : ∀ k, unitRay (b k) = unitRay (c - a (Equiv.swap i j k))) :
    F.mass (σ i) = F.mass (σ j) := by
  let m := F.mass ∘ σ
  let K (k l : Fin n) := angularCost p (halfArc a k l)
  let E := cyclicCostEnergy (angularCost p) m
  have hMin := (angularEnergy_minimum hp m a b (fun k => F.mass_pos (σ k))
    (fun k l h => halfArc_mem ha ha₀ haU h) (fun k l h => halfArc_mem hb hb₀ hbU h)
    (F.weighted_angular_row a σ ha ha₀ haU hphase)).1
  have hRrow := F.weighted_radial_row hp a σ ha ha₀ haU hphase
  have hE := mass_exchange_eq K m hij (angularCost_symmetric p a)
    (fun k => by dsimp only [K]; rw [halfArc_self,angularCost_self hp]) hRrow
  dsimp only at hE
  have hSwap := cyclicCost_swap_invariant (angularCost p) m a b i j
    (reflected_cost ha ha₀ haU hb hb₀ hbU hR)
  change E a ≤ E b at hMin
  have hEq : E b - E a = -2 * (m i - m j) ^ 2 * K i j := by
    dsimp only [E] at *
    rw [hSwap]
    exact hE
  have hK : 0 < K i j := by
    have h := halfArc_mem ha ha₀ haU hij.symm
    have hs := Real.sin_pos_of_pos_of_lt_pi h.1 h.2
    dsimp only [K,angularCost]
    positivity
  have hMass : m i = m j := by
    by_contra h
    have hNeg : -2 * (m i - m j) ^ 2 * K i j < 0 := by
      exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) (sq_pos_of_ne_zero (sub_ne_zero.mpr h))) hK
    linarith only [hMin,hEq,hNeg]
  exact hMass

private noncomputable def reflected02 (a : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![0, a 2 - a 1, a 2 - a 0, a 2 - a 3 + 2 * Real.pi]

private noncomputable def reflected13 (a : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![0, a 0 - a 3 + 2 * Real.pi, a 0 - a 2 + 2 * Real.pi, a 0 - a 1 + 2 * Real.pi]

private theorem reflected02_ray (a : Fin 4 → ℝ) (k : Fin 4) :
    unitRay (reflected02 a k) = unitRay (a 2 - a (Equiv.swap 0 2 k)) := by
  fin_cases k <;>
    norm_num [reflected02,Equiv.swap_apply_def,Fin.isValue,Fin.ext_iff,unitRay_periodic]; rfl

private theorem reflected13_ray (a : Fin 4 → ℝ) (k : Fin 4) :
    unitRay (reflected13 a k) = unitRay (a 0 - a (Equiv.swap 1 3 k)) := by
  fin_cases k <;>
    norm_num [reflected13,Equiv.swap_apply_def,Fin.isValue,Fin.ext_iff,unitRay_periodic]; rfl

private theorem reflected_sorted {a : Fin 4 → ℝ} (ha : StrictMono a)
    (ha₀ : 0 ≤ a 0) (ha₃ : a 3 < 2 * Real.pi) :
    (StrictMono (reflected02 a) ∧ (∀ k, 0 ≤ reflected02 a k) ∧ (∀ k, reflected02 a k < 2 * Real.pi)) ∧
      (StrictMono (reflected13 a) ∧ (∀ k, 0 ≤ reflected13 a k) ∧ (∀ k, reflected13 a k < 2 * Real.pi)) := by
  have h01 : a 0 < a 1 := ha (by decide)
  have h12 : a 1 < a 2 := ha (by decide)
  have h23 : a 2 < a 3 := ha (by decide)
  have hp := Real.pi_pos
  constructor <;> refine ⟨?_,?_,?_⟩
  · intro k l h
    fin_cases k <;> fin_cases l <;> (try contradiction) <;>
      norm_num [reflected02,Fin.isValue] at * <;> linarith only [h01,h12,h23,ha₀,ha₃,hp]
  · intro k
    fin_cases k <;> norm_num [reflected02,Fin.isValue] <;> linarith only [h01,h12,h23,ha₀,ha₃,hp]
  · intro k
    fin_cases k <;> norm_num [reflected02,Fin.isValue] <;> linarith only [h01,h12,h23,ha₀,ha₃,hp]
  · intro k l h
    fin_cases k <;> fin_cases l <;> (try contradiction) <;>
      norm_num [reflected13,Fin.isValue] at * <;> linarith only [h01,h12,h23,ha₀,ha₃,hp]
  · intro k
    fin_cases k <;> norm_num [reflected13,Fin.isValue] <;> linarith only [h01,h12,h23,ha₀,ha₃,hp]
  · intro k
    fin_cases k <;> norm_num [reflected13,Fin.isValue] <;> linarith only [h01,h12,h23,ha₀,ha₃,hp]


theorem four_sites_regular {p : ℝ} (F : Configuration 4 p) (hp : 0 < p) : IsEqualMassRegular F := by
  let σ := Tuple.sort F.phase
  let a := F.phase ∘ σ
  let m := F.mass ∘ σ
  have ha : StrictMono a := (Tuple.monotone_sort F.phase).strictMono_of_injective
    (F.phase_injective.comp σ.injective)
  have ha₀ (k : Fin 4) : 0 ≤ a k := (positiveAngle_range _).1
  have haU (k : Fin 4) : a k < 2 * Real.pi := (positiveAngle_range _).2
  have hphase (k : Fin 4) : F.position (σ k) = F.center + (F.radius : ℂ) * unitRay (a k) :=
    F.phase_eq (σ k)
  obtain ⟨⟨hb₀,hb₁,hb₂⟩,⟨hc₀,hc₁,hc₂⟩⟩ := reflected_sorted ha (ha₀ 0) (haU 3)
  have hM02 := F.reflected_exchange hp σ ha ha₀ haU hphase hb₀ hb₁ hb₂
    (by decide : (0 : Fin 4) ≠ 2) (reflected02_ray a)
  have hM13 := F.reflected_exchange hp σ ha ha₀ haU hphase hc₀ hc₁ hc₂
    (by decide : (1 : Fin 4) ≠ 3) (reflected13_ray a)
  change m 0 = m 2 at hM02
  change m 1 = m 3 at hM13
  have hSq := alternating_square_angles hp m a (fun k => F.mass_pos (σ k))
    ha ha₀ haU (F.weighted_angular_row a σ ha ha₀ haU hphase) hM02 hM13
  have hRow := F.weighted_radial_row hp a σ ha ha₀ haU hphase
  have hRow01 := (hRow 0).trans (hRow 1).symm
  change (∑ j, m j * angularCost p (halfArc a 0 j)) =
    ∑ j, m j * angularCost p (halfArc a 1 j) at hRow01
  rw [Fin.sum_univ_four,Fin.sum_univ_four] at hRow01
  have hCost : angularCost p (Real.pi / 2) = 1 := by simp [angularCost]
  have hRev : angularCost p (3 * Real.pi / 4) = angularCost p (Real.pi / 4) := by
    rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring,angularCost,Real.sin_pi_sub]
    rfl
  have hSelf : angularCost p 0 = 0 := by simp [angularCost,Real.zero_rpow hp.ne']
  have hArc (i j : Fin 4) : halfArc a i j =
      ((j.val : ℝ) * (Real.pi / 2) - (i.val : ℝ) * (Real.pi / 2) + if j < i then 2 * Real.pi else 0) / 2 := by
    unfold halfArc
    rw [hSq i,hSq j]
    ring
  have hA₀₁ : halfArc a 0 1 = Real.pi / 4 := by rw [hArc]; norm_num [Fin.lt_def]; ring
  have hA₀₂ : halfArc a 0 2 = Real.pi / 2 := by rw [hArc]; norm_num [Fin.lt_def]
  have hA₀₃ : halfArc a 0 3 = 3 * Real.pi / 4 := by rw [hArc]; norm_num [Fin.lt_def]; ring
  have hA₁₀ : halfArc a 1 0 = 3 * Real.pi / 4 := by rw [hArc]; norm_num [Fin.lt_def]; ring
  have hA₁₂ : halfArc a 1 2 = Real.pi / 4 := by rw [hArc]; norm_num [Fin.lt_def]; ring
  have hA₁₃ : halfArc a 1 3 = Real.pi / 2 := by rw [hArc]; norm_num [Fin.lt_def]; ring
  rw [halfArc_self,halfArc_self,hSelf,hA₀₁,hA₀₂,hA₀₃,hA₁₀,hA₁₂,hA₁₃,hCost,hRev,
    ← hM02,← hM13] at hRow01
  have hK : 1 < angularCost p (Real.pi / 4) := by
    have hSin₀ := Real.sin_pos_of_pos_of_lt_pi (show 0 < Real.pi / 4 by positivity)
      (show Real.pi / 4 < Real.pi by linarith only [Real.pi_pos])
    have hSin₁ : Real.sin (Real.pi / 4) < 1 := by
      rw [Real.sin_pi_div_four,div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
      simpa using (Real.sqrt_lt (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 2)).2 (by norm_num : (2 : ℝ) < 2 ^ 2)
    have hPow := Real.rpow_lt_rpow hSin₀.le hSin₁ hp
    rw [Real.one_rpow] at hPow
    unfold angularCost
    exact (lt_div_iff₀ (Real.rpow_pos_of_pos hSin₀ _)).mpr (by simpa only [one_mul] using hPow)
  have hM01 : m 0 = m 1 := by
    have hE : (m 0 - m 1) * (2 * angularCost p (Real.pi / 4) - 1) = 0 := by
      linarith only [hRow01]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hE).resolve_right (by linarith only [hK]))
  apply F.equal_mass_regular (by decide) hp.le (F.mass_pos (σ 0))
  intro k
  obtain ⟨j,rfl⟩ := σ.surjective k
  change m j = m 0
  fin_cases j
  · rfl
  · exact hM01.symm
  · exact hM02.symm
  · exact hM13.symm.trans hM01.symm

end ACS12.Configuration

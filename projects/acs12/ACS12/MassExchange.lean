import ACS12.AngularEnergy

/-! The exact quadratic mass exchange uses the original pair kernel and its unchanged common radial row. -/
namespace ACS12
open Set

theorem mass_exchange_eq {n : ℕ} (K : Fin n → Fin n → ℝ) (m : Fin n → ℝ) {C : ℝ}
    {i j : Fin n} (hij : i ≠ j)
    (hSym : ∀ k l, K k l = K l k) (hSelf : ∀ k, K k k = 0)
    (hRow : ∀ k, (∑ l, m l * K k l) = C) :
    let m' := m ∘ Equiv.swap i j
    (∑ k, ∑ l, m' k * m' l * K k l) - (∑ k, ∑ l, m k * m l * K k l) =
      -2 * (m i - m j) ^ 2 * K i j := by
  classical
  let m' := m ∘ Equiv.swap i j
  let d := m j - m i
  let δ (k : Fin n) := d * ((if k = i then 1 else 0) - (if k = j then 1 else 0))
  have hΔ (k : Fin n) : m' k = m k + δ k := by
    by_cases hi : k = i
    · subst k
      simp only [m',Function.comp_apply,Equiv.swap_apply_left,δ,if_true,if_neg hij,sub_zero,mul_one,d]
      ring
    by_cases hj : k = j
    · subst k
      simp only [m',Function.comp_apply,Equiv.swap_apply_right,δ,if_true,if_neg (Ne.symm hij),
        zero_sub,mul_neg,mul_one,d]
      ring
    · simp only [m',Function.comp_apply,Equiv.swap_apply_of_ne_of_ne hi hj,δ,if_neg hi,if_neg hj,sub_self,mul_zero,add_zero]
  have hD (f : Fin n → ℝ) : (∑ k, δ k * f k) = d * (f i - f j) := by
    simp only [δ,mul_assoc,sub_mul,← Finset.mul_sum,Finset.sum_sub_distrib,
      ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  have hL (k : Fin n) : (∑ l, δ k * m l * K k l) = δ k * C := by
    simp only [mul_assoc,← Finset.mul_sum,hRow]
  have hLsum : (∑ k, ∑ l, δ k * m l * K k l) = 0 := by
    simp only [hL]
    rw [hD (fun _ => C),sub_self,mul_zero]
  have hRsum : (∑ k, ∑ l, m k * δ l * K k l) = 0 := by
    rw [Finset.sum_comm]
    have hE : (∑ k, ∑ l, m l * δ k * K l k) = ∑ k, ∑ l, δ k * m l * K k l := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      rw [hSym l k,mul_comm (m l)]
    rwa [hE]
  have hQ (k : Fin n) : (∑ l, δ k * δ l * K k l) = δ k * (d * (K k i - K k j)) := by
    simp only [mul_assoc,← Finset.mul_sum,hD (K k)]
  have hQsum : (∑ k, ∑ l, δ k * δ l * K k l) = -2 * (m i - m j) ^ 2 * K i j := by
    simp only [hQ]
    rw [hD (fun k => d * (K k i - K k j)),hSelf i,hSelf j,hSym j i]
    dsimp only [d]
    ring
  have hPair (k l : Fin n) : m' k * m' l * K k l = m k * m l * K k l +
      δ k * m l * K k l + m k * δ l * K k l + δ k * δ l * K k l := by
    rw [hΔ k,hΔ l]
    ring
  change (∑ k, ∑ l, m' k * m' l * K k l) - _ = _
  simp only [hPair,Finset.sum_add_distrib,hLsum,hRsum,hQsum,add_zero]
  ring

theorem cyclicCost_swap_invariant {n : ℕ} (K : ℝ → ℝ) (m a b : Fin n → ℝ) (i j : Fin n)
    (hArc : ∀ k l, K (halfArc b k l) = K (halfArc a (Equiv.swap i j k) (Equiv.swap i j l))) :
    cyclicCostEnergy K m b = cyclicCostEnergy K (m ∘ Equiv.swap i j) a := by
  classical
  let τ := Equiv.swap i j
  let m' := m ∘ τ
  have hM (k : Fin n) : m' (τ k) = m k := by simp [m',τ]
  unfold cyclicCostEnergy
  have hInner (k : Fin n) : (∑ l, m k * m l * K (halfArc b k l)) =
      ∑ l, m' (τ k) * m' l * K (halfArc a (τ k) l) := by
    calc
      _ = ∑ l, m' (τ k) * m' (τ l) * K (halfArc a (τ k) (τ l)) := by
        apply Finset.sum_congr rfl
        intro l _
        rw [hArc,hM k,hM l]
      _ = _ := Equiv.sum_comp τ (fun l => m' (τ k) * m' l * K (halfArc a (τ k) l))
  simp only [hInner]
  exact Equiv.sum_comp τ (fun k => ∑ l, m' k * m' l * K (halfArc a k l))

theorem angularCost_self {p : ℝ} (hp : 0 < p) : angularCost p 0=0 := by
  simp [angularCost,Real.zero_rpow hp.ne']

theorem angularCost_symmetric {n : ℕ} (p : ℝ) (a : Fin n → ℝ) (i j : Fin n) :
    angularCost p (halfArc a i j)=angularCost p (halfArc a j i) := by
  by_cases h : i=j
  · subst j; rfl
  · rw [halfArc_reverse a h]
    simp only [angularCost,Real.sin_pi_sub]

end ACS12

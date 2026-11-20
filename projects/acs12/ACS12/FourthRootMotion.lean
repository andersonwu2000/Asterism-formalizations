import ACS12.FourthMotion

/-! Finite comparisons of the original fourth roots along the admissible paths. -/

namespace ACS12.GammaMeasure

open Set

theorem fourthSourceRoot_speed {p L θ u v₁ v₂ r₁ r₂ m e : ℝ}
    (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hv₁ : 0 < v₁) (hvv : v₁ < v₂) (hv₂ : v₂ ≤ u) (hu₁ : u < 1)
    (hMode : (e = 0 ∧ v₂ / 3 ≤ m ∧ m ≤ v₁) ∨ (e = 1 ∧ m = v₁))
    (hr₁ : r₁ ∈ Ioo 0 v₁) (hr₂ : r₂ ∈ Ioo 0 v₂)
    (hRoot₁ : fourthSourceRow p L θ u v₁ r₁ m = 0)
    (hRoot₂ : fourthSourceRow p L θ u v₂ r₂ (m + e * (v₂ - v₁)) = 0) :
    r₁ < r₂ ∧ r₂ - r₁ < 2 * (v₂ - v₁) := by
  let δ := v₂ - v₁
  let M := m + e * δ
  have hδ : 0 < δ := sub_pos.mpr hvv
  have hv₂₀ := hv₁.trans hvv
  have hu := hv₂₀.trans_le hv₂
  have hAt (t : ℝ) (ht : t ∈ Icc 0 δ) : 0 < v₁ + t ∧ v₁ + t ≤ u := by
    exact ⟨add_pos_of_pos_of_nonneg hv₁ ht.1, (show v₁ + t ≤ v₂ by linarith [ht.2]).trans hv₂⟩
  have hMass (t : ℝ) (ht : t ∈ Icc 0 δ) :
      (e = 0 ∧ (v₁ + t) / 3 ≤ m ∧ m ≤ v₁ + t) ∨ (e = 1 ∧ m = v₁) := by
    rcases hMode with ⟨he, hM₁, hM₂⟩ | h
    · exact Or.inl ⟨he, by linarith [ht.2], hM₂.trans (le_add_of_nonneg_right ht.1)⟩
    · exact Or.inr h
  have he₀ : 0 ≤ e := by rcases hMode with ⟨rfl, _, _⟩ | ⟨rfl, _⟩ <;> norm_num
  have hMassLe (t : ℝ) (ht : t ∈ Icc 0 δ) : m + e * t ≤ v₁ + t := by
    rcases hMass t ht with ⟨rfl, _, h⟩ | ⟨rfl, rfl⟩
    · simpa only [zero_mul, add_zero] using h
    · simp
  have hRowAnti := fourthSourceRow_strictAnti (u := u) (m := M) hp hp₂ hL hθ hv₂₀
  let f (t : ℝ) := fourthSourceRow p L θ u (v₁ + t) r₁ (m + e * t)
  have hPos (t : ℝ) (ht : t ∈ Icc 0 δ) : ∃ d > 0, HasDerivAt f d t :=
    fourthMotion_derivative_pos hp hp₂ hL hθ hu (hAt t ht).1 hr₁.1 he₀ (hMassLe t ht)
  have hInc : StrictMonoOn f (Icc 0 δ) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 δ)
    · intro t ht
      obtain ⟨_, _, h⟩ := hPos t ht
      exact h.continuousAt.continuousWithinAt
    · intro t ht
      obtain ⟨_, hp, h⟩ := hPos t (interior_subset ht)
      rw [h.deriv]
      exact hp
  have hZero : f 0 = 0 := by simpa only [f, mul_zero, add_zero] using hRoot₁
  have hVδ : v₁ + δ = v₂ := by dsimp only [δ]; ring
  have hAt₁ : 0 < fourthSourceRow p L θ u v₂ r₁ M := by
    have h := hInc ⟨le_rfl, hδ.le⟩ ⟨hδ.le, le_rfl⟩ hδ
    rwa [hZero, show f δ = fourthSourceRow p L θ u v₂ r₁ M by dsimp only [f, M]; rw [hVδ]] at h
  refine ⟨?_, ?_⟩
  · by_contra! h
    have hA := hRowAnti.antitoneOn hr₂.1 hr₁.1 h
    exact hAt₁.not_ge (hA.trans hRoot₂.le)
  let r' := r₁ + 2 * δ
  by_cases hr' : v₂ ≤ r'
  · linarith [hr₂.2]
  have hr'₂ : r' < v₂ := lt_of_not_ge hr'
  have hr'₀ : 0 < r' := add_pos_of_pos_of_nonneg hr₁.1 (mul_nonneg zero_le_two hδ.le)
  let g (t : ℝ) := fourthSourceRow p L θ u (v₁ + t) (r₁ + 2 * t) (m + e * t)
  have hNeg (t : ℝ) (ht : t ∈ Icc 0 δ) : ∃ d < 0, HasDerivAt g d t := by
    have hR₀ : 0 < r₁ + 2 * t := add_pos_of_pos_of_nonneg hr₁.1 (mul_nonneg zero_le_two ht.1)
    have hRV : r₁ + 2 * t ≤ v₁ + t := by linarith only [hr'₂, ht.2, hVδ]
    exact fourthMotion_derivative_neg hp hp₂ hL hθ (hAt t ht).1 (hAt t ht).2 hu₁ hR₀ hRV (hMass t ht)
  have hDec : StrictAntiOn g (Icc 0 δ) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 δ)
    · intro t ht
      obtain ⟨_, _, h⟩ := hNeg t ht
      exact h.continuousAt.continuousWithinAt
    · intro t ht
      obtain ⟨_, hn, h⟩ := hNeg t (interior_subset ht)
      rw [h.deriv]
      exact hn
  have hg0 : g 0 = 0 := by simpa only [g, mul_zero, add_zero] using hRoot₁
  have hAt₂ : fourthSourceRow p L θ u v₂ r' M < 0 := by
    have h := hDec ⟨le_rfl, hδ.le⟩ ⟨hδ.le, le_rfl⟩ hδ
    rwa [hg0, show g δ = fourthSourceRow p L θ u v₂ r' M by dsimp only [g, r', M]; rw [hVδ]] at h
  have hR₂ : r₂ < r' := by
    by_contra! h
    have hA := hRowAnti.antitoneOn hr'₀ hr₂.1 h
    exact hAt₂.not_ge (hRoot₂.ge.trans hA)
  linarith

end ACS12.GammaMeasure


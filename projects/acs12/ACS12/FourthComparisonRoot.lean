import ACS12.FourthRootMotion

/-! The fourth comparison root as a continuous function of the diagonal gap. -/

namespace ACS12.GammaMeasure

open Set

noncomputable def fourthComparisonRoot (p L θ u v m : ℝ) : ℝ := by
  classical
  exact if h : ∃ r ∈ Ioo 0 v, fourthSourceRow p L θ u v r m = 0 ∧
      ∀ q > 0, 0 ≤ fourthSourceRow p L θ u v q m → q ≤ r then Classical.choose h else 0

theorem fourthComparisonRoot_spec {p L θ u v m : ℝ} (hp : 1 ≤ p) (hp₂ : p < 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hv : 0 < v) (hvu : v ≤ u)
    (hu₁ : u < 1) (hm : 0 ≤ m) (hmv : m ≤ v) :
    let r := fourthComparisonRoot p L θ u v m
    r ∈ Ioo 0 v ∧ fourthSourceRow p L θ u v r m = 0 ∧
      ∀ q > 0, 0 ≤ fourthSourceRow p L θ u v q m → q ≤ r := by
  have h := exists_fourthSource_root hp hp₂ hL hθ hv hvu hu₁ hm hmv
  dsimp only
  unfold fourthComparisonRoot
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem fourthComparisonRoot_diagonal_speed {p L θ u x y : ℝ} (hp : 1 ≤ p) (hp₂ : p < 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hu₁ : u < 1)
    (hx : 0 < x) (hxy : x < y) (hy : y ≤ u) :
    let r := fourthComparisonRoot p L θ u x x
    let q := fourthComparisonRoot p L θ u y y
    r < q ∧ q - r < 2 * (y - x) := by
  have hy₀ := hx.trans hxy
  obtain ⟨h1, h2, _⟩ := fourthComparisonRoot_spec hp hp₂ hL hθ hx (hxy.le.trans hy) hu₁ hx.le le_rfl
  obtain ⟨h3, h4, _⟩ := fourthComparisonRoot_spec hp hp₂ hL hθ hy₀ hy hu₁ hy₀.le le_rfl
  have hE : x + 1 * (y - x) = y := by ring
  exact fourthSourceRoot_speed hp hp₂.le hL hθ hx hxy hy hu₁
    (Or.inr ⟨rfl, rfl⟩) h1 h3 h2 (hE.symm ▸ h4)

theorem fourthComparisonRoot_fixed_speed {p L θ u x y m : ℝ} (hp : 1 ≤ p) (hp₂ : p < 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hu₁ : u < 1)
    (hx : 0 < x) (hxy : x < y) (hy : y ≤ u)
    (hm₁ : y / 3 ≤ m) (hm₂ : m ≤ x) :
    let r := fourthComparisonRoot p L θ u x m
    let q := fourthComparisonRoot p L θ u y m
    r < q ∧ q - r < 2 * (y - x) := by
  have hy₀ := hx.trans hxy
  have hm : 0 ≤ m := (div_pos hy₀ (by norm_num : (0 : ℝ) < 3)).le.trans hm₁
  obtain ⟨h1, h2, _⟩ := fourthComparisonRoot_spec hp hp₂ hL hθ hx (hxy.le.trans hy) hu₁ hm hm₂
  obtain ⟨h3, h4, _⟩ := fourthComparisonRoot_spec hp hp₂ hL hθ hy₀ hy hu₁ hm (hm₂.trans hxy.le)
  have hE : m + 0 * (y - x) = m := by ring
  exact fourthSourceRoot_speed hp hp₂.le hL hθ hx hxy hy hu₁
    (Or.inl ⟨rfl, hm₁, hm₂⟩) h1 h3 h2 (hE.symm ▸ h4)

theorem fourthComparisonRoot_diagonal_continuousOn {p L θ u : ℝ} (hp : 1 ≤ p) (hp₂ : p < 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hu₁ : u < 1) :
    ContinuousOn (fun m => fourthComparisonRoot p L θ u m m) (Ioc 0 u) := by
  let f (m : ℝ) := fourthComparisonRoot p L θ u m m
  have hLip : LipschitzOnWith 2 f (Ioc 0 u) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rcases lt_trichotomy x y with h | rfl | h
    · obtain ⟨h₁, h₂⟩ := fourthComparisonRoot_diagonal_speed hp hp₂ hL hθ hu₁ hx.1 h hy.2
      change f x < f y at h₁
      change f y - f x < 2 * (y - x) at h₂
      rw [Real.dist_eq, Real.dist_eq, abs_of_neg (sub_neg.mpr h₁), abs_of_neg (sub_neg.mpr h),
        neg_sub, neg_sub]
      exact h₂.le
    · simp
    · obtain ⟨h₁, h₂⟩ := fourthComparisonRoot_diagonal_speed hp hp₂ hL hθ hu₁ hy.1 h hx.2
      change f y < f x at h₁
      change f x - f y < 2 * (x - y) at h₂
      rw [Real.dist_eq, Real.dist_eq, abs_of_pos (sub_pos.mpr h₁), abs_of_pos (sub_pos.mpr h)]
      exact h₂.le
  exact hLip.continuousOn

end ACS12.GammaMeasure


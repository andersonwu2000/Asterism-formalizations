import ACS12.JointFarLeftLicense
import ACS12.JointFarRightLicense

/-! One-sided Taylor bounds for the complete original adjacent streams. -/
namespace ACS12.GammaMeasure

open Set

private theorem monotoneOn_of_hasDerivAt_nonneg {a b : ℝ} {f d : ℝ → ℝ}
    (hD : ∀ x ∈ Icc a b, HasDerivAt f (d x) x)
    (hP : ∀ x ∈ Icc a b, 0 ≤ d x) : MonotoneOn f (Icc a b) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · exact fun x hx => (hD x hx).continuousAt.continuousWithinAt
  · exact fun x hx => (hD x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(hD x (interior_subset hx)).deriv]
    exact hP x (interior_subset hx)

private theorem cubic_upper {a b K : ℝ} {f f₁ f₂ f₃ : ℝ → ℝ}
    (h₁ : ∀ x ∈ Icc a b, HasDerivAt f (f₁ x) x)
    (h₂ : ∀ x ∈ Icc a b, HasDerivAt f₁ (f₂ x) x)
    (h₃ : ∀ x ∈ Icc a b, HasDerivAt f₂ (f₃ x) x)
    (hK : ∀ x ∈ Icc a b, f₃ x ≤ K) {x : ℝ} (hx : x ∈ Icc a b) :
    f x ≤ f a + f₁ a * (x - a) + f₂ a * (x - a) ^ 2 / 2 + K * (x - a) ^ 3 / 6 := by
  let R (t : ℝ) := f a + f₁ a * (t - a) + f₂ a * (t - a) ^ 2 / 2 + K * (t - a) ^ 3 / 6 - f t
  let R₁ (t : ℝ) := f₁ a + f₂ a * (t - a) + K * (t - a) ^ 2 / 2 - f₁ t
  let R₂ (t : ℝ) := f₂ a + K * (t - a) - f₂ t
  have hR₂ (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt R₂ (K - f₃ t) t := by
    simpa only [R₂,id_eq,mul_one] using
      ((((hasDerivAt_id t).sub_const a).const_mul K).const_add (f₂ a)).sub (h₃ t ht)
  have hR₁ (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt R₁ (R₂ t) t := by
    have h := (hasDerivAt_id t).sub_const a
    convert ((((h.const_mul (f₂ a)).const_add (f₁ a)).add (((h.pow 2).const_mul K).div_const 2))).sub
      (h₂ t ht) using 1
    simp only [R₂,id_eq,mul_one]
    ring
  have hR (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt R (R₁ t) t := by
    have h := (hasDerivAt_id t).sub_const a
    convert (((((h.const_mul (f₁ a)).const_add (f a)).add (((h.pow 2).const_mul (f₂ a)).div_const 2)).add
      (((h.pow 3).const_mul K).div_const 6))).sub (h₁ t ht) using 1
    simp only [R₁,id_eq,mul_one]
    ring
  have ha : a ∈ Icc a b := ⟨le_rfl,hx.1.trans hx.2⟩
  have h₂M := monotoneOn_of_hasDerivAt_nonneg hR₂ (fun t ht => sub_nonneg.mpr (hK t ht))
  have h₂P (t : ℝ) (ht : t ∈ Icc a b) : 0 ≤ R₂ t := by
    have h := h₂M ha ht ht.1
    simpa only [R₂,sub_self,mul_zero,add_zero,sub_self] using h
  have h₁M := monotoneOn_of_hasDerivAt_nonneg hR₁ h₂P
  have h₁P (t : ℝ) (ht : t ∈ Icc a b) : 0 ≤ R₁ t := by
    have h := h₁M ha ht ht.1
    simpa only [R₁,sub_self,mul_zero,zero_pow (by decide : 2 ≠ 0),zero_div,add_zero,sub_self] using h
  have hM := monotoneOn_of_hasDerivAt_nonneg hR h₁P
  have h := hM ha hx hx.1
  have hz : R a = 0 := by simp [R]
  rw [hz] at h
  exact sub_nonneg.mp h

theorem farRight_taylor {p U : ℝ} (hp : 1 ≤ p) (hpP : p ≤ 9 / 5)
    (hU : U ∈ Icc (1 : ℝ) (7 / 6)) :
    rightSourceSum 0 p U ≤ rightSourceSum 0 p 1 + rightSourceSum 1 p 1 * (U - 1) +
      rightSourceSum 2 p 1 * (U - 1) ^ 2 / 2 + (1063 / 1000) * (U - 1) ^ 3 / 6 := by
  have hp₂ : p ≤ 2 := hpP.trans (by norm_num)
  have hI (u : ℝ) (hu : u ∈ Icc (1 : ℝ) (7 / 6)) : u ∈ Ioo (0 : ℝ) 2 :=
    ⟨by linarith only [hu.1],by linarith only [hu.2]⟩
  exact cubic_upper (fun u hu => rightSourceSum_hasDerivAt hp hp₂ (hI u hu) (by decide : 0 < 4))
    (fun u hu => rightSourceSum_hasDerivAt hp hp₂ (hI u hu) (by decide : 1 < 4))
    (fun u hu => rightSourceSum_hasDerivAt hp hp₂ (hI u hu) (by decide : 2 < 4))
    (fun u hu => (farRight_third_lt hp hpP hu).le) hU

theorem farLeft_taylor {p δ : ℝ} (hp : 1 ≤ p) (hpP : p ≤ 9 / 5)
    (hd : δ ∈ Icc (0 : ℝ) (1 / 8)) :
    lowerKnownSum 0 p (1 - δ) ≤ lowerKnownSum 0 p 1 - lowerKnownSum 1 p 1 * δ +
      lowerKnownSum 2 p 1 * δ ^ 2 / 2 + δ ^ 3 / 4 := by
  have hp₂ : p ≤ 2 := hpP.trans (by norm_num)
  have hI (d : ℝ) (hx : d ∈ Icc (0 : ℝ) (1 / 8)) : 1 - d ∈ Ioo (0 : ℝ) 2 :=
    ⟨by linarith only [hx.2],by linarith only [hx.1]⟩
  have hD {k : ℕ} (hk : k < 3) (d : ℝ) (hx : d ∈ Icc (0 : ℝ) (1 / 8)) :
      HasDerivAt (fun t => lowerKnownSum k p (1 - t)) (-lowerKnownSum (k + 1) p (1 - d)) d := by
    simpa only [mul_neg,mul_one] using (lowerKnownSum_hasDerivAt hp hp₂ (hI d hx) hk).comp d
      ((hasDerivAt_id d).const_sub 1)
  have h := cubic_upper (f := fun d => lowerKnownSum 0 p (1 - d))
    (f₁ := fun d => -lowerKnownSum 1 p (1 - d)) (f₂ := fun d => lowerKnownSum 2 p (1 - d))
    (f₃ := fun d => -lowerKnownSum 3 p (1 - d)) (K := 3 / 2)
    (hD (by decide)) (fun d hx => by simpa only [neg_neg] using (hD (by decide : 1 < 3) d hx).neg)
    (hD (by decide)) (fun d hx => (farLeft_third_lt hp hpP hx.1 hx.2).le) hd
  simp only [sub_zero,neg_mul] at h
  linarith only [h]

end ACS12.GammaMeasure

import ACS12.RightClip

/-! The signed left multiplier and the full-integral one-cut comparison. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set

noncomputable def leftMultiplier (a z s : ℝ) : ℝ :=
  1 - Real.exp (-s) - a * s - z * s * Real.exp (-s)

theorem leftMultiplier_abs_le (a z : ℝ) {s : ℝ} (hs : 0 < s) :
    |leftMultiplier a z s| ≤ (1 + |a| + |z|) * s := by
  have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.le)
  have h₀ : 0 ≤ 1 - Real.exp (-s) := sub_nonneg.mpr he
  have h₁ : 1 - Real.exp (-s) ≤ s := by linarith [Real.add_one_le_exp (-s)]
  unfold leftMultiplier
  calc
    _ ≤ |1 - Real.exp (-s) - a * s| + |z * s * Real.exp (-s)| := abs_sub _ _
    _ ≤ (|1 - Real.exp (-s)| + |a * s|) + |z * s * Real.exp (-s)| :=
      add_le_add_left (abs_sub _ _) _
    _ ≤ s + |a| * s + |z| * s := by
      rw [abs_of_nonneg h₀, abs_mul a s, abs_of_pos hs, abs_mul (z * s),
        abs_mul z s, abs_of_pos hs, abs_of_pos (Real.exp_pos _)]
      exact add_le_add (add_le_add_left h₁ _) (mul_le_of_le_one_right (by positivity) he)
    _ = _ := by ring

/-- A positive initial sign and a negative terminal sign on the whole ray. -/
theorem leftMultiplier_one_cut {a z : ℝ} (ha : 0 < a) (ha₂ : a < 1 / 2)
    (hz : 0 ≤ z) (haz : a + z ≤ 1) :
    ∃ c > 0, (∀ s ∈ Ioo 0 c, 0 < leftMultiplier a z s) ∧
      leftMultiplier a z c = 0 ∧ (∀ s > c, leftMultiplier a z s < 0) := by
  let f (s : ℝ) := (1 - a * s) * Real.exp s - 1 - z * s
  let d₁ (s : ℝ) := (1 - a - a * s) * Real.exp s - z
  let d₂ (s : ℝ) := (1 - 2 * a - a * s) * Real.exp s
  have hD₁ (s : ℝ) : HasDerivAt f (d₁ s) s := by
    have h := (((((hasDerivAt_id s).const_mul a).const_sub 1).mul
      (Real.hasDerivAt_exp s)).sub_const 1).sub ((hasDerivAt_id s).const_mul z)
    convert h using 1
    simp only [d₁, id_eq, mul_one]
    ring
  have hD₂ (s : ℝ) : HasDerivAt d₁ (d₂ s) s := by
    have h := (((hasDerivAt_id s).const_mul a).const_sub (1 - a)).mul (Real.hasDerivAt_exp s)
    convert h.sub_const z using 1
    simp only [d₂, id_eq, mul_one]
    ring
  let b := (1 - 2 * a) / a
  let e := (1 - a) / a
  let q := 1 / a
  have hb : 0 < b := div_pos (by linarith) ha
  have hbe : b < e := div_lt_div_of_pos_right (by linarith) ha
  have heq : e < q := div_lt_div_of_pos_right (by linarith) ha
  have hab : a * b = 1 - 2 * a := by
    dsimp [b]
    field_simp
  have hae : a * e = 1 - a := by
    dsimp [e]
    field_simp
  have haq : a * q = 1 := by
    dsimp [q]
    field_simp
  have hInc : StrictMonoOn d₁ (Icc 0 b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · exact fun s _ => (hD₂ s).continuousAt.continuousWithinAt
    · intro s hs
      have hsB : s < b := ((interior_Icc (a := (0 : ℝ)) (b := b)) ▸ hs).2
      rw [(hD₂ s).deriv]
      unfold d₂
      have h := mul_lt_mul_of_pos_left hsB ha
      exact mul_pos (by linarith) (Real.exp_pos _)
  have hDec : StrictAntiOn d₁ (Ici b) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici _)
    · exact fun s _ => (hD₂ s).continuousAt.continuousWithinAt
    · intro s hs
      have hsB : b < s := by simpa only [interior_Ici, mem_Ioi] using hs
      rw [(hD₂ s).deriv]
      unfold d₂
      have h := mul_lt_mul_of_pos_left hsB ha
      exact mul_neg_of_neg_of_pos (by linarith) (Real.exp_pos _)
  have hd₀ : 0 ≤ d₁ 0 := by
    norm_num [d₁]
    linarith
  have hdB : 0 < d₁ b := hd₀.trans_lt (hInc ⟨le_rfl, hb.le⟩ ⟨hb.le, le_rfl⟩ hb)
  have hdE : d₁ e ≤ 0 := by
    unfold d₁
    rw [hae, sub_self, zero_mul, zero_sub]
    exact neg_nonpos.mpr hz
  have hdC : ContinuousOn d₁ (Icc b e) := fun s _ => (hD₂ s).continuousAt.continuousWithinAt
  obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc' hbe.le hdC ⟨hdE, hdB.le⟩
  have hR : 0 < r := hb.trans_le hr.1
  have hf₀ : f 0 = 0 := by norm_num [f]
  have hfInc : StrictMonoOn f (Icc 0 r) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · exact fun s _ => (hD₁ s).continuousAt.continuousWithinAt
    · intro s hs
      have hs' : s ∈ Ioo 0 r := by simpa only [interior_Icc] using hs
      rw [(hD₁ s).deriv]
      rcases le_total s b with hsb | hbs
      · exact hd₀.trans_lt (hInc ⟨le_rfl, hb.le⟩ ⟨hs'.1.le, hsb⟩ hs'.1)
      · rw [← hr0]
        exact hDec hbs hr.1 hs'.2
  have hfDec : StrictAntiOn f (Ici r) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici _)
    · exact fun s _ => (hD₁ s).continuousAt.continuousWithinAt
    · intro s hs
      have hs' : r < s := by simpa only [interior_Ici, mem_Ioi] using hs
      rw [(hD₁ s).deriv, ← hr0]
      exact hDec hr.1 (hr.1.trans hs'.le) hs'
  have hfR : 0 < f r := by
    rw [← hf₀]
    exact hfInc ⟨le_rfl, hR.le⟩ ⟨hR.le, le_rfl⟩ hR
  have hfQ : f q < 0 := by
    unfold f
    rw [haq, sub_self, zero_mul, zero_sub]
    have hq₀ : 0 ≤ q := (hR.trans (hr.2.trans_lt heq)).le
    linarith [mul_nonneg hz hq₀]
  have hfC : ContinuousOn f (Icc r q) := fun s _ => (hD₁ s).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' (hr.2.trans heq.le) hfC ⟨hfQ.le, hfR.le⟩
  have hFactor (s : ℝ) : leftMultiplier a z s * Real.exp s = f s := by
    have h : Real.exp (-s) * Real.exp s = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    unfold leftMultiplier f
    linear_combination -(1 + z * s) * h
  refine ⟨c, hR.trans_le hc.1, ?_, ?_, ?_⟩
  · intro s hs
    have hPos : 0 < f s := by
      rcases le_total s r with hsr | hrs
      · rw [← hf₀]
        exact hfInc ⟨le_rfl, hR.le⟩ ⟨hs.1.le, hsr⟩ hs.1
      · rw [← hc0]
        exact hfDec hrs hc.1 hs.2
    exact pos_of_mul_pos_left ((hFactor s).symm ▸ hPos) (Real.exp_pos s).le
  · exact (mul_eq_zero.mp ((hFactor c).trans hc0)).resolve_right (Real.exp_ne_zero _)
  · intro s hs
    have hNeg : f s < 0 := by
      rw [← hc0]
      exact hfDec hc.1 (hc.1.trans hs.le) hs
    exact neg_of_mul_neg_left ((hFactor s).symm ▸ hNeg) (Real.exp_pos s).le

/-- The signed integral stays positive under a positive decreasing multiplier. -/
theorem positive_integral_of_one_cut {f g : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hF : IntegrableOn f (Ioi 0)) (hG : IntegrableOn (fun s => f s * g s) (Ioi 0))
    (hBefore : ∀ s ∈ Ioo 0 c, 0 ≤ f s) (hAfter : ∀ s > c, f s ≤ 0)
    (hg : AntitoneOn g (Ioi 0)) (hgc : 0 < g c)
    (hP : 0 < ∫ s : ℝ in Ioi 0, f s) :
    0 < ∫ s : ℝ in Ioi 0, f s * g s := by
  have h := integral_mono_ae (hF.mul_const (g c)) hG ?_
  · rw [integral_mul_const] at h
    exact (mul_pos hP hgc).trans_le h
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rcases lt_trichotomy s c with hsc | hsc | hcs
    · exact mul_le_mul_of_nonneg_left (hg hs hc hsc.le) (hBefore s ⟨hs, hsc⟩)
    · subst s
      rfl
    · exact mul_le_mul_of_nonpos_left (hg hc hs hcs.le) (hAfter s hcs)

end ACS12.GammaMeasure


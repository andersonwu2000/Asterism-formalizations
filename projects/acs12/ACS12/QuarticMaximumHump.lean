import ACS12.HighPhysicalHumpCapacity

/-! One occupied-semicircle integral for the actual comparison barycenter. -/
namespace ACS12.HighCurrent

open Set MeasureTheory

noncomputable def quarticHump (x B z : ℝ) : ℝ :=
  max 0 (z ^ 2 * (1 - (x + z ^ 2) / B))

theorem quarticHump_continuous (x B : ℝ) : Continuous (quarticHump x B) := by
  unfold quarticHump
  fun_prop

theorem quarticHump_nonneg (x B z : ℝ) : 0 ≤ quarticHump x B z := le_max_left _ _

theorem quarticHump_height {x B : ℝ} (hB : 0 < B) (z : ℝ) :
    quarticHump x B z ≤ (B - x) ^ 2 / (4 * B) := by
  unfold quarticHump
  apply max_le (by positivity)
  apply (le_div_iff₀ (by positivity : 0 < 4 * B)).mpr
  have hEq : z ^ 2 * (1 - (x + z ^ 2) / B) * (4 * B) = 4 * z ^ 2 * (B - x - z ^ 2) := by
    field_simp [hB.ne']
    ring
  rw [hEq]
  nlinarith only [sq_nonneg (B - x - 2 * z ^ 2)]

theorem quarticHump_min {x B a b c : ℝ} (hB : 0 < B)
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    min (quarticHump x B a) (quarticHump x B c) ≤ quarticHump x B b := by
  have hba := pow_le_pow_left₀ ha hab 2
  have hcb := pow_le_pow_left₀ (ha.trans hab) hbc 2
  by_cases h : 2 * b ^ 2 ≤ B - x
  · apply (min_le_left _ _).trans
    unfold quarticHump
    apply max_le_max_left
    apply (mul_le_mul_iff_left₀ hB).mp
    have hh := mul_nonneg (sub_nonneg.mpr hba) (show 0 ≤ B - x - b ^ 2 - a ^ 2 by linarith)
    field_simp [hB.ne']
    nlinarith only [hh]
  · apply (min_le_right _ _).trans
    unfold quarticHump
    apply max_le_max_left
    apply (mul_le_mul_iff_left₀ hB).mp
    have hh := mul_nonneg (sub_nonneg.mpr hcb) (show 0 ≤ c ^ 2 + b ^ 2 - (B - x) by linarith [le_of_not_ge h])
    field_simp [hB.ne']
    nlinarith only [hh]

private theorem quarticHump_integral {x B Z : ℝ} (hx : 0 < x) (hB : x < B) :
    (∫ z in (0 : ℝ)..Z, quarticHump x B z / (x + z ^ 2)) ≤
      (2 / 3) * Real.sqrt B - Real.sqrt x + x * Real.sqrt x / (3 * B) := by
  let b := Real.sqrt (B - x)
  let f (z : ℝ) := quarticHump x B z / (x + z ^ 2)
  let W (z : ℝ) := Real.sqrt (x + z ^ 2)
  let primitive (z : ℝ) := W z - (W z) ^ 3 / (3 * B)
  let g (z : ℝ) := z / W z * (1 - (x + z ^ 2) / B)
  have hB₀ : 0 < B := hx.trans hB
  have hSq (z : ℝ) : W z ^ 2 = x + z ^ 2 := Real.sq_sqrt (by positivity)
  have hW (z : ℝ) : 0 < W z := Real.sqrt_pos.mpr (by positivity)
  have hb : 0 < b := Real.sqrt_pos.mpr (sub_pos.mpr hB)
  have hb₂ : b ^ 2 = B - x := Real.sq_sqrt (sub_nonneg.mpr hB.le)
  have hC : Continuous f :=
    (quarticHump_continuous x B).div (by fun_prop) (fun z => (show 0 < x + z ^ 2 by positivity).ne')
  have hC' : Continuous g := by
    have hc : Continuous W := by unfold W; fun_prop
    exact (continuous_id.div hc (fun z => (hW z).ne')).mul (by fun_prop)
  have hLower (z : ℝ) : 0 ≤ f z := div_nonneg (quarticHump_nonneg _ _ _) (by positivity)
  have hMain : (∫ z in (0 : ℝ)..Z, f z) ≤ ∫ z in (0 : ℝ)..b, f z := by
    by_cases h : Z ≤ b
    · have hAdd := intervalIntegral.integral_add_adjacent_intervals
        (hC.intervalIntegrable (μ := volume) 0 Z) (hC.intervalIntegrable (μ := volume) Z b)
      linarith only [hAdd, intervalIntegral.integral_nonneg (μ := volume) h (fun z _ => hLower z)]
    · have hbZ := le_of_not_ge h
      have hZero : (∫ z in b..Z, f z) = 0 := by
        rw [← intervalIntegral.integral_zero]
        apply intervalIntegral.integral_congr
        intro z hz
        rw [uIcc_of_le hbZ] at hz
        have hz₂ := pow_le_pow_left₀ hb.le hz.1 2
        unfold f quarticHump
        have hSign : 1 - (x + z ^ 2) / B ≤ 0 := by
          apply sub_nonpos.mpr
          exact (one_le_div hB₀).mpr (by linarith only [hb₂, hz₂])
        rw [max_eq_left (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg z) hSign), zero_div]
      have hAdd := intervalIntegral.integral_add_adjacent_intervals
        (hC.intervalIntegrable (μ := volume) 0 b) (hC.intervalIntegrable (μ := volume) b Z)
      linarith only [hAdd, hZero]
  apply hMain.trans
  have hUp : (∫ z in (0 : ℝ)..b, f z) ≤ ∫ z in (0 : ℝ)..b, g z := by
    apply intervalIntegral.integral_mono_on hb.le (hC.intervalIntegrable _ _) (hC'.intervalIntegrable _ _)
    intro z hz
    have hz₂ := pow_le_pow_left₀ hz.1 hz.2 2
    have hSign : 0 ≤ 1 - (x + z ^ 2) / B := by
      apply sub_nonneg.mpr
      exact (div_le_one hB₀).mpr (by linarith only [hb₂, hz₂])
    have hRatio : z / W z ≤ 1 := (div_le_one (hW z)).mpr (Real.le_sqrt_of_sq_le (by linarith only [hx]))
    have hR₀ := div_nonneg hz.1 (hW z).le
    have hR := mul_le_mul_of_nonneg_left hRatio hR₀
    rw [← pow_two, div_pow, hSq, mul_one] at hR
    unfold f quarticHump g
    rw [max_eq_right (mul_nonneg (sq_nonneg z) hSign), mul_div_right_comm]
    exact mul_le_mul_of_nonneg_right hR hSign
  apply hUp.trans
  have hDer (z : ℝ) : HasDerivAt primitive (g z) z := by
    have h := ((hasDerivAt_id z).pow 2).const_add x
    have h₀ := h.sqrt (show x + z ^ 2 ≠ 0 by positivity)
    convert h₀.sub ((h₀.pow 3).div_const (3 * B)) using 1
    simp only [g, W, Pi.pow_apply, id_eq, Nat.reduceSub, pow_one, mul_one, Nat.cast_ofNat]
    rw [Real.sq_sqrt (by positivity : 0 ≤ x + z ^ 2)]
    field_simp [(hW z).ne', hB₀.ne']
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => hDer z) (hC'.intervalIntegrable _ _)]
  have hWb : W b = Real.sqrt B := by unfold W; rw [hb₂]; congr 1; ring
  have hW0 : W 0 = Real.sqrt x := by simp [W]
  have hCube {v : ℝ} (hv : 0 ≤ v) : Real.sqrt v ^ 3 = v * Real.sqrt v := by
    rw [pow_succ, Real.sq_sqrt hv]
  unfold primitive
  rw [hW0, hWb, hCube hx.le, hCube hB₀.le]
  field_simp [hB₀.ne']
  linarith

theorem quarticHump_arc_integral {x B a b : ℝ} {z : ℝ → ℝ}
    (hx : 0 < x) (hB : x < B) (hab : a ≤ b)
    (hZ : ContinuousOn z (Icc a b))
    (hD : ∀ s ∈ Icc a b, HasDerivAt z (-(x + z s ^ 2)) s)
    (_hZa : 0 ≤ z a) (hZb : z b = 0) :
    (∫ s in a..b, quarticHump x B (z s)) ≤
      (2 / 3) * Real.sqrt B - Real.sqrt x + x * Real.sqrt x / (3 * B) := by
  let f (v : ℝ) := quarticHump x B v / (x + v ^ 2)
  have hF : Continuous f := (quarticHump_continuous x B).div (by fun_prop)
    (fun v => (show 0 < x + v ^ 2 by positivity).ne')
  have hSub := intervalIntegral.integral_comp_mul_deriv
    (fun t ht => hD t (by simpa only [uIcc_of_le hab] using ht))
    (show ContinuousOn (fun s => -(x + z s ^ 2)) (uIcc a b) by rw [uIcc_of_le hab]; fun_prop) hF
  have hLeft : (∫ s in a..b, (f ∘ z) s * (-(x + z s ^ 2))) =
      -(∫ s in a..b, quarticHump x B (z s)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro s _
    simp only [Function.comp_apply, f]
    field_simp [show x + z s ^ 2 ≠ 0 by positivity]
  rw [hLeft, hZb, intervalIntegral.integral_symm 0 (z a)] at hSub
  rw [neg_injective hSub]
  exact quarticHump_integral hx hB

end ACS12.HighCurrent

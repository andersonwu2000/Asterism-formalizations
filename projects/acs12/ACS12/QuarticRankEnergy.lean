import ACS12.QuarticRankGap
import ACS12.QuarticRankMoments
import ACS12.QuarticRankLogBounds

/-! The actual and regular quartic trials use the same directed rank normalization. -/
namespace ACS12.NativeCells

open Finset
set_option backward.isDefEq.respectTransparency false

noncomputable def quarticRankFactor (w : ℝ) : ℝ :=
  Real.sqrt (w / analyticRow 4 w⁻¹) / Real.sin (Real.pi * w) ^ 2

noncomputable def quarticRankScale (n : ℕ) : ℝ :=
  quarticRankFactor (1 / (n : ℝ)) ^ 2

noncomputable def quarticRankPrefactor {n : ℕ} (w : Fin n → ℝ) (i j : Fin n) : ℝ :=
  quarticRankFactor (w i) * quarticRankFactor (w j) / quarticRankScale n

private theorem width_sine_pos {w : ℝ} (hw : 0 < w) (hw₁ : w < 1) :
    0 < Real.sin (Real.pi * w) :=
  Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hw)
    (by nlinarith only [mul_pos Real.pi_pos (sub_pos.mpr hw₁)])

theorem quarticRankFactor_pos {w : ℝ} (hw : 0 < w) (hw₁ : w < 1) :
    0 < quarticRankFactor w :=
  div_pos (Real.sqrt_pos.mpr (div_pos hw (analyticRow_pos (by norm_num) ((one_lt_inv₀ hw).mpr hw₁))))
    (sq_pos_of_pos (width_sine_pos hw hw₁))

theorem quarticRankScale_pos {n : ℕ} (hn : 2 ≤ n) : 0 < quarticRankScale n := by
  have hN : (1 : ℝ) < n := Nat.one_lt_cast.mpr (by omega)
  exact sq_pos_of_pos (quarticRankFactor_pos (one_div_pos.mpr (zero_lt_one.trans hN))
    ((div_lt_one (zero_lt_one.trans hN)).mpr hN))

theorem quarticRankPrefactor_pos {n : ℕ} (hn : 2 ≤ n) {w : Fin n → ℝ}
    (hw : ∀ i, 0 < w i) (hw₁ : ∀ i, w i < 1) (i j : Fin n) :
    0 < quarticRankPrefactor w i j :=
  div_pos (mul_pos (quarticRankFactor_pos (hw i) (hw₁ i)) (quarticRankFactor_pos (hw j) (hw₁ j)))
    (quarticRankScale_pos hn)

theorem quarticRankFactor_log {w : ℝ} (hw : 0 < w) (hcap : w ≤ 1 / 4) :
    2 * Real.log (quarticRankFactor w) = Real.log w - quarticLogGauge w := by
  have hw₁ : w < 1 := by linarith only [hcap]
  have hR := analyticRow_pos (by norm_num : (0 : ℝ) < 4) ((one_lt_inv₀ hw).mpr hw₁)
  have hs := width_sine_pos hw hw₁
  have hQ := div_pos hw hR
  rw [quarticRankFactor, Real.log_div (Real.sqrt_pos.mpr hQ).ne' (sq_pos_of_pos hs).ne',
    Real.log_sqrt hQ.le, Real.log_div hw.ne' hR.ne', Real.log_pow,
    quarticLogGauge_eq_row hw hcap]
  ring

private theorem quarticGauge_eq_factor (p : ℝ) {w : ℝ} (hw : 0 < w) (hw₁ : w < 1) :
    quarticGauge p w = quarticRankFactor w * Real.sin (Real.pi * w) ^ (p / 2) := by
  have hs := width_sine_pos hw hw₁
  unfold quarticGauge quarticRankFactor
  rw [show p / 2 = 2 + (p - 4) / 2 by ring, Real.rpow_add hs, Real.rpow_ofNat]
  rw [← mul_assoc, div_mul_cancel₀ _ (pow_ne_zero 2 hs.ne')]

theorem quartic_pair_energy {n : ℕ} {p : ℝ} {w : Fin n → ℝ} (hn : 2 ≤ n)
    (hw : ∀ i, 0 < w i) (hw₁ : ∀ i, w i < 1) (hW : ∑ i, w i = 1)
    {i j : Fin n} (hij : j ≠ i) :
    quarticGauge p (w i) * quarticGauge p (w j) * angularCost p (halfArc (quarticCellAngle w) i j) =
      quarticRankScale n * (quarticRankPrefactor w i j * Real.exp (-p * quarticActualGap w i j)) := by
  let a := quarticCellAngle w
  let v (i : Fin n) := Real.sin (Real.pi * w i)
  let s := Real.sin (halfArc a i j)
  have ha : StrictMono a := center_strictMono (massCells_strictMonoOn hw)
  have hb (k : Fin n) : a k ∈ Set.Ioo 0 (2 * Real.pi) :=
    center_mem (massCells_strictMonoOn hw) (massCells_zero w) (massCells_end hW) k
  have hArc := halfArc_mem ha (fun k => (hb k).1.le) (fun k => (hb k).2) hij
  have hs : 0 < s := Real.sin_pos_of_pos_of_lt_pi hArc.1 hArc.2
  have hv (k : Fin n) : 0 < v k := width_sine_pos (hw k) (hw₁ k)
  have hSQ := Real.sqrt_pos.mpr (mul_pos (hv i) (hv j))
  have hE : Real.exp (-p * quarticActualGap w i j) = (Real.sqrt (v i * v j) / s) ^ p := by
    change Real.exp (-p * Real.log (s / Real.sqrt (v i * v j))) = _
    rw [neg_mul, Real.exp_neg, mul_comm p,
      ← Real.rpow_def_of_pos (div_pos hs hSQ), Real.div_rpow hs.le hSQ.le, inv_div,
      ← Real.div_rpow hSQ.le hs.le]
  have hFactor : (Real.sqrt (v i * v j)) ^ p = v i ^ (p / 2) * v j ^ (p / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (mul_pos (hv i) (hv j)).le,
      show (1 / 2 : ℝ) * p = p / 2 by ring, Real.mul_rpow (hv i).le (hv j).le]
  rw [quarticGauge_eq_factor p (hw i) (hw₁ i), quarticGauge_eq_factor p (hw j) (hw₁ j), hE]
  unfold quarticRankPrefactor angularCost
  change (quarticRankFactor (w i) * v i ^ (p / 2)) * (quarticRankFactor (w j) * v j ^ (p / 2)) *
      (1 / s ^ p) = _
  rw [Real.div_rpow hSQ.le hs.le, hFactor]
  field_simp [(quarticRankScale_pos hn).ne', (Real.rpow_pos_of_pos hs p).ne']

theorem quarticZ_rank_sum {n : ℕ} [NeZero n] {p : ℝ} {w : Fin n → ℝ}
    (hn : 2 ≤ n) (hp : 0 < p) (hw : ∀ i, 0 < w i) (hw₁ : ∀ i, w i < 1) (hW : ∑ i, w i = 1) :
    quarticZ p w = quarticRankScale n * ∑ r ∈ (univ : Finset (Fin n)).erase 0,
      ∑ i, quarticRankPrefactor w i (i + r) * Real.exp (-p * quarticActualGap w i (i + r)) := by
  let a := quarticCellAngle w
  let v (i : Fin n) := quarticGauge p (w i)
  let f (i j : Fin n) := v i * v j * angularCost p (halfArc a i j)
  have hZero (i : Fin n) : f i i = 0 := by
    simp [f, halfArc_self, angularCost, Real.zero_rpow hp.ne']
  have hRow (i : Fin n) : (∑ j, f i j) = ∑ r ∈ (univ : Finset (Fin n)).erase 0, f i (i + r) := by
    rw [sum_erase_eq_sub (mem_univ (0 : Fin n)), add_zero, hZero, sub_zero]
    exact (Equiv.sum_comp (Equiv.addLeft i) (f i)).symm
  change (∑ i, ∑ j, f i j) = _
  simp_rw [hRow]
  rw [sum_comm, mul_sum]
  apply sum_congr rfl
  intro r hr
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  have hr0 := (mem_erase.mp hr).1
  exact quartic_pair_energy hn hw hw₁ hW (fun h => hr0 (add_left_cancel (h.trans (add_zero i).symm)))

/-- The regular normalization uses exactly the same finite rank sum at every exponent. -/
theorem quarticRegular_rank_sum {n : ℕ} [NeZero n] {p : ℝ} (hn : 2 ≤ n) (hp : 0 < p) :
    quarticRegularRatio p n = ((n : ℝ) * quarticRankScale n) *
      ∑ r ∈ (univ : Finset (Fin n)).erase 0, Real.exp (-p * quarticRegularGap r) := by
  let s := Real.sin (Real.pi / (n : ℝ))
  have hN : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hN₁ : 1 < (n : ℝ) := Nat.one_lt_cast.mpr (by omega)
  have hR := analyticRow_pos (by norm_num : (0 : ℝ) < 4) hN₁
  have hs : 0 < s := nearest_sine_pos hn
  have hTerm (r : Fin n) (hr : r ∈ (univ : Finset (Fin n)).erase 0) :
      Real.exp (-p * quarticRegularGap r) = s ^ p * angularCost p (Real.pi * (r : ℝ) / (n : ℝ)) := by
    have hsr := rank_sine_pos (mem_erase.mp hr).1
    calc
      _ = (Real.exp (-quarticRegularGap r)) ^ p := by
        rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
        congr 1
        ring
      _ = _ := by
        rw [exp_neg_regular_gap hn (mem_erase.mp hr).1, Real.div_rpow hs.le hsr.le, angularCost]
        ring
  have hScale :
      ((n : ℝ) * quarticRankScale n) * s ^ p = s ^ (p - 4) / analyticRow 4 n := by
    unfold quarticRankScale quarticRankFactor
    rw [div_pow, Real.sq_sqrt (div_nonneg (by positivity) (by
      convert hR.le using 1
      rw [one_div, inv_inv])), show (1 / (n : ℝ))⁻¹ = n by rw [one_div, inv_inv],
      show Real.pi * (1 / (n : ℝ)) = Real.pi / n by ring, ← pow_mul]
    change (n : ℝ) * ((1 / (n : ℝ)) / analyticRow 4 n / s ^ (4 : ℕ)) * s ^ p = _
    have hPow : s ^ p = s ^ (p-4) * s ^ (4:ℕ) := by
      rw [← Real.rpow_natCast,← Real.rpow_add hs]
      congr 1
      norm_num
    rw [hPow]
    field_simp [hN.ne', hR.ne', hs.ne']
  rw [sum_congr rfl hTerm, ← mul_sum, ← analyticRow_integer hn hp, ← mul_assoc, hScale]
  unfold quarticRegularRatio
  ring

theorem quarticNearest_lower_regular {n : ℕ} [NeZero n] {p : ℝ} (hn : 5 ≤ n) (hp : 0 < p) :
    2 * ((n : ℝ) * quarticRankScale n) ≤ quarticRegularRatio p n := by
  have hn₂ : 2 ≤ n := by omega
  have h₁ : ((1 : Fin n) : ℕ) = 1 :=
    (Fin.val_one' n).trans (Nat.mod_eq_of_lt (by omega))
  have hm : ((-1 : Fin n) : ℕ) = n - 1 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp
  have h10 : (1 : Fin n) ≠ 0 := by intro h; have := congrArg Fin.val h; simp at *; omega
  have hm0 : (-1 : Fin n) ≠ 0 := by intro h; have := congrArg Fin.val h; simp at *; omega
  have hm1 : (-1 : Fin n) ≠ 1 := by intro h; have := congrArg Fin.val h; omega
  let T := (univ : Finset (Fin n)).erase 0
  let f (r : Fin n) := Real.exp (-p * quarticRegularGap r)
  have hmem1 : (1 : Fin n) ∈ T := mem_erase.mpr ⟨h10, mem_univ _⟩
  have hmemM : (-1 : Fin n) ∈ T.erase 1 :=
    mem_erase.mpr ⟨hm1, mem_erase.mpr ⟨hm0, mem_univ _⟩⟩
  obtain ⟨hs₁, hsm⟩ := nearest_sines hn₂
  have hOne : quarticRegularGap (1 : Fin n) = 0 := by
    rw [quarticRegularGap, hs₁, div_self (nearest_sine_pos hn₂).ne', Real.log_one]
  have hNeg : quarticRegularGap (-1 : Fin n) = 0 := by
    rw [quarticRegularGap, hsm, div_self (nearest_sine_pos hn₂).ne', Real.log_one]
  have h1 : f 1 = 1 := by simp [f, hOne]
  have h2 : f (-1) = 1 := by simp [f, hNeg]
  have hSum : (2 : ℝ) ≤ ∑ i ∈ T, f i := by
    have hNon : 0 ≤ ∑ i ∈ (T.erase 1).erase (-1), f i :=
      sum_nonneg (fun _ _ => (Real.exp_pos _).le)
    rw [sum_erase_eq_sub hmemM, sum_erase_eq_sub hmem1, h1, h2] at hNon
    linarith only [hNon]
  rw [quarticRegular_rank_sum hn₂ hp, mul_comm 2]
  exact mul_le_mul_of_nonneg_left hSum (mul_nonneg (Nat.cast_nonneg _) (quarticRankScale_pos hn₂).le)

end ACS12.NativeCells

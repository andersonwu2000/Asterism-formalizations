import ACS12.JointLowerCentralExpansion
import ACS12.JointLowerCentralRatio

/-! The third response of each higher centered native coefficient has the favorable sign. -/
namespace ACS12.GammaMeasure

open Set

noncomputable def lowerCentralResponse (k : ℕ) (p J : ℝ) (n : ℕ) (d : ℝ) : ℝ :=
  let q := p + 1 + (n : ℝ)
  let a := (n : ℝ) / ((n : ℝ) + 1)
  if Even n then
    weightedAffineResponse k a (-(1 + 2 * a)) 2 0 (J + 1) (2 * J) q d
  else
    weightedAffineResponse k (13 / 25) (-(51 / 25)) (62 / 25) (-(24 / 25)) (J + 1) (2 * J) q d

theorem lowerCentralResponse_zero (p J : ℝ) (n : ℕ) (d : ℝ) :
    lowerCentralResponse 0 p J n d =
      (1 - 2 * d) * lowerCentralCoefficient n d * (J * (1 - 2 * d) + 1) ^ (-(p + 1 + (n : ℝ))) := by
  unfold lowerCentralResponse lowerCentralCoefficient
  split_ifs <;> rw [weightedAffineResponse_zero,show J + 1 - 2 * J * d = J * (1 - 2 * d) + 1 by ring] <;> ring

theorem lowerCentralResponse_deriv {k : ℕ} (hk : k < 3) {p J d : ℝ}
    (hJ : 0 ≤ J) (hd : d < 1 / 2) (n : ℕ) :
    HasDerivAt (lowerCentralResponse k p J n) (lowerCentralResponse (k + 1) p J n d) d := by
  have hY : 0 < J + 1 - 2 * J * d := by
    nlinarith only [mul_nonneg hJ (show 0 ≤ 1 - 2 * d by linarith only [hd])]
  unfold lowerCentralResponse
  split_ifs
  · exact weightedAffineResponse_deriv hk _ _ _ _ _ _ _ _ hY
  · exact weightedAffineResponse_deriv hk _ _ _ _ _ _ _ _ hY

private theorem centralMass_responses (q J d : ℝ) (hm : 0 < 1 - 2 * d)
    (hY : 0 < J * (1 - 2 * d) + 1) :
    let m := 1 - 2 * d
    let y := J * m + 1
    let X := y⁻¹
    let D (k : ℕ) := weightedAffineResponse k 1 (-2) 0 0 (J + 1) (2 * J) q d
    D 1 = 2 * y ^ (-q) * (q - 1 - q * X) ∧
      D 2 = (4 * q / m) * y ^ (-q) * (1 - X) * (q - 1 - (q + 1) * X) ∧
      D 3 = (8 * q * (q + 1) / m ^ 2) * y ^ (-q) * (1 - X) ^ 2 * (q - 1 - (q + 2) * X) := by
  let m := 1 - 2 * d
  let y := J * m + 1
  let X := y⁻¹
  let b := 2 * J
  have hm' : 0 < m := hm
  have hy' : 0 < y := hY
  have hEq : J + 1 - b * d = y := by unfold b y m; ring
  have h₁ : y ^ (-q - 1) = y ^ (-q) / y := Real.rpow_sub_one hy'.ne' _
  have h₂ : y ^ (-q - 2) = y ^ (-q) / y ^ (2 : ℕ) := by
    rw [show -q - 2 = -q - 1 - 1 by ring,Real.rpow_sub_one hy'.ne',h₁,div_div,pow_two]
  have h₃ : y ^ (-q - 3) = y ^ (-q) / y ^ (3 : ℕ) := by
    rw [show -q - 3 = -q - 2 - 1 by ring,Real.rpow_sub_one hy'.ne',h₂,div_div,← pow_succ]
  have hXEq : 1 - X = (J * m) / y := by
    unfold X
    field_simp [hy'.ne']
    unfold y
    ring
  have hb : b / y = 2 * (1 - X) / m := by
    rw [hXEq]
    unfold b
    field_simp [hm'.ne',hy'.ne']
  dsimp only
  change weightedAffineResponse 1 1 (-2) 0 0 (J + 1) b q d = 2 * y ^ (-q) * (q - 1 - q * X) ∧
    weightedAffineResponse 2 1 (-2) 0 0 (J + 1) b q d =
      (4 * q / m) * y ^ (-q) * (1 - X) * (q - 1 - (q + 1) * X) ∧
    weightedAffineResponse 3 1 (-2) 0 0 (J + 1) b q d =
      (8 * q * (q + 1) / m ^ 2) * y ^ (-q) * (1 - X) ^ 2 * (q - 1 - (q + 2) * X)
  have hA : 1 + (-2 : ℝ) * d + 0 * d ^ 2 + 0 * d ^ 3 = m := by unfold m; ring
  refine ⟨?_,?_,?_⟩
  · change ((-2 : ℝ) + 2 * 0 * d + 3 * 0 * d ^ 2) * (J + 1 - b * d) ^ (-q) +
      (1 + (-2) * d + 0 * d ^ 2 + 0 * d ^ 3) * (b * q) * (J + 1 - b * d) ^ (-q - 1) = _
    rw [hEq,h₁,hA]
    calc
      _ = y ^ (-q) * (-2 + m * (b / y) * q) := by ring
      _ = _ := by rw [hb]; field_simp [hm'.ne']; ring
  · change (2 * 0 + 6 * 0 * d) * (J + 1 - b * d) ^ (-q) +
      2 * ((-2 : ℝ) + 2 * 0 * d + 3 * 0 * d ^ 2) * (b * q) * (J + 1 - b * d) ^ (-q - 1) +
      (1 + (-2) * d + 0 * d ^ 2 + 0 * d ^ 3) * (b ^ 2 * q * (q + 1)) * (J + 1 - b * d) ^ (-q - 2) = _
    rw [hEq,h₁,h₂,hA]
    calc
      _ = y ^ (-q) * (-4 * (b / y) * q + m * (b / y) ^ 2 * q * (q + 1)) := by rw [div_pow]; ring
      _ = _ := by rw [hb]; field_simp [hm'.ne']; ring
  · rw [weightedAffineResponse_third,hEq,h₁,h₂,h₃,hA]
    calc
      _ = y ^ (-q) * (-6 * (b / y) ^ 2 * q * (q + 1) +
          m * (b / y) ^ 3 * q * (q + 1) * (q + 2)) := by rw [div_pow,div_pow]; ring
      _ = _ := by rw [hb]; field_simp [hm'.ne']; ring

theorem lowerCentralResponse_third_pos {p J d : ℝ} (hp : 1 ≤ p) (hJ : 5 / 2 ≤ J)
    (hd : d ∈ Icc (0 : ℝ) (1 / 8)) {n : ℕ} (hn : 2 ≤ n) :
    0 < lowerCentralResponse 3 p J n d := by
  let q := p + 1 + (n : ℝ)
  let a := (n : ℝ) / ((n : ℝ) + 1)
  let m := 1 - 2 * d
  let y := J * m + 1
  let X := y⁻¹
  let D (k : ℕ) := weightedAffineResponse k 1 (-2) 0 0 (J + 1) (2 * J) q d
  have hm₀ : 3 / 4 ≤ m := by unfold m; linarith only [hd.2]
  have hm : 0 < m := (by norm_num : (0 : ℝ) < 3 / 4).trans_le hm₀
  have hm₁ : m ≤ 1 := by unfold m; linarith only [hd.1]
  have hY : 23 / 8 ≤ y := by
    unfold y
    have h := mul_le_mul hJ hm₀ (by norm_num : (0 : ℝ) ≤ 3 / 4) (show 0 ≤ J by linarith only [hJ])
    linarith only [h]
  have hy : 0 < y := (by norm_num : (0 : ℝ) < 23 / 8).trans_le hY
  have hX : 0 < X := inv_pos.mpr hy
  have hXU : X ≤ 8 / 23 := by
    unfold X
    rw [← one_div]
    apply (div_le_iff₀ hy).mpr
    linarith only [hY]
  have hJx : (1 - X) / m = J * X := by
    unfold X
    apply (div_eq_iff hm.ne').mpr
    field_simp [hy.ne']
    unfold y
    ring
  have hN : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hq : 4 ≤ q := by unfold q; linarith only [hp,hN]
  obtain ⟨hD₁,hD₂,hD₃⟩ := centralMass_responses q J d hm hy
  change D 1 = 2 * y ^ (-q) * (q - 1 - q * X) at hD₁
  change D 2 = (4 * q / m) * y ^ (-q) * (1 - X) * (q - 1 - (q + 1) * X) at hD₂
  change D 3 = (8 * q * (q + 1) / m ^ 2) * y ^ (-q) * (1 - X) ^ 2 * (q - 1 - (q + 2) * X) at hD₃
  have hE : 0 < q - 1 - (q + 1) * X := by
    nlinarith only [mul_nonneg (show 0 ≤ q - 4 by linarith only [hq])
      (show 0 ≤ 1 - X by linarith only [hXU]),hXU]
  have hq₀ : 0 < q := by linarith only [hq]
  have hX₁ : 0 < 1 - X := by linarith only [hXU]
  have hD₁p : 0 < D 1 := by
    rw [hD₁]
    exact mul_pos (by positivity) (by linarith only [hE,hX])
  have hD₂p : 0 < D 2 := by rw [hD₂]; positivity
  have hR : D 3 / D 2 = 2 * (q + 1) * ((1 - X) / m) *
      ((q - 1 - (q + 2) * X) / (q - 1 - (q + 1) * X)) := by
    rw [hD₃,hD₂]
    field_simp [hm.ne',hq₀.ne',hX₁.ne',hE.ne',(Real.rpow_pos_of_pos hy (-q)).ne']
    ring
  unfold lowerCentralResponse
  change 0 < if Even n then
    weightedAffineResponse 3 a (-(1 + 2 * a)) 2 0 (J + 1) (2 * J) q d
    else weightedAffineResponse 3 (13 / 25) (-(51 / 25)) (62 / 25) (-(24 / 25)) (J + 1) (2 * J) q d
  by_cases hEven : Even n
  · rw [if_pos hEven]
    have hA : 2 / 3 ≤ a := by
      unfold a
      exact (le_div_iff₀ (by positivity)).mpr (by linarith only [hN])
    have hc : 13 / 24 ≤ a - d := by linarith only [hA,hd.2]
    have hK := centralOddRatio_lower hq hX hXU hm hm₁ hJ hJx
    rw [← hR] at hK
    have hB := (le_div_iff₀ hD₂p).mp hK
    have hEq : weightedAffineResponse 3 a (-(1 + 2 * a)) 2 0 (J + 1) (2 * J) q d =
        (a - d) * D 3 - 3 * D 2 := by
      unfold D
      simp only [weightedAffineResponse_third,weightedAffineResponse_second]
      ring
    rw [hEq]
    have hLower := mul_le_mul hc hB (mul_nonneg (by norm_num) hD₂p.le)
      (show 0 ≤ a - d by linarith only [hc])
    nlinarith only [hLower,hD₂p]
  · rw [if_neg hEven]
    have hn₃ : 3 ≤ n := by
      by_contra! h
      have hn₂ : n = 2 := by omega
      exact hEven (hn₂ ▸ (by decide : Even 2))
    have hN₃ : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn₃
    have hq₅ : 5 ≤ q := by unfold q; linarith only [hp,hN₃]
    have hK := centralEvenRatio_lower hq₅ hX hXU hm hm₁ hJ hJx
    rw [← hR] at hK
    have hB := (le_div_iff₀ hD₂p).mp hK
    let c := 13 / 25 - d + (12 / 25) * d ^ 2
    have hc : 161 / 400 ≤ c := by
      unfold c
      nlinarith only [hd.2,mul_nonneg (show 0 ≤ 1 / 8 - d by linarith only [hd.2])
        (show 0 ≤ 47 / 50 - 12 / 25 * d by linarith only [hd.2])]
    have hEq : weightedAffineResponse 3 (13 / 25) (-(51 / 25)) (62 / 25) (-(24 / 25)) (J + 1) (2 * J) q d =
        c * D 3 + 3 * (-1 + 24 / 25 * d) * D 2 + (72 / 25) * D 1 := by
      unfold c D
      simp only [weightedAffineResponse_third,weightedAffineResponse_second,weightedAffineResponse_first]
      ring
    rw [hEq]
    have hLower := mul_le_mul hc hB (mul_nonneg (by norm_num) hD₂p.le)
      (show 0 ≤ c by linarith only [hc])
    nlinarith only [hLower,hD₂p,hD₁p,mul_nonneg hd.1 hD₂p.le]

end ACS12.GammaMeasure


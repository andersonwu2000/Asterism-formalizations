import ACS12.JointLowerCentralDomination

/-! Exact normalized retained base tail from the central expansion. -/
namespace ACS12.GammaMeasure

open Set

noncomputable def lowerBaseThird (p j δ : ℝ) : ℝ :=
  lowerCentralWeight p 0 * lowerCentralResponse 3 p (j + 1 / 2) 0 δ +
    lowerCentralWeight p 1 * lowerCentralResponse 3 p (j + 1 / 2) 1 δ

noncomputable def lowerBaseCoeff (k : Fin 5) (p h : ℝ) : ℝ :=
  let l := 1 + 2 * h
  let B := 13 / 25 + 27 / 25 * h + 14 / 25 * h ^ 2
  let d := 1 + 26 / 25 * h
  match k.val with
  | 0 => -8 * h * p * (p + 2) - 12 * p
  | 1 => (24 * h * (p + 2) * (p + 1) + 24 * (p + 1)) * l +
      (p + 1) * (4 * B * (p + 2) * (p + 3) - 6 * d * (p + 2) + 72 / 25)
  | 2 => -(24 * h * (p + 2) ^ 2 + 12 * (p + 2)) * l ^ 2 +
      (-12 * B * (p + 2) ^ 2 * (p + 3) + 12 * d * (p + 2) ^ 2 - 72 / 25 * (p + 2)) * l
  | 3 => 8 * h * (p + 2) * (p + 3) * l ^ 3 +
      (12 * B * (p + 2) * (p + 3) ^ 2 - 6 * d * (p + 2) * (p + 3)) * l ^ 2
  | _ => -4 * B * (p + 2) * (p + 3) * (p + 4) * l ^ 3

private theorem lowerBase_polynomial_eq (p h Y W : ℝ) (hY : 0 < Y) :
    let J := Y - (1 + 2 * h)
    let B := 13 / 25 + 27 / 25 * h + 14 / 25 * h ^ 2
    let d := 1 + 26 / 25 * h
    24 * J * (W / Y ^ (0 + 1 : ℕ)) + 12 * (2 * h - 1) * J ^ 2 * (p + 2) * (W / Y ^ (1 + 1 : ℕ)) -
      8 * h * J ^ 3 * (p + 2) * (p + 3) * (W / Y ^ (2 + 1 : ℕ)) -
      (72 / 25) * (W / Y ^ (0 + 1 : ℕ)) +
      3 * (24 / 25 + 4 * d) * J * (p + 2) * (W / Y ^ (1 + 1 : ℕ)) -
      6 * (d + 2 * B) * J ^ 2 * (p + 2) * (p + 3) * (W / Y ^ (2 + 1 : ℕ)) +
      4 * B * J ^ 3 * (p + 2) * (p + 3) * (p + 4) * (W / Y ^ (3 + 1 : ℕ)) =
      ∑ k : Fin 5, lowerBaseCoeff k p h * (W / Y ^ k.val) := by
  norm_num [Fin.sum_univ_succ,Fin.val_succ,lowerBaseCoeff]
  field_simp [hY.ne']
  ring

theorem lowerBaseThird_eq {p j δ : ℝ} (hp : 1 ≤ p) (hj : 2 ≤ j) (hδ : δ < 1 / 2) :
    let m := 1 - 2 * δ
    let h := δ / m
    let Y := j + 3 / 2 + 2 * h
    m ^ (p + 2) / (p * (p + 1)) * lowerBaseThird p j δ =
      ∑ k : Fin 5, lowerBaseCoeff k p h * Y ^ (-p - 1 - (k.val : ℝ)) := by
  let m := 1 - 2 * δ
  let h := δ / m
  let l := 1 + 2 * h
  let J := j + 1 / 2
  let y := J + 1 - 2 * J * δ
  let Y := J + l
  let B := 13 / 25 + 27 / 25 * h + 14 / 25 * h ^ 2
  let d := 1 + 26 / 25 * h
  have hp₀ := zero_lt_one.trans_le hp
  have hm : 0 < m := by unfold m; linarith only [hδ]
  have hJ : 0 < J := by unfold J; linarith only [hj]
  have hL : l = 1 / m := by unfold l h; field_simp [hm.ne']; unfold m; ring
  have hl : 0 < l := hL.symm ▸ one_div_pos.mpr hm
  have hY : 0 < Y := add_pos hJ hl
  have hM : y = m * Y := by
    unfold Y
    rw [hL,mul_add,mul_one_div_cancel hm.ne']
    unfold y m
    ring
  have hy : 0 < y := hM ▸ mul_pos hm hY
  have hN (k : ℕ) : m ^ (p + 2) * y ^ (-p - 2 - (k : ℝ)) =
      (m ^ k)⁻¹ * Y ^ (-p - 2 - (k : ℝ)) := by
    rw [hM,Real.mul_rpow hm.le hY.le,← mul_assoc,← Real.rpow_add hm,
      show p + 2 + (-p - 2 - (k : ℝ)) = -(k : ℝ) by ring,Real.rpow_neg hm.le,Real.rpow_natCast]
  have hδE : δ = m * h := by unfold h; field_simp [hm.ne']
  have hb : 13 / 25 - δ + (12 / 25) * δ ^ 2 = m ^ 2 * B := by
    unfold B h
    field_simp [hm.ne']
    unfold m
    ring
  have hb' : -1 + (24 / 25) * δ = -m * d := by
    unfold d h
    field_simp [hm.ne']
    unfold m
    ring
  have hP₀ : lowerCentralWeight p 0 = p := by simp [lowerCentralWeight]
  have hP₁ : lowerCentralWeight p 1 = p * (p + 1) / 2 := by
    simp [lowerCentralWeight]
  have hR₀ : lowerCentralResponse 3 p J 0 δ =
      24 * J * (p + 1) * y ^ (-p - 2) +
      12 * (4 * δ - 1) * J ^ 2 * (p + 1) * (p + 2) * y ^ (-p - 3) -
      δ * m * 8 * J ^ 3 * (p + 1) * (p + 2) * (p + 3) * y ^ (-p - 4) := by
    unfold lowerCentralResponse
    simp only [show Even (0 : ℕ) by decide,if_true,Nat.cast_zero,zero_div,mul_zero,add_zero]
    rw [weightedAffineResponse_third]
    change _ = _
    unfold y m
    simp only [mul_zero,zero_mul,add_zero,zero_add]
    rw [show -(p + 1) - 1 = -p - 2 by ring,
      show -(p + 1) - 2 = -p - 3 by ring,show -(p + 1) - 3 = -p - 4 by ring]
    ring
  have hR₁ : lowerCentralResponse 3 p J 1 δ =
      -(144 / 25) * y ^ (-p - 2) +
      6 * m * (24 / 25 + 4 * d) * J * (p + 2) * y ^ (-p - 3) -
      12 * m ^ 2 * (d + 2 * B) * J ^ 2 * (p + 2) * (p + 3) * y ^ (-p - 4) +
      8 * m ^ 3 * B * J ^ 3 * (p + 2) * (p + 3) * (p + 4) * y ^ (-p - 5) := by
    unfold lowerCentralResponse
    simp only [show ¬ Even (1 : ℕ) by decide,if_false,Nat.cast_one]
    rw [weightedAffineResponse_third]
    have h₀ : 13 / 25 + -(51 / 25) * δ + (62 / 25) * δ ^ 2 + -(24 / 25) * δ ^ 3 = m ^ 3 * B := by
      rw [show m ^ 3 * B = m * (m ^ 2 * B) by ring,← hb]
      unfold m
      ring
    have h₁ : -(51 / 25) + 2 * (62 / 25) * δ + 3 * (-(24 / 25)) * δ ^ 2 =
        -m ^ 2 * (d + 2 * B) := by
      calc
        _ = m * (-1 + (24 / 25) * δ) - 2 * (13 / 25 - δ + (12 / 25) * δ ^ 2) := by unfold m; ring
        _ = _ := by rw [hb,hb']; ring
    have h₂ : 2 * (62 / 25) + 6 * (-(24 / 25)) * δ = m * (24 / 25 + 4 * d) := by
      calc
        _ = m * (24 / 25) - 4 * (-1 + (24 / 25) * δ) := by unfold m; ring
        _ = _ := by rw [hb']; ring
    rw [h₀,h₁,h₂,show -(p + 1 + 1) = -p - 2 by ring,
      show -p - 2 - 1 = -p - 3 by ring,show -p - 2 - 2 = -p - 4 by ring,
      show -p - 2 - 3 = -p - 5 by ring]
    unfold y
    ring
  change m ^ (p + 2) / (p * (p + 1)) * lowerBaseThird p j δ = _
  have hYE : j + 3 / 2 + 2 * h = Y := by unfold Y J l; ring
  rw [hYE]
  unfold lowerBaseThird
  rw [hP₀,hP₁]
  change m ^ (p + 2) / (p * (p + 1)) *
    (p * lowerCentralResponse 3 p J 0 δ + p * (p + 1) / 2 * lowerCentralResponse 3 p J 1 δ) = _
  rw [hR₀,hR₁]
  let M := m ^ (p + 2)
  let R (k : ℕ) := y ^ (-p - 2 - (k : ℝ))
  let S (k : ℕ) := Y ^ (-p - 2 - (k : ℝ))
  have hU (k : ℕ) : M * R k = (m ^ k)⁻¹ * S k := hN k
  have hM₀ : M * y ^ (-p - 2) = S 0 := by simpa only [R,Nat.cast_zero,sub_zero,pow_zero,inv_one,one_mul] using hU 0
  have hM₁ : M * y ^ (-p - 3) = m⁻¹ * S 1 := by
    simpa only [R,Nat.cast_one,pow_one,show -p - 2 - 1 = -p - 3 by ring] using hU 1
  have hM₂ : M * y ^ (-p - 4) = (m ^ 2)⁻¹ * S 2 := by
    simpa only [R,Nat.cast_ofNat,show -p - 2 - 2 = -p - 4 by ring] using hU 2
  have hM₃ : M * y ^ (-p - 5) = (m ^ 3)⁻¹ * S 3 := by
    simpa only [R,Nat.cast_ofNat,show -p - 2 - 3 = -p - 5 by ring] using hU 3
  have hNorm :
      m ^ (p + 2) / (p * (p + 1)) *
      (p * (24 * J * (p + 1) * y ^ (-p - 2) +
        12 * (4 * δ - 1) * J ^ 2 * (p + 1) * (p + 2) * y ^ (-p - 3) -
        δ * m * 8 * J ^ 3 * (p + 1) * (p + 2) * (p + 3) * y ^ (-p - 4)) +
        p * (p + 1) / 2 * (-(144 / 25) * y ^ (-p - 2) +
        6 * m * (24 / 25 + 4 * d) * J * (p + 2) * y ^ (-p - 3) -
        12 * m ^ 2 * (d + 2 * B) * J ^ 2 * (p + 2) * (p + 3) * y ^ (-p - 4) +
        8 * m ^ 3 * B * J ^ 3 * (p + 2) * (p + 3) * (p + 4) * y ^ (-p - 5))) =
      24 * J * S 0 + 12 * (2 * h - 1) * J ^ 2 * (p + 2) * S 1 -
        8 * h * J ^ 3 * (p + 2) * (p + 3) * S 2 -
        (72 / 25) * S 0 + 3 * (24 / 25 + 4 * d) * J * (p + 2) * S 1 -
        6 * (d + 2 * B) * J ^ 2 * (p + 2) * (p + 3) * S 2 +
        4 * B * J ^ 3 * (p + 2) * (p + 3) * (p + 4) * S 3 := by
    let c₀ := 24 * J - 72 / 25
    let c₁ := 12 * (4 * δ - 1) * J ^ 2 * (p + 2) + 3 * m * (24 / 25 + 4 * d) * J * (p + 2)
    let c₂ := -8 * δ * m * J ^ 3 * (p + 2) * (p + 3) - 6 * m ^ 2 * (d + 2 * B) * J ^ 2 * (p + 2) * (p + 3)
    let c₃ := 4 * m ^ 3 * B * J ^ 3 * (p + 2) * (p + 3) * (p + 4)
    have hGroup : m ^ (p + 2) / (p * (p + 1)) *
        (p * (24 * J * (p + 1) * y ^ (-p - 2) +
          12 * (4 * δ - 1) * J ^ 2 * (p + 1) * (p + 2) * y ^ (-p - 3) -
          δ * m * 8 * J ^ 3 * (p + 1) * (p + 2) * (p + 3) * y ^ (-p - 4)) +
          p * (p + 1) / 2 * (-(144 / 25) * y ^ (-p - 2) +
          6 * m * (24 / 25 + 4 * d) * J * (p + 2) * y ^ (-p - 3) -
          12 * m ^ 2 * (d + 2 * B) * J ^ 2 * (p + 2) * (p + 3) * y ^ (-p - 4) +
          8 * m ^ 3 * B * J ^ 3 * (p + 2) * (p + 3) * (p + 4) * y ^ (-p - 5))) =
        c₀ * (M * y ^ (-p - 2)) + c₁ * (M * y ^ (-p - 3)) +
          c₂ * (M * y ^ (-p - 4)) + c₃ * (M * y ^ (-p - 5)) := by
      unfold c₀ c₁ c₂ c₃ M
      field_simp [hp₀.ne',(show 0 < p + 1 by positivity).ne']
      ring
    rw [hGroup,hM₀,hM₁,hM₂,hM₃]
    simp only [← inv_pow]
    have hNorm₁ : c₁ * m⁻¹ = 12 * (2 * h - 1) * J ^ 2 * (p + 2) +
        3 * (24 / 25 + 4 * d) * J * (p + 2) := by
      unfold c₁ h
      field_simp [hm.ne']
      unfold m
      ring
    have hNorm₂ : c₂ * m⁻¹ ^ 2 = -8 * h * J ^ 3 * (p + 2) * (p + 3) -
        6 * (d + 2 * B) * J ^ 2 * (p + 2) * (p + 3) := by
      unfold c₂ h
      field_simp [hm.ne']
    have hNorm₃ : c₃ * m⁻¹ ^ 3 = 4 * B * J ^ 3 * (p + 2) * (p + 3) * (p + 4) := by
      unfold c₃
      field_simp [hm.ne']
    change c₀ * S 0 + c₁ * (m⁻¹ * S 1) + c₂ * (m⁻¹ ^ 2 * S 2) + c₃ * (m⁻¹ ^ 3 * S 3) = _
    rw [← mul_assoc c₁,← mul_assoc c₂,← mul_assoc c₃,hNorm₁,hNorm₂,hNorm₃]
    unfold c₀
    ring
  rw [hNorm]
  have hSY (k : ℕ) : S k = Y ^ (-p - 1) / Y ^ (k + 1) := by
    unfold S
    rw [show -p - 2 - (k : ℝ) = -p - 1 - ((k + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_sub_natCast hY.ne']
  simp only [hSY]
  have hTerm (k : Fin 5) : Y ^ (-p - 1 - (k.val : ℝ)) = Y ^ (-p - 1) / Y ^ k.val :=
    Real.rpow_sub_natCast hY.ne' _ _
  simp_rw [hTerm]
  rw [show J = Y - (1 + 2 * h) by unfold Y l; ring]
  exact lowerBase_polynomial_eq p h Y (Y ^ (-p - 1)) hY

end ACS12.GammaMeasure


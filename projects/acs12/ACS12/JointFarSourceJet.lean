import ACS12.JointFarMotion

/-! Exponent derivatives of the two licensed complete source envelopes. -/
namespace ACS12.GammaMeasure

noncomputable def farM2Jet (k : ℕ) (p : ℝ) : ℝ :=
  match k with
  | 0 => pureQ p - p * (p + 1)
  | 1 => pureQPrime p - (2 * p + 1)
  | _ => pureQSecond p - 2

theorem farM2Jet_deriv {k : ℕ} (hk : k < 2) {p : ℝ} (hp : 0 < p) :
    HasDerivAt (farM2Jet k) (farM2Jet (k + 1) p) p := by
  have h := hasDerivAt_id p
  have hp' : -1 < p := by linarith only [hp]
  interval_cases k
  · convert (pureQ_derivative hp').sub (h.mul (h.add_const 1)) using 1
    simp only [farM2Jet,id_eq,mul_one,one_mul]
    ring
  · simpa only [farM2Jet,id_eq,mul_one] using
      (pureQPrime_derivative hp').sub (((hasDerivAt_id p).const_mul 2).add_const 1)

noncomputable def farM3Jet (k : ℕ) (p : ℝ) : ℝ :=
  let T := p * (p + 1) * (p + 2)
  let T' := 3 * p ^ 2 + 6 * p + 2
  let T'' := 6 * p + 6
  let L (j : ℕ) := powerLogTail (p + 3) j 2
  match k with
  | 0 => T * L 0
  | 1 => T' * L 0 - T * L 1
  | _ => T'' * L 0 - 2 * T' * L 1 + T * L 2

theorem farM3Jet_deriv {k : ℕ} (hk : k < 2) {p : ℝ} (hp : 0 < p) :
    HasDerivAt (farM3Jet k) (farM3Jet (k + 1) p) p := by
  have h := hasDerivAt_id p
  have hT := (h.mul (h.add_const 1)).mul (h.add_const 2)
  have hT' := ((((h.pow 2).const_mul 3).add (h.const_mul 6))).add_const 2
  have hL (j : ℕ) := (powerLogTail_hasDerivAt (show 1 < p + 3 by linarith only [hp]) j 2 (by decide)).comp p
    (h.add_const 3)
  interval_cases k
  · convert hT.mul (hL 0) using 1
    simp only [farM3Jet,Function.comp_apply,id_eq,Pi.mul_apply,mul_one,one_mul,zero_add]
    ring
  · convert (hT'.mul (hL 0)).sub (hT.mul (hL 1)) using 1
    simp only [farM3Jet,Function.comp_apply,id_eq,Pi.mul_apply,Pi.pow_apply,Pi.add_apply,mul_one,one_mul,zero_add]
    ring

theorem farM3Jet_zero {p : ℝ} (hp : 0 < p) : farM3Jet 0 p = pureR p - p * (p + 1) * (p + 2) := by
  change p * (p + 1) * (p + 2) * powerLogTail (p + 3) 0 2 = _
  unfold pureR
  rw [powerLogTail_zero,powerTail_shift (show 1 < p + 3 by linarith only [hp]) 1]
  simp only [Nat.cast_one,Real.one_rpow]
  ring

private noncomputable def productJet (f g : ℕ → ℝ → ℝ) (k : ℕ) (p : ℝ) : ℝ :=
  match k with
  | 0 => f 0 p * g 0 p
  | 1 => f 1 p * g 0 p + f 0 p * g 1 p
  | _ => f 2 p * g 0 p + 2 * f 1 p * g 1 p + f 0 p * g 2 p

private theorem productJet_deriv {f g : ℕ → ℝ → ℝ} {k : ℕ} (hk : k < 2) {p : ℝ}
    (hf : ∀ i < 2, HasDerivAt (f i) (f (i + 1) p) p)
    (hg : ∀ i < 2, HasDerivAt (g i) (g (i + 1) p) p) :
    HasDerivAt (productJet f g k) (productJet f g (k + 1) p) p := by
  interval_cases k
  · exact (hf 0 (by decide)).mul (hg 0 (by decide))
  · convert (((hf 1 (by decide)).mul (hg 0 (by decide))).add
      ((hf 0 (by decide)).mul (hg 1 (by decide)))) using 1
    unfold productJet
    ring

private noncomputable def farAdjacentLeftJet (k : ℕ) (p : ℝ) : ℝ :=
  (match k with
    | 0 => p + 1 - pureZ p + 1063 / 1296000
    | 1 => 1 - pureZPrime p
    | _ => -pureZSecond p) + 13 * farM2Jet k p / 72 - farM3Jet k p / 72

private theorem farAdjacentLeftJet_deriv {k : ℕ} (hk : k < 2) {p : ℝ} (hp : 0 < p) :
    HasDerivAt (farAdjacentLeftJet k) (farAdjacentLeftJet (k + 1) p) p := by
  have hM := ((farM2Jet_deriv hk hp).const_mul 13).div_const 72
  have hR := (farM3Jet_deriv hk hp).div_const 72
  interval_cases k
  · exact ((((hasDerivAt_id p).add_const 1).sub (pureZ_derivative hp)).add_const _).add hM |>.sub hR
  · exact ((pureZPrime_derivative hp).const_sub 1).add hM |>.sub hR

private noncomputable def farAdjacentRightJet (k : ℕ) (p : ℝ) : ℝ :=
  (match k with
    | 0 => pureZ p - 1 - p / 8 + farPolyPower 0 (-3 / 4) (1 / 8) (7 / 8) p + 1 / 2048
    | 1 => pureZPrime p - 1 / 8 + farPolyPowerD 0 (-3 / 4) (1 / 8) (7 / 8) p
    | _ => pureZSecond p + farPolyPowerDD 0 (-3 / 4) (1 / 8) (7 / 8) p) + farM2Jet k p / 128

private theorem farAdjacentRightJet_deriv {k : ℕ} (hk : k < 2) {p : ℝ} (hp : 0 < p) :
    HasDerivAt (farAdjacentRightJet k) (farAdjacentRightJet (k + 1) p) p := by
  have hM := (farM2Jet_deriv hk hp).div_const 128
  interval_cases k
  · exact (((((pureZ_derivative hp).sub_const 1).sub ((hasDerivAt_id p).div_const 8)).add
      (farPolyPower_deriv 0 (-3 / 4) (1 / 8) (by norm_num : (0 : ℝ) < 7 / 8))).add_const _).add hM
  · exact (((pureZPrime_derivative hp).sub_const (1 / 8)).add
      (farPolyPowerD_deriv 0 (-3 / 4) (1 / 8) (by norm_num : (0 : ℝ) < 7 / 8))).add hM

noncomputable def farAdjacentJet (k : ℕ) (p : ℝ) : ℝ :=
  productJet (fun j q => farPowerJet j (3 / 4) (q - 1)) farAdjacentLeftJet k p +
    farAdjacentRightJet k p

theorem farAdjacentJet_deriv {k : ℕ} (hk : k < 2) {p : ℝ} (hp : 0 < p) :
    HasDerivAt (farAdjacentJet k) (farAdjacentJet (k + 1) p) p := by
  have hF (j : ℕ) (_ : j < 2) : HasDerivAt (fun q => farPowerJet j (3 / 4) (q - 1))
      (farPowerJet (j + 1) (3 / 4) (p - 1)) p := by
    simpa only [Function.comp_apply,mul_one] using
      (farPowerJet_deriv (p := p - 1) (by norm_num : (0 : ℝ) < 3 / 4) j).comp p
        ((hasDerivAt_id p).sub_const 1)
  exact (productJet_deriv hk hF (fun _ hj => farAdjacentLeftJet_deriv hj hp)).add
    (farAdjacentRightJet_deriv hk hp)

theorem farAdjacentJet_zero {p : ℝ} (hp : 0 < p) : farAdjacentJet 0 p = jointFarAdjacent p := by
  unfold farAdjacentJet productJet farAdjacentLeftJet farAdjacentRightJet farPolyPower farPowerJet
  rw [farM3Jet_zero hp]
  unfold jointFarAdjacent
  change _ =
    (4 / 3 : ℝ) ^ (p - 1) * (p + 1 - pureZ p + 13 * (pureQ p - p * (p + 1)) / 72 -
      (pureR p - p * (p + 1) * (p + 2)) / 72 + 1063 / 1296000) +
    pureZ p - 1 - p / 8 + (1 / 8 - 3 * p / 4) * (8 / 7 : ℝ) ^ p +
    (pureQ p - p * (p + 1)) / 128 + 1 / 2048
  have hs : (4 / 3 : ℝ) ^ (p - 1) = (3 / 4 : ℝ) ^ (-(p - 1)) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3 / 4),← Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 3 / 4),show (3 / 4 : ℝ)⁻¹ = 4 / 3 by norm_num]
  have hr : (8 / 7 : ℝ) ^ p = (7 / 8 : ℝ) ^ (-p) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 7 / 8),← Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 7 / 8),show (7 / 8 : ℝ)⁻¹ = 8 / 7 by norm_num]
  rw [hs,hr]
  simp only [farM2Jet,pow_zero,one_mul]
  ring

theorem farAdjacentJet_second (p : ℝ) :
    farAdjacentJet 2 p =
      let L := -Real.log (3 / 4)
      let s := (3 / 4 : ℝ) ^ (-(p - 1))
      let z := pureZSecond p
      (1 - s) * z + 2 * L * s * (1 - pureZPrime p) + s * L ^ 2 * (p + 1 - pureZ p + 1063 / 1296000) +
        (13 * s / 72 + 1 / 128) * farM2Jet 2 p + (26 * s * L / 72) * farM2Jet 1 p +
        (13 * s * L ^ 2 / 72) * farM2Jet 0 p -
        (s / 72) * (farM3Jet 2 p + 2 * L * farM3Jet 1 p + L ^ 2 * farM3Jet 0 p) +
        farPolyPowerDD 0 (-3 / 4) (1 / 8) (7 / 8) p := by
  unfold farAdjacentJet productJet farAdjacentLeftJet farAdjacentRightJet farPowerJet
  ring

private noncomputable def farFourthLeftJet (k : ℕ) (p : ℝ) : ℝ :=
  match k with
  | 0 => 1 + pureP p
  | 1 => purePPrime p
  | _ => purePSecond p

private theorem farFourthLeftJet_deriv {k : ℕ} (hk : k < 2) {p : ℝ} (hp : 0 < p) :
    HasDerivAt (farFourthLeftJet k) (farFourthLeftJet (k + 1) p) p := by
  interval_cases k
  · exact (pureP_derivative hp).const_add 1
  · exact purePPrime_derivative hp

noncomputable def farFourthRightJet (k : ℕ) (p : ℝ) : ℝ :=
  (match k with
  | 0 => 2 * p + pureP p - pureQ p
  | 1 => 2 + purePPrime p - pureQPrime p
  | _ => purePSecond p - pureQSecond p) + farPowerJet k 2 p

theorem farFourthRightJet_deriv {k : ℕ} (hk : k < 2) {p : ℝ} (hp : 0 < p) :
    HasDerivAt (farFourthRightJet k) (farFourthRightJet (k + 1) p) p := by
  have hp' : -1 < p := by linarith only [hp]
  have hE := farPowerJet_deriv (p := p) (by norm_num : (0 : ℝ) < 2) k
  interval_cases k
  · simpa only [farFourthRightJet,mul_one] using
      ((((hasDerivAt_id p).const_mul 2).add (pureP_derivative hp)).sub (pureQ_derivative hp')).add hE
  · exact (((purePPrime_derivative hp).const_add 2).sub (pureQPrime_derivative hp')).add hE

noncomputable def farFourthJet (k : ℕ) (p : ℝ) : ℝ :=
  -(9 / 128) * (productJet (fun j q => farPowerJet j (13 / 16) (q + 2)) farFourthLeftJet k p +
    productJet (fun j q => farPowerJet j (15 / 16) (q + 2)) farFourthRightJet k p)

theorem farFourthJet_deriv {k : ℕ} (hk : k < 2) {p : ℝ} (hp : 0 < p) :
    HasDerivAt (farFourthJet k) (farFourthJet (k + 1) p) p := by
  have hF (x : ℝ) (hx : 0 < x) (j : ℕ) (_ : j < 2) :
      HasDerivAt (fun q => farPowerJet j x (q + 2)) (farPowerJet (j + 1) x (p + 2)) p := by
    simpa only [Function.comp_apply,mul_one] using
      (farPowerJet_deriv (p := p + 2) hx j).comp p ((hasDerivAt_id p).add_const 2)
  exact ((productJet_deriv hk (hF _ (by norm_num : (0 : ℝ) < 13 / 16))
    (fun _ hj => farFourthLeftJet_deriv hj hp)).add
    (productJet_deriv hk (hF _ (by norm_num : (0 : ℝ) < 15 / 16))
      (fun _ hj => farFourthRightJet_deriv hj hp))).const_mul _

theorem farFourthJet_zero (p : ℝ) : farFourthJet 0 p = jointFarFourth p := by
  unfold farFourthJet productJet farFourthLeftJet farFourthRightJet farPowerJet jointFarFourth
  simp only [pow_zero,one_mul,neg_add_rev]
  rw [show -(2 : ℝ) + -p = -p - 2 by ring]
  ring

theorem farFourthJet_second (p : ℝ) :
    farFourthJet 2 p =
      -(9 / 128) * ((13 / 16 : ℝ) ^ (-(p + 2)) * (purePSecond p +
        2 * (-Real.log (13 / 16)) * purePPrime p + (Real.log (13 / 16)) ^ 2 * (1 + pureP p)) +
        (15 / 16 : ℝ) ^ (-(p + 2)) * (farFourthRightJet 2 p +
          2 * (-Real.log (15 / 16)) * farFourthRightJet 1 p + (Real.log (15 / 16)) ^ 2 * farFourthRightJet 0 p)) := by
  unfold farFourthJet productJet farFourthLeftJet farPowerJet
  ring

end ACS12.GammaMeasure

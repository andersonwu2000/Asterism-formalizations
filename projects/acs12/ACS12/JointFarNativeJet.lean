import ACS12.JointFarMotion

/-! The full second exponent derivative of the far native value. -/
namespace ACS12.GammaMeasure

private noncomputable def farPolyJet (k : ℕ) (a b c x p : ℝ) : ℝ :=
  match k with
  | 0 => farPolyPower a b c x p
  | 1 => farPolyPowerD a b c x p
  | _ => farPolyPowerDD a b c x p

private theorem farPolyJet_deriv {k : ℕ} (hk : k < 2) (a b c : ℝ) {x p : ℝ} (hx : 0 < x) :
    HasDerivAt (farPolyJet k a b c x) (farPolyJet (k + 1) a b c x p) p := by
  interval_cases k
  · exact farPolyPower_deriv a b c hx
  · exact farPolyPowerD_deriv a b c hx

private noncomputable def farNativeBaseJet (k : ℕ) (p : ℝ) : ℝ :=
  match k with
  | 0 => (7 / 8) * (1 + (189 / 800) * p - pureZ p)
  | 1 => (7 / 8) * (189 / 800 - pureZPrime p)
  | _ => -(7 / 8) * pureZSecond p

private theorem farNativeBaseJet_deriv {k : ℕ} (hk : k < 2) {p : ℝ} (hp : 0 < p) :
    HasDerivAt (farNativeBaseJet k) (farNativeBaseJet (k + 1) p) p := by
  interval_cases k
  · simpa only [farNativeBaseJet,mul_one] using
      ((((hasDerivAt_id p).const_mul (189 / 800)).const_add 1).sub (pureZ_derivative hp)).const_mul (7 / 8)
  · convert ((pureZPrime_derivative hp).const_sub (189 / 800)).const_mul (7 / 8) using 1
    change -(7 / 8 : ℝ) * pureZSecond p = (7 / 8) * (-pureZSecond p)
    ring

noncomputable def farNativeJet (k : ℕ) (p : ℝ) : ℝ :=
  let ax : ℝ := (511 / 800) / (13 / 8) ^ 2
  let ay : ℝ := (189 / 800) / (21 / 8) ^ 2
  farNativeBaseJet k p +
    (3 / 4) * (farPolyJet k 0 (73 / 100) (-1) (7 / 8) p + farPolyJet k 0 (63 / 500) 1 (15 / 8) p) +
    ((511 / 800) * farPowerJet k (13 / 8) p + (189 / 800) * farPowerJet k (21 / 8) p - farIntegralJet k p) +
    (3 / 8) * (farPolyJet k 0 (511 / 1300) (-1) (13 / 8) p + farPolyJet k 0 (9 / 100) 1 (21 / 8) p) +
    (3 / 64) * (farPolyJet k ax (ax - 8 / 13) 0 (13 / 8) p +
      farPolyJet k ay (ay + 8 / 21) 0 (21 / 8) p)

theorem farNativeJet_zero (p : ℝ) : farNativeJet 0 p = jointFarNative p := by
  unfold farNativeJet farNativeBaseJet farPolyJet farPolyPower jointFarNative farG farGx farGIntegral
  rw [farIntegralJet_zero]
  norm_num [farPowerJet]
  ring

theorem farNativeJet_deriv {k : ℕ} (hk : k < 2) {p : ℝ} (hp : 0 < p) :
    HasDerivAt (farNativeJet k) (farNativeJet (k + 1) p) p := by
  let ax : ℝ := (511 / 800) / (13 / 8) ^ 2
  let ay : ℝ := (189 / 800) / (21 / 8) ^ 2
  have hB := farNativeBaseJet_deriv hk hp
  have hU := ((farPolyJet_deriv (p := p) hk 0 (73 / 100) (-1) (by norm_num : (0 : ℝ) < 7 / 8)).add
    (farPolyJet_deriv (p := p) hk 0 (63 / 500) 1 (by norm_num : (0 : ℝ) < 15 / 8))).const_mul (3 / 4)
  have hI := (((farPowerJet_deriv (p := p) (by norm_num : (0 : ℝ) < 13 / 8) k).const_mul (511 / 800)).add
    ((farPowerJet_deriv (p := p) (by norm_num : (0 : ℝ) < 21 / 8) k).const_mul (189 / 800))).sub
      (farIntegralJet_deriv hp k)
  have hX := ((farPolyJet_deriv (p := p) hk 0 (511 / 1300) (-1) (by norm_num : (0 : ℝ) < 13 / 8)).add
    (farPolyJet_deriv (p := p) hk 0 (9 / 100) 1 (by norm_num : (0 : ℝ) < 21 / 8))).const_mul (3 / 8)
  have hD := ((farPolyJet_deriv (p := p) hk ax (ax - 8 / 13) 0 (by norm_num : (0 : ℝ) < 13 / 8)).add
    (farPolyJet_deriv (p := p) hk ay (ay + 8 / 21) 0 (by norm_num : (0 : ℝ) < 21 / 8))).const_mul (3 / 64)
  exact ((((hB.add hU).add hI).add hX).add hD)

theorem farNativeJet_second (p : ℝ) :
    farNativeJet 2 p =
      -(7 / 8) * pureZSecond p +
      (3 / 4) * (farPolyPowerDD 0 (73 / 100) (-1) (7 / 8) p + farPolyPowerDD 0 (63 / 500) 1 (15 / 8) p) +
      ((511 / 800) * farPowerJet 2 (13 / 8) p + (189 / 800) * farPowerJet 2 (21 / 8) p - farIntegralJet 2 p) +
      (3 / 8) * (farPolyPowerDD 0 (511 / 1300) (-1) (13 / 8) p + farPolyPowerDD 0 (9 / 100) 1 (21 / 8) p) +
      (3 / 64) * (farPolyPowerDD (1022 / 4225) (1022 / 4225 - 8 / 13) 0 (13 / 8) p +
        farPolyPowerDD (6 / 175) (6 / 175 + 8 / 21) 0 (21 / 8) p) := by
  unfold farNativeJet farNativeBaseJet farPolyJet
  norm_num

end ACS12.GammaMeasure

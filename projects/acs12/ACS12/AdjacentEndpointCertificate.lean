import ACS12.EndpointBinomial
import ACS12.EndpointBernstein
import ACS12.PureAdjacentPrimitiveFloor
import ACS12.PureAdjacentEndpointMass
import ACS12.PureAdjacentValueData

/-! Whole-interval certificates for the adjacent power-kernel endpoint. -/
namespace ACS12.GammaMeasure

open Set CenteredCircle.AllN
noncomputable section
set_option maxHeartbeats 8000000

private def endpointCubic (u : ℝ) : ℝ := (2304 / 8575) * u ^ 3 + (5 / 7) * u

private theorem endpointCubic_eq (u : ℝ) : endpointCubic u = upperCapMass u := by
  unfold endpointCubic upperCapMass
  ring

private def endpointPosition (j u : ℝ) : ℝ := u + j * endpointCubic u

private theorem endpointPosition_mono {j : ℝ} (hj : 0 ≤ j) :
    MonotoneOn (endpointPosition j) (Ici 0) := by
  intro u hu v _ huv
  have hu₀ : 0 ≤ u := hu
  have hCube := pow_le_pow_left₀ hu₀ huv 3
  have hMass : endpointCubic u ≤ endpointCubic v := by
    unfold endpointCubic
    linarith only [hCube,huv]
  unfold endpointPosition
  exact add_le_add huv (mul_le_mul_of_nonneg_left hMass hj)

private def powLower (a L x M : ℝ) : ℝ :=
  L * ∑ j ∈ Finset.range 5, risingCoefficient a j * (1 - x / M) ^ j

private def powUpper (a H x M r : ℝ) : ℝ :=
  H * ((∑ j ∈ Finset.range 5, risingCoefficient a j * (1 - x / M) ^ j) +
    risingCoefficient a 5 * (1 - x / M) ^ 5 / (1 - r))

private theorem powEnclosure {a x d M r L H : ℝ} (ha : 0 < a) (hd : 0 < d) (hdx : d ≤ x)
    (hxM : x ≤ M) (hr : 0 ≤ r) (hr₁ : r < 1) (hwR : 1 - d / M ≤ r)
    (hRatio : (1 - d / M) * ((a + 5) / 6) ≤ r)
    (hL : L ≤ M ^ (-a)) (hH : M ^ (-a) ≤ H) :
    powLower a L x M ≤ x ^ (-a) ∧ x ^ (-a) ≤ powUpper a H x M r := by
  have hx := hd.trans_le hdx
  have hM := hx.trans_le hxM
  exact scaled_binomial_four_enclosure ha hx hM hxM
    (sub_le_sub_left (div_le_div_of_nonneg_right hdx hM.le) 1) hr hr₁ hwR hRatio hL hH

private theorem endpoint_pureRight_clear {u x : ℝ} (hx : 0 < x) :
    x * (x + 1) * pureRight (9 / 5) u x =
      ((9 / 5) * middleZ u - x) * (x + 1) * x ^ (-(9 / 5 : ℝ)) +
      ((9 / 5) * middleA u + x + 1) * x * (x + 1) ^ (-(9 / 5 : ℝ)) := by
  have hx' := add_pos hx zero_lt_one
  unfold pureRight
  rw [show -(9 / 5 + 1 : ℝ) = -(9 / 5 : ℝ) - 1 by ring,
    Real.rpow_sub_one hx.ne',Real.rpow_sub_one hx'.ne']
  field_simp [hx.ne',hx'.ne']
  ring

private theorem endpoint_primitive_clear {u x : ℝ} (hx : 0 < x) :
    pureRightPrimitive (9 / 5) u x =
      (middleZ u - (5 / 4) * x) * x ^ (-(9 / 5 : ℝ)) +
      (middleA u + (5 / 4) * (x + 1)) * (x + 1) ^ (-(9 / 5 : ℝ)) := by
  unfold pureRightPrimitive
  rw [show (1 : ℝ) - 9 / 5 = -(9 / 5) + 1 by ring,
    Real.rpow_add_one hx.ne',Real.rpow_add_one (add_pos hx zero_lt_one).ne']
  ring

private theorem endpoint_delta_power {u : ℝ} (hu : u < 1) :
    (1 - u) ^ (14 / 5 : ℝ) = (1 - u) ^ 3 * (1 - u) ^ (-(1 / 5 : ℝ)) := by
  rw [← Real.rpow_natCast,← Real.rpow_add (sub_pos.mpr hu)]
  norm_num


private theorem rationalPowEnclosure {x d M r L H : ℝ} {k : ℕ} (hd : 0 < d) (hdx : d ≤ x)
    (hxM : x ≤ M) (hk : 0 < k) (hr : 0 ≤ r) (hr₁ : r < 1) (hwR : 1 - d / M ≤ r)
    (hRatio : (1 - d / M) * (((k : ℝ) / 5 + 5) / 6) ≤ r)
    (hL : 0 ≤ L) (hH : 0 ≤ H) (hLow : L ^ 5 < (M ^ k)⁻¹) (hHigh : (M ^ k)⁻¹ < H ^ 5) :
    powLower ((k : ℝ) / 5) L x M ≤ x ^ (-((k : ℝ) / 5)) ∧
      x ^ (-((k : ℝ) / 5)) ≤ powUpper ((k : ℝ) / 5) H x M r := by
  have hM := hd.trans_le (hdx.trans hxM)
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  apply powEnclosure (by positivity) hd hdx hxM hr hr₁ hwR hRatio
  · simpa only [neg_div] using (fifth_rpow_lower hM hL hLow).le
  · simpa only [neg_div] using (fifth_rpow_upper hM hH hHigh).le

private theorem endpointPosition_bounds {l h j u : ℝ} (hl : 0 ≤ l) (hj : 0 ≤ j)
    (hu : u ∈ Icc l h) :
    endpointPosition j l ≤ endpointPosition j u ∧ endpointPosition j u ≤ endpointPosition j h := by
  have hU := hl.trans hu.1
  have hH := hU.trans hu.2
  exact ⟨endpointPosition_mono hj (mem_Ici.mpr hl) (mem_Ici.mpr hU) hu.1,
    endpointPosition_mono hj (mem_Ici.mpr hU) (mem_Ici.mpr hH) hu.2⟩

private theorem uPower_bounds {u : ℝ} (hu : u ∈ Icc (2 / 3 : ℝ) (7 / 8)) :
    powLower (9 / 5) (635851219993579191 / 500000000000000000) u (7 / 8) ≤ u ^ (-(9 / 5 : ℝ)) ∧
      u ^ (-(9 / 5 : ℝ)) ≤ powUpper (9 / 5) (1271702439987158383 / 1000000000000000000) u (7 / 8) (17 / 63) := by
  have h₁ : (2 / 3) ≤ u := by
    exact hu.1
  have h₂ : u ≤ (7 / 8) := by
    exact hu.2
  simpa only [Nat.cast_ofNat] using rationalPowEnclosure (k := 9) (by norm_num) h₁ h₂
    (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem upPower_bounds {u : ℝ} (hu : u ∈ Icc (2 / 3 : ℝ) (7 / 8)) :
    powLower (9 / 5) (161275246596697203 / 500000000000000000) (u + 1) (15 / 8) ≤ (u + 1) ^ (-(9 / 5 : ℝ)) ∧
      (u + 1) ^ (-(9 / 5 : ℝ)) ≤ powUpper (9 / 5) (322550493193394407 / 1000000000000000000) (u + 1) (15 / 8) (17 / 135) := by
  have h₁ : (5 / 3) ≤ (u + 1) := by
    linarith only [hu.1]
  have h₂ : (u + 1) ≤ (15 / 8) := by
    linarith only [hu.2]
  simpa only [Nat.cast_ofNat] using rationalPowEnclosure (k := 9) (by norm_num) h₁ h₂
    (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem xPower_bounds {u : ℝ} (hu : u ∈ Icc (2 / 3 : ℝ) (7 / 8)) :
    powLower (9 / 5) (196522960198032107 / 500000000000000000) (endpointPosition 1 u) (42 / 25) ≤ (endpointPosition 1 u) ^ (-(9 / 5 : ℝ)) ∧
      (endpointPosition 1 u) ^ (-(9 / 5 : ℝ)) ≤ powUpper (9 / 5) (78609184079212843 / 200000000000000000) (endpointPosition 1 u) (42 / 25) (20009 / 64827) := by
  have h₁ : (31448 / 25725) ≤ (endpointPosition 1 u) := by
    have h := (endpointPosition_bounds (j := 1) (by norm_num) (by norm_num) hu).1
    norm_num [endpointPosition,endpointCubic] at h
    simpa only [endpointPosition,endpointCubic,one_mul] using h
  have h₂ : (endpointPosition 1 u) ≤ (42 / 25) := by
    have h := (endpointPosition_bounds (j := 1) (by norm_num) (by norm_num) hu).2
    norm_num [endpointPosition,endpointCubic] at h
    simpa only [endpointPosition,endpointCubic,one_mul] using h
  simpa only [Nat.cast_ofNat] using rationalPowEnclosure (k := 9) (by norm_num) h₁ h₂
    (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem xpPower_bounds {u : ℝ} (hu : u ∈ Icc (2 / 3 : ℝ) (7 / 8)) :
    powLower (9 / 5) (169573260510100783 / 1000000000000000000) (endpointPosition 1 u + 1) (67 / 25) ≤ (endpointPosition 1 u + 1) ^ (-(9 / 5 : ℝ)) ∧
      (endpointPosition 1 u + 1) ^ (-(9 / 5 : ℝ)) ≤ powUpper (9 / 5) (10598328781881299 / 62500000000000000) (endpointPosition 1 u + 1) (67 / 25) (40018 / 206829) := by
  have h₁ : (57173 / 25725) ≤ (endpointPosition 1 u + 1) := by
    have h := (endpointPosition_bounds (j := 1) (by norm_num) (by norm_num) hu).1
    norm_num [endpointPosition,endpointCubic] at h
    unfold endpointPosition endpointCubic
    linarith only [h]
  have h₂ : (endpointPosition 1 u + 1) ≤ (67 / 25) := by
    have h := (endpointPosition_bounds (j := 1) (by norm_num) (by norm_num) hu).2
    norm_num [endpointPosition,endpointCubic] at h
    unfold endpointPosition endpointCubic
    linarith only [h]
  simpa only [Nat.cast_ofNat] using rationalPowEnclosure (k := 9) (by norm_num) h₁ h₂
    (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem tPower_bounds {u : ℝ} (hu : u ∈ Icc (2 / 3 : ℝ) (7 / 8)) :
    powLower (9 / 5) (26702196151322461 / 100000000000000000) (endpointPosition (3 / 2) u) (833 / 400) ≤ (endpointPosition (3 / 2) u) ^ (-(9 / 5 : ℝ)) ∧
      (endpointPosition (3 / 2) u) ^ (-(9 / 5 : ℝ)) ≤ powUpper (9 / 5) (267021961513224611 / 1000000000000000000) (endpointPosition (3 / 2) u) (833 / 400) (47921 / 151263) := by
  have h₁ : (38597 / 25725) ≤ (endpointPosition (3 / 2) u) := by
    have h := (endpointPosition_bounds (j := (3 / 2)) (by norm_num) (by norm_num) hu).1
    norm_num [endpointPosition,endpointCubic] at h
    simpa only [endpointPosition,endpointCubic,one_mul] using h
  have h₂ : (endpointPosition (3 / 2) u) ≤ (833 / 400) := by
    have h := (endpointPosition_bounds (j := (3 / 2)) (by norm_num) (by norm_num) hu).2
    norm_num [endpointPosition,endpointCubic] at h
    simpa only [endpointPosition,endpointCubic,one_mul] using h
  simpa only [Nat.cast_ofNat] using rationalPowEnclosure (k := 9) (by norm_num) h₁ h₂
    (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem tpPower_bounds {u : ℝ} (hu : u ∈ Icc (2 / 3 : ℝ) (7 / 8)) :
    powLower (9 / 5) (131817917584213129 / 1000000000000000000) (endpointPosition (3 / 2) u + 1) (1233 / 400) ≤ (endpointPosition (3 / 2) u + 1) ^ (-(9 / 5 : ℝ)) ∧
      (endpointPosition (3 / 2) u + 1) ^ (-(9 / 5 : ℝ)) ≤ powUpper (9 / 5) (13181791758421313 / 100000000000000000) (endpointPosition (3 / 2) u + 1) (1233 / 400) (814657 / 3806271) := by
  have h₁ : (64322 / 25725) ≤ (endpointPosition (3 / 2) u + 1) := by
    have h := (endpointPosition_bounds (j := (3 / 2)) (by norm_num) (by norm_num) hu).1
    norm_num [endpointPosition,endpointCubic] at h
    unfold endpointPosition endpointCubic
    linarith only [h]
  have h₂ : (endpointPosition (3 / 2) u + 1) ≤ (1233 / 400) := by
    have h := (endpointPosition_bounds (j := (3 / 2)) (by norm_num) (by norm_num) hu).2
    norm_num [endpointPosition,endpointCubic] at h
    unfold endpointPosition endpointCubic
    linarith only [h]
  simpa only [Nat.cast_ofNat] using rationalPowEnclosure (k := 9) (by norm_num) h₁ h₂
    (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem dPower_bounds {u : ℝ} (hu : u ∈ Icc (2 / 3 : ℝ) (7 / 8)) :
    powLower (1 / 5) (49829237584620693 / 40000000000000000) (1 - u) (1 / 3) ≤ (1 - u) ^ (-(1 / 5 : ℝ)) ∧
      (1 - u) ^ (-(1 / 5 : ℝ)) ≤ powUpper (1 / 5) (622865469807758663 / 500000000000000000) (1 - u) (1 / 3) (5 / 8) := by
  have h₁ : (1 / 8) ≤ (1 - u) := by
    linarith only [hu.2]
  have h₂ : (1 - u) ≤ (1 / 3) := by
    linarith only [hu.1]
  simpa only [Nat.cast_one] using rationalPowEnclosure (k := 1) (r := 5 / 8)
    (L := 49829237584620693 / 40000000000000000) (H := 622865469807758663 / 500000000000000000)
    (by norm_num) h₁ h₂
    (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem sixPower_bounds {u : ℝ} (hu : u ∈ Icc (1 / 2 : ℝ) (7 / 8)) :
    powLower (9 / 5) (21762552738492793 / 500000000000000000) (endpointPosition 6 u) (1141 / 200) ≤ (endpointPosition 6 u) ^ (-(9 / 5 : ℝ)) ∧
      (endpointPosition 6 u) ^ (-(9 / 5 : ℝ)) ≤ powUpper (9 / 5) (43525105476985587 / 1000000000000000000) (endpointPosition 6 u) (1141 / 200) (1112021 / 1956815) := by
  have h₁ : (48781 / 17150) ≤ (endpointPosition 6 u) := by
    have h := (endpointPosition_bounds (j := 6) (by norm_num) (by norm_num) hu).1
    norm_num [endpointPosition,endpointCubic] at h
    simpa only [endpointPosition,endpointCubic,one_mul] using h
  have h₂ : (endpointPosition 6 u) ≤ (1141 / 200) := by
    have h := (endpointPosition_bounds (j := 6) (by norm_num) (by norm_num) hu).2
    norm_num [endpointPosition,endpointCubic] at h
    simpa only [endpointPosition,endpointCubic,one_mul] using h
  simpa only [Nat.cast_ofNat] using rationalPowEnclosure (k := 9) (by norm_num) h₁ h₂
    (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem sixpPower_bounds {u : ℝ} (hu : u ∈ Icc (1 / 2 : ℝ) (7 / 8)) :
    powLower (9 / 5) (8136210961041829 / 250000000000000000) (endpointPosition 6 u + 1) (1341 / 200) ≤ (endpointPosition 6 u + 1) ^ (-(9 / 5 : ℝ)) ∧
      (endpointPosition 6 u + 1) ^ (-(9 / 5 : ℝ)) ≤ powUpper (9 / 5) (32544843844167317 / 1000000000000000000) (endpointPosition 6 u + 1) (1341 / 200) (1112021 / 2299815) := by
  have h₁ : (65931 / 17150) ≤ (endpointPosition 6 u + 1) := by
    have h := (endpointPosition_bounds (j := 6) (by norm_num) (by norm_num) hu).1
    norm_num [endpointPosition,endpointCubic] at h
    unfold endpointPosition endpointCubic
    linarith only [h]
  have h₂ : (endpointPosition 6 u + 1) ≤ (1341 / 200) := by
    have h := (endpointPosition_bounds (j := 6) (by norm_num) (by norm_num) hu).2
    norm_num [endpointPosition,endpointCubic] at h
    unfold endpointPosition endpointCubic
    linarith only [h]
  simpa only [Nat.cast_ofNat] using rationalPowEnclosure (k := 9) (by norm_num) h₁ h₂
    (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private def clearedRight (u x q q' : ℝ) : ℝ :=
  ((9 / 5) * middleZ u - x) * (x + 1) * q +
    ((9 / 5) * middleA u + x + 1) * x * q'

private theorem endpoint_middleA_nonneg {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ 1) : 0 ≤ middleA u := by
  unfold middleA
  have : 0 ≤ 2 - u := by linarith only [hU]
  positivity

private theorem endpoint_z_coefficient {u : ℝ} (hu : 2 / 3 ≤ u) (hU : u ≤ 7 / 8) :
    0 ≤ (9 / 5) * middleZ u - u := by
  unfold middleZ middleA
  nlinarith only [mul_nonneg (show 0 ≤ u by linarith only [hu])
    (show 0 ≤ 54 * u - 8 by linarith only [hu])]

private theorem endpoint_following_coefficient {u j : ℝ} (hu : 0 < u) (hU : u ≤ 7 / 8)
    (hj : 1 ≤ j) : (9 / 5) * middleZ u - endpointPosition j u ≤ 0 := by
  have hMass : 5 / 7 * u ≤ endpointCubic u := by
    unfold endpointCubic
    exact le_add_of_nonneg_left (by positivity)
  have hX : (1 + 5 / 7) * u ≤ endpointPosition j u := by
    unfold endpointPosition
    have h := mul_le_mul hj hMass (by positivity : 0 ≤ (5 / 7 : ℝ) * u)
      (show 0 ≤ j by linarith only [hj])
    nlinarith only [h]
  unfold middleZ middleA
  have hU' : 0 ≤ (6 / 25 : ℝ) * (2 - u) := by linarith only [hU]
  have hProd := mul_le_mul_of_nonneg_left (show (6 / 25 : ℝ) * (2 - u) ≥ 27 / 100 by linarith only [hU]) hu.le
  nlinarith only [hX,hProd,hu]

private theorem clearedRight_mono_lower {u x q q' : ℝ} (hu : 0 ≤ u) (hU : u ≤ 1)
    (hx : 0 < x) (hZ : (9 / 5) * middleZ u - x ≤ 0)
    (hQ : q ≤ x ^ (-(9 / 5 : ℝ))) (hQ' : (x + 1) ^ (-(9 / 5 : ℝ)) ≤ q') :
    x * (x + 1) * pureRight (9 / 5) u x ≤ clearedRight u x q q' := by
  rw [endpoint_pureRight_clear hx]
  unfold clearedRight
  have hA := endpoint_middleA_nonneg hu hU
  exact add_le_add (mul_le_mul_of_nonpos_left hQ (mul_nonpos_of_nonpos_of_nonneg hZ (by positivity)))
    (mul_le_mul_of_nonneg_left hQ' (by positivity))

private theorem clearedRight_mono_upper {u x q q' : ℝ} (hu : 0 ≤ u) (hU : u ≤ 1)
    (hx : 0 < x) (hZ : 0 ≤ (9 / 5) * middleZ u - x)
    (hQ : x ^ (-(9 / 5 : ℝ)) ≤ q) (hQ' : (x + 1) ^ (-(9 / 5 : ℝ)) ≤ q') :
    x * (x + 1) * pureRight (9 / 5) u x ≤ clearedRight u x q q' := by
  rw [endpoint_pureRight_clear hx]
  unfold clearedRight
  have hA := endpoint_middleA_nonneg hu hU
  exact add_le_add (mul_le_mul_of_nonneg_left hQ (by positivity)) (mul_le_mul_of_nonneg_left hQ' (by positivity))

private def endpointTailBound (u : ℝ) : ℝ :=
  pureRightPrimitive (9 / 5) u (endpointPosition (3 / 2) u) +
    (10 / 9) * (1 - u) ^ (14 / 5 : ℝ)

private def endpointNative (u : ℝ) : ℝ :=
  u * (1 + (9 / 5) * middleA u - pureZ (9 / 5)) + endpointCubic u * pureRight (9 / 5) u u

private def endpointFirst (u : ℝ) : ℝ :=
  endpointCubic u * pureRight (9 / 5) u (endpointPosition 1 u)


private def uPow (u : ℝ) : ℝ := powUpper (9 / 5) (1271702439987158383 / 1000000000000000000) u (7 / 8) (17 / 63)
private def upPow (u : ℝ) : ℝ := powUpper (9 / 5) (322550493193394407 / 1000000000000000000) (u + 1) (15 / 8) (17 / 135)
private def xPow (u : ℝ) : ℝ := powLower (9 / 5) (196522960198032107 / 500000000000000000) (endpointPosition 1 u) (42 / 25)
private def xpPow (u : ℝ) : ℝ := powUpper (9 / 5) (10598328781881299 / 62500000000000000) (endpointPosition 1 u + 1) (67 / 25) (40018 / 206829)
private def tPow (u : ℝ) : ℝ := powLower (9 / 5) (26702196151322461 / 100000000000000000) (endpointPosition (3 / 2) u) (833 / 400)
private def tpPow (u : ℝ) : ℝ := powUpper (9 / 5) (13181791758421313 / 100000000000000000) (endpointPosition (3 / 2) u + 1) (1233 / 400) (814657 / 3806271)
private def dPow (u : ℝ) : ℝ := powUpper (1 / 5) (622865469807758663 / 500000000000000000) (1 - u) (1 / 3) (5 / 8)
private def sixPow (u : ℝ) : ℝ := powLower (9 / 5) (21762552738492793 / 500000000000000000) (endpointPosition 6 u) (1141 / 200)
private def sixpPow (u : ℝ) : ℝ := powUpper (9 / 5) (32544843844167317 / 1000000000000000000) (endpointPosition 6 u + 1) (1341 / 200) (1112021 / 2299815)

private def endpointTailPolynomial (u : ℝ) : ℝ :=
  (middleZ u - (5 / 4) * endpointPosition (3 / 2) u) * tPow u +
    (middleA u + (5 / 4) * (endpointPosition (3 / 2) u + 1)) * tpPow u +
    (10 / 9) * (1 - u) ^ 3 * dPow u

private def endpointBasePolynomial (u : ℝ) : ℝ :=
  u * (1 + (9 / 5) * middleA u - (22446558 / 10000000))

private def nativeDenominator (u : ℝ) : ℝ := u * (u + 1)

private def firstDenominator (u : ℝ) : ℝ :=
  endpointPosition 1 u * (endpointPosition 1 u + 1)

private def clearedNativePolynomial (u : ℝ) : ℝ :=
  endpointCubic u * clearedRight u u (uPow u) (upPow u)

private def clearedFirstPolynomial (u : ℝ) : ℝ :=
  endpointCubic u * clearedRight u (endpointPosition 1 u) (xPow u) (xpPow u)

private def sixPolynomial (u : ℝ) : ℝ :=
  -(clearedRight u (endpointPosition 6 u) (sixPow u) (sixpPow u))

private def valuePolynomial (u : ℝ) : ℝ :=
  -(nativeDenominator u * firstDenominator u * (endpointBasePolynomial u + endpointTailPolynomial u + 1 / 2000) +
    firstDenominator u * clearedNativePolynomial u)

private def valueWithFirstPolynomial (u : ℝ) : ℝ :=
  valuePolynomial u - nativeDenominator u * clearedFirstPolynomial u

private def ratioPolynomial (u : ℝ) : ℝ :=
  firstDenominator u * ((7 / 80) * u - endpointTailPolynomial u)

private def ratioWithFirstPolynomial (u : ℝ) : ℝ :=
  ratioPolynomial u - clearedFirstPolynomial u

private def sixCoefficients : Fin 22 → ℕ :=
  ![1522527913262745756120175120718441387341064569243426655098837875072,
    31912842900449889147428708268882885997668543947225611824632141500880,
    316320420742593035759064286487674467852028906473958965368068545607304,
    1971355482486721132464726388428782015464256307868672288501705633371783,
    8663052476297914613536122191591714295412119753305174279946700521099001,
    28533505677874190727292401865863338304941060688845540331790452233084332,
    73087108059437014287273243407006854606743032111924817988419403079271879,
    149085286951900899749638854856998239546074931287079338414067870165090048,
    245978407106053083368942648199355309894174165151086147312236442405453376,
    331546743842793920452747962085794271851769507340248362158081580589232217,
    367150463558801013974147085353101581622247585509717158685405649603487089,
    334744177320855249501869835202402497713737846281353621390370107400401708,
    250976936181944908359788510760732657607143415128916734942524119816076016,
    154029170707945994537544257158044528310550838855622225910349959133372787,
    76718899320424179875382564402357240685515142379116204913346890075098249,
    30592606500890302450089478840233422987345237886060989028172145479487772,
    9565822904228645532977000740336229214201984090216820632395172019301996,
    2271720495483512190488139166902117361314966654184044084100375442679215,
    389275454713805554485055925508578849423611394971614491927212858845975,
    44003206656446055328322742096393612287038417671185179754208380588625,
    2728741439190318596532122436750582668041342401932529466852571956875,
    53722207931429631209448534835967646573326712584708438278909115625]

private theorem sixCertificate {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    0 < sixPolynomial ((1 / 2) + (3 / 8) * v) := by
  have hC (i : Fin 22) : (21 : ℕ).choose i.val ≤ sixCoefficients i := by
    fin_cases i <;> decide
  have hPos := ACS12.bernsteinScaledFinCertificate_pos (d := 9726054970213403585942505013775651343532500000000000000000000000000) hv (by decide) hC
  have hEq : sixPolynomial ((1 / 2) + (3 / 8) * v) =
      (∑ j : Fin 22, (sixCoefficients j : ℝ) * v ^ j.val * (1 - v) ^ (21 - j.val)) / 9726054970213403585942505013775651343532500000000000000000000000000 := by
    simp only [sixPolynomial, valuePolynomial, ratioPolynomial, endpointTailPolynomial, endpointBasePolynomial,
      clearedNativePolynomial, clearedFirstPolynomial, nativeDenominator, firstDenominator, clearedRight,
      sixPow, sixpPow, powLower, powUpper, risingCoefficient, Finset.sum_range_succ,
      endpointCubic, endpointPosition, middleZ, middleA, Fin.sum_univ_succ, sixCoefficients,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ]
    ring
  rwa [hEq]

private def valueCoefficients : Fin 27 → ℕ :=
  ![1061568100064378676208714063915291748491115869480880329317313220748962602229908524498944,
    30269677983940133541407009434079540385740555008041188425724937610605571489093793993457664,
    412427224972268732593614064818583728074502065853640117070667025630364945910011317683486720,
    3577680409509079889357517848784475407820501854565680303410514506539636120918289705618309120,
    22206851944508073505184403383743294076457448344626133335121959106686043344287783579696291840,
    105068856025299115572652820932040541414721528283023848721299221671328093395696819570449248256,
    394106646472391799138818366946921063203157399456546733321942762335820754081274852243570149376,
    1203211424793634632657120579804282476479752618813950087283354881427214162049519815395301482240,
    3045697009596423781132351701717538520515248429628319473649769966834080490770346857627000412960,
    6477708923930797576607046378691961132834300291709481051479945617016915653112023816920530335420,
    11687444353657839231258105369081891551860896664902781641998144717182486428005986592250597550804,
    18011361347623167896388350304612668553322292889377217263385750238695023236416167804496515872719,
    23817719952418410606899038420846380196416546480133600740544573577960901668342376351350294814050,
    27099120264100913473294266800046605932051892215020078566229967044455867157774001599990829664785,
    26554675728543510086927517332747551174410649595811742368621181516627203184437251781409747244820,
    22395823442399519196891886531427716318114873747208006890294384498000224773760101376039392279616,
    16218085714979168726767608540980076255576019740760151927743395731063709062437378759977476689716,
    10041215197871580700058668623399195612203790891888951768107504345181490854693054589947760011510,
    5280973285600918864767229262812223052893482862603893149579931680025322038522305395463768186420,
    2337607005082615826716357084559986606753090493989399528500944088545344629008302956310655514615,
    859728120776056342993435923394709320994785813820674118501813885345238907692297709866736961874,
    258017004049476561690354188433618007473951438568444760989769937765438619730609923171749233709,
    61576439130377695034766580975522431668251738917087190232919464156962711455990294157669342980,
    11242342464730035199776533485660774991985319878497274271192153071484522364861546875392209850,
    1475005779331905969956421525034447805256210557607670207314363206559047325929928893519229000,
    123837453005502720889680138622226272036024728636125581707582206028555181321935921048690000,
    4998190224090314986303223269227972548506554146348842305326031064048854131020092951450000]

private theorem valueCertificate {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    0 < valuePolynomial ((2 / 3) + (5 / 24) * v) := by
  have hC (i : Fin 27) : (26 : ℕ).choose i.val ≤ valueCoefficients i := by
    fin_cases i <;> decide
  have hPos := ACS12.bernsteinScaledFinCertificate_pos (d := 11532652776919562281342726852828339592266460207483395891200000000000000000000000000000000) hv (by decide) hC
  have hEq : valuePolynomial ((2 / 3) + (5 / 24) * v) =
      (∑ j : Fin 27, (valueCoefficients j : ℝ) * v ^ j.val * (1 - v) ^ (26 - j.val)) / 11532652776919562281342726852828339592266460207483395891200000000000000000000000000000000 := by
    simp only [valuePolynomial, valuePolynomial, ratioPolynomial, endpointTailPolynomial, endpointBasePolynomial,
      clearedNativePolynomial, clearedFirstPolynomial, nativeDenominator, firstDenominator, clearedRight,
      uPow, upPow, xPow, xpPow, tPow, tpPow, dPow, powLower, powUpper, risingCoefficient, Finset.sum_range_succ,
      endpointCubic, endpointPosition, middleZ, middleA, Fin.sum_univ_succ, valueCoefficients,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ]
    ring
  rwa [hEq]

private def valueWithFirstCoefficients : Fin 27 → ℕ :=
  ![433371714740565417615443916770914224307724009290250804064934410187333602184409984685838825280241664,
    12179642860070644083342559126644349348610038649784023514124621021408038400679982709671294634488233984,
    161189677705582139856002660385383527153448211129737213313886849876905459469123013545176584333631160320,
    1341558474166299832614645026606155935007328093327764915797396669487474634207430872556030140079940894720,
    7902840461974828975795209772789988367090295192388884035251209390980148958078278554611735670864771031040,
    35130881727700379909956057870002211447348691294199586729246960741346542992350479728339394830353624641536,
    122620104607730028604552202557863735017432156669607404761563291894767196217723904329789924040788405088256,
    345054164272297269244739274778203889941738809251245514732849955228971086279746219221862182006780758973440,
    797327724408314459028694058044418686436861366705207536866908332294518968506589417917464040925019518297760,
    1532613082446530227298340911245816930922726295580492096717906493015049763504029306450524520382060229840020,
    2472903383163949332679024210687566310387263293979109477815107091639307476396587300109006698053424110985324,
    3369733299445687337735657648384867387921118087187342132006000661102683478141560615685486523239477400081189,
    3891966261304260105470282144566237976035991279657810710487373425453213013794433983406906655355247176640550,
    3815674929321886672371495013168747612205100126522712698438878731473201026970334038608995819510908239911835,
    3173848504621641671871417404696071798544932123243462948807045415126657561246912741515485484374854126721420,
    2234380357617321728359203661686608930610197550467824902782430861740696361234992156844846308363086118949696,
    1325488260235750105646087279734932063746385426048807632478820674555150178895498976090679459755802557422796,
    658364457806096405754148729191115480873422978904201547159368310830761813038587376755754303464362702957810,
    271533716849726619270107607191619066308525547032138839504809508481136244714932701263703616681739333321020,
    92099062515061957146324300649292735115028758757384454102130766637237132310156683136689555687484819089565,
    25454066353003618975973904739563647310285976415227679592043505844181970484837327843219424608705067735494,
    5707494626442023686210472466831058845173421269900631955581597676359771471701230717951311327326653920879,
    1046968708078953051240730955486188660267544451184048088544848843914990234882033658855180354058346030380,
    160824289163378221564622346187831020085780443634405373401250641204160532102588210736428239764532740350,
    20756909224357716981825311179416144578379388988080442504640711886466302771903194352265961693723999000,
    2024319781368348249294195048537395231205253567866169225683497397612508441099670210204039410428390000,
    105831920714557157777298098172997324708975655519458420097706462559856867518372026654320373889950000]

private theorem valueWithFirstCertificate {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    0 < valueWithFirstPolynomial ((2 / 3) + (5 / 24) * v) := by
  have hC (i : Fin 27) : (26 : ℕ).choose i.val ≤ valueWithFirstCoefficients i := by
    fin_cases i <;> decide
  have hPos := ACS12.bernsteinScaledFinCertificate_pos (d := 38766189398686989027143453764363777190952612300774236597735308285747200000000000000000000000000000000) hv (by decide) hC
  have hEq : valueWithFirstPolynomial ((2 / 3) + (5 / 24) * v) =
      (∑ j : Fin 27, (valueWithFirstCoefficients j : ℝ) * v ^ j.val * (1 - v) ^ (26 - j.val)) / 38766189398686989027143453764363777190952612300774236597735308285747200000000000000000000000000000000 := by
    simp only [valueWithFirstPolynomial, valuePolynomial, ratioPolynomial, endpointTailPolynomial, endpointBasePolynomial,
      clearedNativePolynomial, clearedFirstPolynomial, nativeDenominator, firstDenominator, clearedRight,
      uPow, upPow, xPow, xpPow, tPow, tpPow, dPow, powLower, powUpper, risingCoefficient, Finset.sum_range_succ,
      endpointCubic, endpointPosition, middleZ, middleA, Fin.sum_univ_succ, valueWithFirstCoefficients,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ]
    ring
  rwa [hEq]

private def ratioCoefficients : Fin 25 → ℕ :=
  ![4775183812499116635954601082363788139637618992698561633886044734949966217216,
    121119643063788074370109806934917244668651385218181858898540798719725009240064,
    1465866242775390161329458501265373739101391985783943085031456994732640702652416,
    11271319569156375621923630069245985792653453627373405779398693403289507198726144,
    61844681755028371487638194575414613368480810732855079544044921870919194826264576,
    257800255510419387942418847920334164493884660768577892422194472437428432742387968,
    848593056427175476468415595835100222398155764658112966200915360219343555657552512,
    2263088142637377378543799857328096992858806098201198279461136990948837776832963788,
    4977448336272228559592278037537901765772916744164307281188154587311319473429516892,
    9141998278565432076768929767335410892194952090712916461975554637196359116059269163,
    14144258665331568488695161234096589478190704729221444607529009002398929663706680658,
    18540643724899024113002749355799876806595687153467973322120266767077946816289434277,
    20659497047581519893496759376246237862442865853913088105720555207087295885177861668,
    19591544736159416518481666525653089356845438502252971906040915983966729118231823712,
    15796856413325950046138787308883888657568922336649255181001000598132355166500110708,
    10796557884883638750653678676223383857980714265427419178439662715677266755952696526,
    6220415789707897663196904380505061183694807858903616842892036037309756088329510524,
    2995782297418706412549100343937852032015223206366489910165101189980434047362849011,
    1191385476548961782578180282714182766631822042705985577914860563712311704518863074,
    384466383263948040984360959988319598029480933392654492510549262905411209511962481,
    98156963803715738077838503131649140896098523059189927675471516192705535484691620,
    19081796168775175259848434196491144830479589416932906279947261192723373583845570,
    2654172802125325865324861477080379602190578999887121455814283022923769043476840,
    235296645434633959122746014882955170667932853485374267909387892745849406201360,
    9990381633416966716067916607176097264354043527998293237283180564100838001360]

private theorem ratioCertificate {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    0 < ratioPolynomial ((2 / 3) + (5 / 24) * v) := by
  have hC (i : Fin 25) : (24 : ℕ).choose i.val ≤ ratioCoefficients i := by
    fin_cases i <;> decide
  have hPos := ACS12.bernsteinScaledFinCertificate_pos (d := 37771727755406738004888976837233569449820552550506496000000000000000000000000) hv (by decide) hC
  have hEq : ratioPolynomial ((2 / 3) + (5 / 24) * v) =
      (∑ j : Fin 25, (ratioCoefficients j : ℝ) * v ^ j.val * (1 - v) ^ (24 - j.val)) / 37771727755406738004888976837233569449820552550506496000000000000000000000000 := by
    simp only [ratioPolynomial, valuePolynomial, ratioPolynomial, endpointTailPolynomial, endpointBasePolynomial,
      clearedNativePolynomial, clearedFirstPolynomial, nativeDenominator, firstDenominator, clearedRight,
      xPow, xpPow, tPow, tpPow, dPow, powLower, powUpper, risingCoefficient, Finset.sum_range_succ,
      endpointCubic, endpointPosition, middleZ, middleA, Fin.sum_univ_succ, ratioCoefficients,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ]
    ring
  rwa [hEq]

private def ratioWithFirstCoefficients : Fin 25 → ℕ :=
  ![170260662987559179268822720588787730720164643505255676642821421345214071890647500871172096,
    4140931293083259224357428493034681148510361750682902215739532135143408297444882852607033344,
    47958430830592562988987354395077031203088795474925900343094480407613865777226426330643275776,
    352106958823358348958079430266890006223485353828280676859427779172663105351268285257178230784,
    1840272368165742795962546943246906162474433840776782514582479582250828768458926814697062076416,
    7287757125634831065569580117174394340689305559556629070533797894543187148432517851735386533888,
    22723765434110702297614502008826680880771046122148408305799050658973093056132800700067808970432,
    57222282797166004386493046909520348819641000968100961004771244924548733191789867072867510113828,
    118418345459163615778259231047059633507438595261784614912877238961064613817315205943436487303652,
    203842364733711794740714550823519402675380174680688976597023832135017127775699301128190818252273,
    294279598370813988105340572852853322596945668112376312117890787547024798538407140515555852269638,
    358150411382900166731672531490921399586176003506019181544704868273466725534187770107908490136607,
    368421024656955167726334795856824866624463716003194409904654301102400323288020214476757317033628,
    320413004712619489995700102568120627494596997126017329191674625355006042151822759031937898021152,
    235104621056082696886289760322453429770221969417559156325521887047933969131257207029011266624748,
    144877659985435191277102641808123290076218218952641152489476266049270805788354626192962656328746,
    74414324390321358914838707675848033676777944703444338685013416976707249242320142444229926357044,
    31502331145928439587974132687209027170683564362081708500060544382983406146340240951898909525001,
    10814249633452837121415129621580890749367808931151498386434683880086589185816857768649835753734,
    2940171799846539624052169160393060055931869352331611989758022233492719274792442635197186981091,
    611186970452405727664740967412415671515923312467927904231112916497604517673156564030652025900,
    91871599920393697136671133336356853163588038760012042651839180049744173648849882945817858150,
    9054491347811151715048535306346267640234163246977714505942962940399746902328546018121263800,
    474676069580346432958738145938228632611799953554314964479049129896492684232407820431889200,
    6326988966433427530459639515189699707551387291683983231063103614066291972555289046777200]

private theorem ratioWithFirstCertificate {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    0 < ratioWithFirstPolynomial ((2 / 3) + (5 / 24) * v) := by
  have hC (i : Fin 25) : (24 : ℕ).choose i.val ≤ ratioWithFirstCoefficients i := by
    fin_cases i <;> decide
  have hPos := ACS12.bernsteinScaledFinCertificate_pos (d := 3174174191327846477290055986601471971747532326273170932427356774400000000000000000000000000) hv (by decide) hC
  have hEq : ratioWithFirstPolynomial ((2 / 3) + (5 / 24) * v) =
      (∑ j : Fin 25, (ratioWithFirstCoefficients j : ℝ) * v ^ j.val * (1 - v) ^ (24 - j.val)) / 3174174191327846477290055986601471971747532326273170932427356774400000000000000000000000000 := by
    simp only [ratioWithFirstPolynomial, valuePolynomial, ratioPolynomial, endpointTailPolynomial, endpointBasePolynomial,
      clearedNativePolynomial, clearedFirstPolynomial, nativeDenominator, firstDenominator, clearedRight,
      xPow, xpPow, tPow, tpPow, dPow, powLower, powUpper, risingCoefficient, Finset.sum_range_succ,
      endpointCubic, endpointPosition, middleZ, middleA, Fin.sum_univ_succ, ratioWithFirstCoefficients,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ]
    ring
  rwa [hEq]

private theorem sixPolynomial_pos {u : ℝ} (hu : u ∈ Icc (1 / 2 : ℝ) (7 / 8)) :
    0 < sixPolynomial u := by
  let v := (u - 1 / 2) / (3 / 8)
  have hv : v ∈ Icc (0 : ℝ) 1 := by constructor <;> unfold v <;> linarith only [hu.1,hu.2]
  have h := sixCertificate hv
  rwa [show 1 / 2 + (3 / 8) * v = u by unfold v; ring] at h

private theorem valuePolynomials_pos {u : ℝ} (hu : u ∈ Icc (2 / 3 : ℝ) (7 / 8)) :
    0 < valuePolynomial u ∧ 0 < valueWithFirstPolynomial u ∧
      0 < ratioPolynomial u ∧ 0 < ratioWithFirstPolynomial u := by
  let v := (u - 2 / 3) / (5 / 24)
  have hv : v ∈ Icc (0 : ℝ) 1 := by constructor <;> unfold v <;> linarith only [hu.1,hu.2]
  have h := show 2 / 3 + (5 / 24) * v = u by unfold v; ring
  exact ⟨h ▸ valueCertificate hv,h ▸ valueWithFirstCertificate hv,h ▸ ratioCertificate hv,h ▸ ratioWithFirstCertificate hv⟩

theorem pureRight_sixth_endpoint_neg {u : ℝ} (hu : u ∈ Icc (1 / 2 : ℝ) (7 / 8)) :
    pureRight (9 / 5) u (u + 6 * upperCapMass u) < 0 := by
  have hu₀ := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hu.1
  have hu₁ := hu.2.trans (by norm_num : (7 / 8 : ℝ) ≤ 1)
  let x := endpointPosition 6 u
  have hx : 0 < x := by
    unfold x endpointPosition
    rw [endpointCubic_eq]
    exact add_pos_of_pos_of_nonneg hu₀ (mul_nonneg (by norm_num) (upperCapMass_pos hu₀).le)
  have h := clearedRight_mono_lower hu₀.le hu₁ hx (endpoint_following_coefficient hu₀ hu.2 (by norm_num))
    (sixPower_bounds hu).1 (sixpPower_bounds hu).2
  have hBound : x * (x + 1) * pureRight (9 / 5) u x ≤ -sixPolynomial u := by
    simpa only [sixPolynomial,neg_neg,sixPow,sixpPow] using h
  have hN : x * (x + 1) * pureRight (9 / 5) u x < 0 := hBound.trans_lt (neg_neg_of_pos (sixPolynomial_pos hu))
  have hX : x = u + 6 * upperCapMass u := by unfold x endpointPosition; rw [endpointCubic_eq]
  rw [← hX]
  exact neg_of_mul_neg_right hN (mul_pos hx (add_pos hx zero_lt_one)).le

private theorem endpointTailBound_le {u : ℝ} (hu : u ∈ Icc (2 / 3 : ℝ) (7 / 8)) :
    endpointTailBound u ≤ endpointTailPolynomial u := by
  let t := endpointPosition (3 / 2) u
  have hu₀ := (by norm_num : (0 : ℝ) < 2 / 3).trans_le hu.1
  have hu₁ := hu.2.trans_lt (by norm_num : (7 / 8 : ℝ) < 1)
  have hT : u ≤ t := by
    unfold t endpointPosition
    rw [endpointCubic_eq]
    exact le_add_of_nonneg_right (mul_nonneg (by norm_num) (upperCapMass_pos hu₀).le)
  have ht := hu₀.trans_le hT
  have hA := endpoint_middleA_nonneg hu₀.le hu₁.le
  have hZ : middleZ u - (5 / 4) * t ≤ 0 := by unfold middleZ; linarith only [hA,hT,hu₀]
  have hA' : 0 ≤ middleA u + (5 / 4) * (t + 1) := by positivity
  have h₁ := mul_le_mul_of_nonpos_left (tPower_bounds hu).1 hZ
  have h₂ := mul_le_mul_of_nonneg_left (tpPower_bounds hu).2 hA'
  have h₃ := mul_le_mul_of_nonneg_left (dPower_bounds hu).2
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 10 / 9) (pow_nonneg (sub_nonneg.mpr hu₁.le) 3))
  unfold endpointTailBound endpointTailPolynomial
  rw [endpoint_primitive_clear ht,endpoint_delta_power hu₁]
  change (middleZ u - (5 / 4) * t) * (t ^ (-(9 / 5 : ℝ))) ≤
    (middleZ u - (5 / 4) * t) * tPow u at h₁
  change (middleA u + (5 / 4) * (t + 1)) * ((t + 1) ^ (-(9 / 5 : ℝ))) ≤
    (middleA u + (5 / 4) * (t + 1)) * tpPow u at h₂
  change (10 / 9) * (1 - u) ^ 3 * ((1 - u) ^ (-(1 / 5 : ℝ))) ≤
    (10 / 9) * (1 - u) ^ 3 * dPow u at h₃
  change _ ≤ (middleZ u - (5 / 4) * t) * tPow u +
    (middleA u + (5 / 4) * (t + 1)) * tpPow u + (10 / 9) * (1 - u) ^ 3 * dPow u
  linarith only [h₁,h₂,h₃]

theorem pureAdjacent_endpoint_signed_bounds {u : ℝ} (hu : u ∈ Icc (2 / 3 : ℝ) (7 / 8)) :
    endpointNative u + endpointTailBound u < -(1 / 2000) ∧
    endpointNative u + endpointFirst u + endpointTailBound u < -(1 / 2000) ∧
    endpointTailBound u < (7 / 80) * u ∧
    endpointFirst u + endpointTailBound u < (7 / 80) * u := by
  let x := endpointPosition 1 u
  let m := endpointCubic u
  let U := nativeDenominator u
  let X := firstDenominator u
  have hu₀ := (by norm_num : (0 : ℝ) < 2 / 3).trans_le hu.1
  have hu₁ := hu.2.trans_lt (by norm_num : (7 / 8 : ℝ) < 1)
  have hm : 0 < m := by unfold m; rw [endpointCubic_eq]; exact upperCapMass_pos hu₀
  have hx : 0 < x := by unfold x endpointPosition; change 0 < u + 1 * m; positivity
  have hU : 0 < U := by unfold U nativeDenominator; positivity
  have hX : 0 < X := by unfold X firstDenominator; change 0 < x * (x + 1); positivity
  have hN := clearedRight_mono_upper hu₀.le hu₁.le hu₀ (endpoint_z_coefficient hu.1 hu.2)
    (uPower_bounds hu).2 (upPower_bounds hu).2
  have hF := clearedRight_mono_lower hu₀.le hu₁.le hx (endpoint_following_coefficient hu₀ hu.2 le_rfl)
    (xPower_bounds hu).1 (xpPower_bounds hu).2
  change U * pureRight (9 / 5) u u ≤ clearedRight u u (uPow u) (upPow u) at hN
  change X * pureRight (9 / 5) u x ≤ clearedRight u x (xPow u) (xpPow u) at hF
  have hN' : U * (m * pureRight (9 / 5) u u) ≤ clearedNativePolynomial u := by
    rw [← mul_left_comm]
    exact mul_le_mul_of_nonneg_left hN hm.le
  have hF' : X * endpointFirst u ≤ clearedFirstPolynomial u := by
    unfold endpointFirst
    change X * (m * pureRight (9 / 5) u x) ≤ _
    rw [← mul_left_comm]
    exact mul_le_mul_of_nonneg_left hF hm.le
  have hZ : u * (1 + (9 / 5) * middleA u - pureZ (9 / 5)) ≤ endpointBasePolynomial u := by
    unfold endpointBasePolynomial
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left pureZ_upperEndpoint_lower.le _) hu₀.le
  have hT := endpointTailBound_le hu
  obtain ⟨hVP,hVFP,hRP,hRFP⟩ := valuePolynomials_pos hu
  have hB := mul_le_mul_of_nonneg_left (add_le_add hZ hT) (mul_pos hU hX).le
  have hNN := mul_le_mul_of_nonneg_left hN' hX.le
  have hFF := mul_le_mul_of_nonneg_left hF' hU.le
  change 0 < -(U * X * (endpointBasePolynomial u + endpointTailPolynomial u + 1 / 2000) +
    X * clearedNativePolynomial u) at hVP
  change 0 < -(U * X * (endpointBasePolynomial u + endpointTailPolynomial u + 1 / 2000) +
    X * clearedNativePolynomial u) - U * clearedFirstPolynomial u at hVFP
  change 0 < X * ((7 / 80) * u - endpointTailPolynomial u) at hRP
  change 0 < X * ((7 / 80) * u - endpointTailPolynomial u) - clearedFirstPolynomial u at hRFP
  have hE : endpointNative u = u * (1 + (9 / 5) * middleA u - pureZ (9 / 5)) +
      m * pureRight (9 / 5) u u := rfl
  rw [hE]
  constructor
  · apply lt_of_mul_lt_mul_left _ (mul_pos hU hX).le
    linarith only [hB,hNN,hVP]
  constructor
  · apply lt_of_mul_lt_mul_left _ (mul_pos hU hX).le
    linarith only [hB,hNN,hFF,hVFP]
  · have hTT := mul_le_mul_of_nonneg_left hT hX.le
    constructor
    · apply lt_of_mul_lt_mul_left _ hX.le
      linarith only [hTT,hRP]
    · apply lt_of_mul_lt_mul_left _ hX.le
      linarith only [hTT,hF',hRFP]

theorem pureAdjacent_integral_endpoint {L u : ℝ} (hL : 0 < L) (hu : u ∈ Icc (2 / 3 : ℝ) (7 / 8)) :
    middleLawBase (9 / 5) L 0 u +
      samplingHead (lawRightClip (9 / 5) L 0 u) u (adjacentCap (9 / 5) u) < -(1 / 2000) ∧
    samplingTail (lawRightClip (9 / 5) L 0 u) u (adjacentCap (9 / 5) u) < (7 / 80) * u := by
  let p : ℝ := 9 / 5
  let m := upperCapMass u
  let f := lawRightClip p L 0 u
  let x := endpointPosition 1 u
  let t := endpointPosition (3 / 2) u
  let X := endpointPosition 6 u
  have hp : 1 < p := by norm_num [p]
  have hp₂ : p ≤ 2 := by norm_num [p]
  have hθ : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have hu₀ := (by norm_num : (0 : ℝ) < 2 / 3).trans_le hu.1
  have hm : 0 < m := upperCapMass_pos hu₀
  have hmE : m = adjacentCap p u := upperCapMass_eq u
  have hx : x = u + m := by unfold x endpointPosition; rw [endpointCubic_eq,one_mul]
  have ht : t = u + 3 * m / 2 := by unfold t endpointPosition; rw [endpointCubic_eq]; ring
  have hX : X = u + 6 * m := by unfold X endpointPosition; rw [endpointCubic_eq]
  have htL : 3 / 2 ≤ t := by
    have h := (endpointPosition_bounds (j := 3 / 2) (by norm_num) (by norm_num) hu).1
    change _ ≤ t at h
    norm_num [endpointPosition,endpointCubic] at h
    exact (by norm_num : (3 / 2 : ℝ) ≤ 38597 / 25725).trans h
  have htX : t ≤ X := by rw [ht,hX]; linarith only [hm]
  have hLast := pureRight_sixth_endpoint_neg ⟨(by norm_num : (1 / 2 : ℝ) ≤ 2 / 3).trans hu.1,hu.2⟩
  have hX₀ : pureRight p u X ≤ 0 := by rw [hX]; exact hLast.le
  have hTail₀ := followingTail_le_integral hp hp₂ hL hu₀ hm
  rw [← ht] at hTail₀
  have hTail : samplingTail f (u + m) m ≤ endpointTailBound u :=
    hTail₀.trans (pureRight_clipped_tail_le hL hu htL htX hX₀)
  have hQ := lawRightClip_quadratureData (u := u) hp.le hp₂ hL hθ hu₀
  have hS := hQ.summable u m le_rfl hm
  have hS' := hQ.summable (u + m) m (le_add_of_nonneg_right hm.le) hm
  have hSplit : samplingTail f u m = m * f x + samplingTail f (u + m) m := by
    rw [samplingTail_eq_shift,samplingHead_split _ _ _ hS',hx]
  have hF {z : ℝ} (hz : 0 < z) : f z = max 0 (pureRight p u z) := by
    unfold f lawRightClip
    rw [lawRightTest_zero hp.le hp₂ hL hz]
  have hNative : f u = pureRight p u u := by
    rw [hF hu₀,max_eq_right]
    exact (pureRight_native_pos hp.le hp₂ ((by norm_num : (1 / 2 : ℝ) ≤ 2 / 3).trans hu.1)).le
  have hFirst : m * f x = max 0 (endpointFirst u) := by
    rw [hF (by rw [hx]; positivity),mul_max_of_nonneg _ _ hm.le,mul_zero]
    unfold endpointFirst
    rw [endpointCubic_eq]
  have hBase : middleLawBase p L 0 u + m * f u = endpointNative u := by
    rw [hNative,middleLawBase_zero hp.le hp₂ hL]
    unfold endpointNative pureZ
    rw [endpointCubic_eq]
    dsimp only [p,m]
    ring
  change middleLawBase p L 0 u + samplingHead f u (adjacentCap p u) < _ ∧
    samplingTail f u (adjacentCap p u) < _
  rw [← hmE,samplingHead_split _ _ _ hS,← add_assoc,hBase,hSplit,hFirst]
  obtain ⟨hN,hNF,hT,hTF⟩ := pureAdjacent_endpoint_signed_bounds hu
  rcases le_or_gt (endpointFirst u) 0 with h | h
  · rw [max_eq_left h,zero_add]
    constructor <;> linarith only [hN,hT,hTail]
  · rw [max_eq_right h.le]
    constructor <;> linarith only [hNF,hTF,hTail]

end
end ACS12.GammaMeasure

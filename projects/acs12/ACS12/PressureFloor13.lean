import ACS12.PressureMomentEnvelope
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-! Convex pressure envelope at the two radial thresholds. -/
namespace ACS12.Pressure

open Set

noncomputable def floor13Reciprocal (R : ℝ) : ℝ := (1 / 13) * (13 * R / 2) ^ (5 / 9 : ℝ)

theorem pressure_floor13Reciprocal_bound {p q R y : ℝ} (hp : 9 / 5 ≤ p) (hQ : 0 < q)
    (hQ₁ : q ≤ 1 / 13) (hR : 1 ≤ R) (hy : 0 ≤ y) (h : y ^ p ≤ q ^ (p - 1) * R / 2) :
    y ≤ floor13Reciprocal R := by
  have hp₀ : 0 < p := by linarith only [hp]
  have hR₀ := zero_lt_one.trans_le hR
  let a : ℝ := 1 / 13
  let b : ℝ := 13 * R / 2
  have ha : 0 < a := by norm_num [a]
  have hb : 1 ≤ b := by dsimp only [b]; linarith only [hR]
  have hb₀ := zero_lt_one.trans_le hb
  have hQ' := Real.rpow_le_rpow hQ.le hQ₁ (by linarith only [hp] : 0 ≤ p - 1)
  have h' : y ^ p ≤ a ^ (p - 1) * (R / 2) := by
    exact h.trans (by dsimp only [a]; rw [← mul_div_assoc]; gcongr)
  have hPow : y ≤ a * b ^ (1 / p) := by
    have hC := Real.rpow_le_rpow (Real.rpow_nonneg hy _) h' (by positivity : 0 ≤ 1 / p)
    rw [← Real.rpow_mul hy,show p * (1 / p) = 1 by field_simp [hp₀.ne'],Real.rpow_one] at hC
    have hP : a ^ (p - 1) * (R / 2) = a ^ p * b := by
      rw [Real.rpow_sub_one ha.ne']
      dsimp only [a,b]
      ring
    rw [hP,Real.mul_rpow (Real.rpow_nonneg ha.le _) hb₀.le,
      ← Real.rpow_mul ha.le,show p * (1 / p) = 1 by field_simp [hp₀.ne'],Real.rpow_one] at hC
    exact hC
  have hpE : 1 / p ≤ 5 / 9 := (div_le_iff₀ hp₀).mpr (by linarith only [hp])
  exact hPow.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hb hpE) ha.le)

private theorem floor13Reciprocal_nonneg {R : ℝ} (hR : 0 ≤ R) : 0 ≤ floor13Reciprocal R := by
  unfold floor13Reciprocal
  positivity

private theorem floor13Reciprocal_mono {R S : ℝ} (hR : 0 ≤ R) (hRS : R ≤ S) :
    floor13Reciprocal R ≤ floor13Reciprocal S := by
  unfold floor13Reciprocal
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity) (by linarith only [hRS]) (by norm_num)) (by norm_num)

private theorem floor13Reciprocal_pow {R : ℝ} (hR : 0 ≤ R) :
    floor13Reciprocal R ^ 9 = (R / 2) ^ 5 / 13 ^ 4 := by
  unfold floor13Reciprocal
  rw [mul_pow,← Real.rpow_natCast ((13 * R / 2) ^ (5 / 9 : ℝ)) 9,← Real.rpow_mul (by positivity)]
  norm_num
  ring

private theorem floor13Reciprocal_first_lt : floor13Reciprocal (51 / 20) < 3 / 8 := by
  by_contra! h
  have h' := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 8) h 9
  rw [floor13Reciprocal_pow (by norm_num)] at h'
  norm_num at h'

private theorem floor13Reciprocal_last_lt : floor13Reciprocal 4 < 19 / 40 := by
  by_contra! h
  have h' := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 19 / 40) h 9
  rw [floor13Reciprocal_pow (by norm_num)] at h'
  norm_num at h'

private theorem cube_cap {u : ℝ} (hu : 1 ≤ u) (hU : u ^ 3 ≤ 3) : u ≤ 29 / 20 := by
  by_contra! h
  have h' := pow_lt_pow_left₀ h (by norm_num : (0 : ℝ) ≤ 29 / 20) (by decide : (3 : ℕ) ≠ 0)
  norm_num at h'
  linarith only [hU,h']

private theorem u_div_one_add_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    u / (1 + u) ≤ v / (1 + v) := by
  have hv := hu.trans huv
  apply (div_le_div_iff₀ (by positivity : 0 < 1 + u) (by positivity : 0 < 1 + v)).mpr
  linarith only [huv]

private theorem firstNeighbor_anti {y U : ℝ} (hy : 0 ≤ y) (hyU : y ≤ 3 / 8)
    (hU : 1 ≤ U) (hUc : U ^ 3 ≤ 3) :
    AntitoneOn (fun u => pressureNeighbor (9 / 5) u y) (Icc 1 U) := by
  let f (u : ℝ) := pressureNeighbor (9 / 5) u y
  let D (u : ℝ) := (1 + u) ^ (-14 / 5 : ℝ) *
    (-(9 / 5) + (u ^ 2 * (3 + u / 5) / (1 + u)) * y +
      (u ^ 5 * (3 + 11 * u / 10) / (1 + u) ^ 2) * y ^ 2)
  have hDer (u : ℝ) (hu : 1 ≤ u) : HasDerivAt f (D u) u := by
    have hT : 0 < 1 + u := by linarith only [hu]
    have hT' := ((hasDerivAt_id u).const_add 1)
    have hr (q : ℝ) := hT'.rpow_const (p := q) (Or.inl hT.ne')
    have hB := (((hasDerivAt_id u).pow 3).mul_const y).div hT' hT.ne'
    have hB' := ((hasDerivAt_const u (1 : ℝ)).add hB).add ((hB.pow 2).div_const 2)
    have h := ((hr (-(9 / 5))).mul hB').const_add (2 * y)
    convert h using 1
    dsimp only [D,id_eq,Pi.add_apply,Pi.div_apply,Pi.pow_apply]
    norm_num only [Nat.cast_ofNat,show (- (9 / 5 : ℝ) - 1) = -14 / 5 by norm_num,
      show (3 - 1 : ℕ) = 2 by decide,show (2 - 1 : ℕ) = 1 by decide,pow_one]
    have hE : (1 + u) ^ (- (9 / 5 : ℝ)) = (1 + u) ^ (-14 / 5 : ℝ) * (1 + u) := by
      rw [← Real.rpow_add_one hT.ne']
      congr 1
      norm_num
    rw [hE]
    field_simp [hT.ne']
    <;> ring
  have hD (u : ℝ) (hu : u ∈ Icc (1 : ℝ) U) : D u ≤ 0 := by
    have hu₀ : 0 ≤ u := zero_le_one.trans hu.1
    have huv := hu.2.trans (cube_cap hU hUc)
    let v : ℝ := 29 / 20
    have h := u_div_one_add_mono hu₀ huv
    have hE (z : ℝ) (hz : 0 ≤ z) :
        z ^ 2 * (3 + z / 5) / (1 + z) = z * (3 + z / 5) * (z / (1 + z)) := by
      field_simp [show 1 + z ≠ 0 by positivity]
    have hE' (z : ℝ) (hz : 0 ≤ z) :
        z ^ 5 * (3 + 11 * z / 10) / (1 + z) ^ 2 = z ^ 3 * (3 + 11 * z / 10) * (z / (1 + z)) ^ 2 := by
      field_simp [show 1 + z ≠ 0 by positivity]
    have hv : 0 ≤ v := by norm_num [v]
    have hA : u ^ 2 * (3 + u / 5) / (1 + u) ≤ 17 / 6 := by
      rw [hE _ hu₀]
      calc
        _ ≤ v * (3 + v / 5) * (v / (1 + v)) := by gcongr
        _ ≤ _ := by norm_num [v]
    have hB : u ^ 5 * (3 + 11 * u / 10) / (1 + u) ^ 2 ≤ 5 := by
      rw [hE' _ hu₀]
      calc
        _ ≤ v ^ 3 * (3 + 11 * v / 10) * (v / (1 + v)) ^ 2 := by gcongr
        _ ≤ _ := by norm_num [v]
    have hA' := mul_le_mul_of_nonneg_right hA hy
    have hB' := mul_le_mul_of_nonneg_right hB (sq_nonneg y)
    have hY := pow_le_pow_left₀ hy hyU 2
    unfold D
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith only [hA',hB',hyU,hY])
  exact antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    (fun u hu => (hDer u hu.1).continuousAt.continuousWithinAt)
    (fun u hu => (hDer u (show u ∈ Icc (1 : ℝ) U from interior_subset hu).1).differentiableAt.differentiableWithinAt)
    (fun u hu => by
      have hu' : u ∈ Icc (1 : ℝ) U := interior_subset hu
      rw [(hDer u hu'.1).deriv]
      exact hD u hu')

private noncomputable def branch13 (u R : ℝ) : ℝ :=
  R / 2 * max 1 (pressureNeighbor (9 / 5) u (floor13Reciprocal R))

private theorem branch13_first_lt {u : ℝ} (hu : 1 ≤ u) (hu₃ : u ^ 3 ≤ 3) :
    branch13 u (51 / 20) < 7 / 5 := by
  let y := floor13Reciprocal (51 / 20)
  have hy : 0 ≤ y := floor13Reciprocal_nonneg (by norm_num)
  have hyU : y ≤ 3 / 8 := floor13Reciprocal_first_lt.le
  have hN := (firstNeighbor_anti hy hyU hu hu₃) (show (1 : ℝ) ∈ Icc 1 u from ⟨le_rfl,hu⟩)
    (show u ∈ Icc 1 u from ⟨hu,le_rfl⟩) hu
  have hM := pressureNeighbor_mono (p := 9 / 5) (u := 1) le_rfl hy hyU
  have hP := GammaMeasure.fifth_rpow_upper (b := 2) (x := 23 / 80) (k := 9)
    (by norm_num) (by norm_num) (by norm_num)
  have hP' : (2 : ℝ) ^ (- (9 / 5) : ℝ) ≤ 23 / 80 := by convert hP.le using 1 <;> norm_num
  have hB : pressureNeighbor (9 / 5) 1 (3 / 8) ≤ 2290461 / 2088960 := by
    unfold pressureNeighbor
    norm_num only [one_pow,one_mul,show (1 + 1 : ℝ) = 2 by norm_num]
    nlinarith only [hP']
  unfold branch13
  rw [show (51 / 20 : ℝ) / 2 = 51 / 40 by norm_num]
  change 51 / 40 * max 1 (pressureNeighbor (9 / 5) u y) < 7 / 5
  rw [mul_max_of_nonneg _ _ (by norm_num : 0 ≤ (51 / 40 : ℝ))]
  apply max_lt (by norm_num)
  have hFinal := hN.trans (hM.trans hB)
  linarith only [hFinal]

private theorem branch13_last_lt {u : ℝ} (hu : 1 ≤ u) (hu₃ : u ^ 3 ≤ 3) :
    branch13 u 4 < 57 / 20 := by
  let y := floor13Reciprocal 4
  have hy : 0 ≤ y := floor13Reciprocal_nonneg (by norm_num)
  have hyU : y ≤ 19 / 40 := floor13Reciprocal_last_lt.le
  have hu₀ := zero_le_one.trans hu
  have huv : u ≤ 3 / 2 := (cube_cap hu hu₃).trans (by norm_num)
  have hT : 0 < 1 + u := by positivity
  have hC : (1 + u) ^ (1 / 5 : ℝ) ≤ 5 / 4 := by
    apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg hT.le _) (by norm_num : (0 : ℝ) ≤ 5 / 4)
      (z := (5 : ℝ)) (by norm_num)).mp
    rw [← Real.rpow_mul hT.le,show (1 / 5 : ℝ) * 5 = 1 by norm_num,Real.rpow_one]
    norm_num [← Real.rpow_natCast] 
    linarith only [huv]
  have hC₀ := GammaMeasure.fifth_rpow_upper (b := 2) (x := 3 / 10) (k := 9)
    (by norm_num) (by norm_num) (by norm_num)
  have hA : (1 + u) ^ (-(9 / 5) : ℝ) ≤ 3 / 10 :=
    (Real.rpow_le_rpow_of_nonpos (x := (2 : ℝ)) (y := 1 + u)
      (z := -(9 / 5)) (by norm_num) (by linarith only [hu]) (by norm_num)).trans
      (by convert hC₀.le using 1 <;> norm_num)
  have hrat := u_div_one_add_mono hu₀ huv
  have hB : u ^ 3 * (1 + u) ^ (-(14 / 5) : ℝ) ≤ 27 / 100 := by
    rw [show -(14 / 5 : ℝ) = 1 / 5 + (- (3 : ℝ)) by norm_num,Real.rpow_add hT,Real.rpow_neg hT.le]
    norm_num only [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,Real.rpow_natCast]
    calc
      _ = (u / (1 + u)) ^ 3 * (1 + u) ^ (1 / 5 : ℝ) := by
        generalize 1 + u = T
        rw [div_pow]
        have hE : T ^ (3 : ℝ) = T ^ (3 : ℕ) := by
          exact_mod_cast Real.rpow_natCast T 3
        rw [hE]
        change u ^ 3 * (T ^ (1 / 5 : ℝ) * (T ^ (3 : ℕ))⁻¹) =
          u ^ 3 / T ^ (3 : ℕ) * T ^ (1 / 5 : ℝ)
        calc
          _ = (u ^ 3 * (T ^ (3 : ℕ))⁻¹) * T ^ (1 / 5 : ℝ) := by ac_rfl
          _ = _ := by simp only [div_eq_mul_inv]
      _ ≤ ((3 / 2 : ℝ) / (1 + 3 / 2)) ^ 3 * (5 / 4) := by gcongr
      _ ≤ _ := by norm_num
  have hE : u ^ 6 / 2 * (1 + u) ^ (-(19 / 5) : ℝ) ≤ 3 / 16 := by
    rw [show -(19 / 5 : ℝ) = 1 / 5 + (- (4 : ℝ)) by norm_num,Real.rpow_add hT,Real.rpow_neg hT.le]
    norm_num only [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,Real.rpow_natCast]
    calc
      _ = (u / (1 + u)) ^ 4 * u ^ 2 / 2 * (1 + u) ^ (1 / 5 : ℝ) := by
        generalize 1 + u = T
        rw [div_pow]
        have hE : T ^ (4 : ℝ) = T ^ (4 : ℕ) := by
          exact_mod_cast Real.rpow_natCast T 4
        rw [hE]
        change u ^ 6 / 2 * (T ^ (1 / 5 : ℝ) * (T ^ (4 : ℕ))⁻¹) =
          u ^ 4 / T ^ (4 : ℕ) * u ^ 2 / 2 * T ^ (1 / 5 : ℝ)
        have hPow : u ^ 6 = u ^ 4 * u ^ 2 := by ring
        calc
          _ = (u ^ 4 * u ^ 2) / 2 * (T ^ (1 / 5 : ℝ) * (T ^ (4 : ℕ))⁻¹) := by rw [← hPow]
          _ = _ := by
            simp only [div_eq_mul_inv]
            generalize (T ^ (4 : ℕ))⁻¹ = d
            ring
      _ ≤ ((3 / 2 : ℝ) / (1 + 3 / 2)) ^ 4 * (3 / 2) ^ 2 / 2 * (5 / 4) := by gcongr
      _ ≤ _ := by norm_num
  have hNE : pressureNeighbor (9 / 5) u y = 2 * y + (1 + u) ^ (-(9 / 5) : ℝ) +
      (u ^ 3 * (1 + u) ^ (-(14 / 5) : ℝ)) * y +
      (u ^ 6 / 2 * (1 + u) ^ (-(19 / 5) : ℝ)) * y ^ 2 := by
    unfold pressureNeighbor
    have hE₁ : (1 + u) ^ (-(14 / 5) : ℝ) = (1 + u) ^ (-(9 / 5) : ℝ) / (1 + u) := by
      rw [show -(14 / 5 : ℝ) = -(9 / 5) - 1 by norm_num,Real.rpow_sub hT,Real.rpow_one]
    have hE₂ : (1 + u) ^ (-(19 / 5) : ℝ) = (1 + u) ^ (-(9 / 5) : ℝ) / (1 + u) ^ 2 := by
      rw [show -(19 / 5 : ℝ) = -(9 / 5) - 2 by norm_num,Real.rpow_sub hT,Real.rpow_two]
    rw [hE₁,hE₂,div_pow]
    generalize 1 + u = T
    simp only [div_eq_mul_inv]
    ring
  have hM := mul_le_mul hB hyU hy (by norm_num)
  have hM' := mul_le_mul hE (pow_le_pow_left₀ hy hyU 2) (sq_nonneg y) (by norm_num)
  unfold branch13
  rw [show (4 : ℝ) / 2 = 2 by norm_num]
  change 2 * max 1 (pressureNeighbor (9 / 5) u y) < 57 / 20
  rw [mul_max_of_nonneg _ _ (by norm_num : 0 ≤ (2 : ℝ))]
  exact max_lt (by norm_num) (by linarith only [hNE,hA,hM,hM',hyU])

private theorem branch13_convex {u : ℝ} (hu : 1 ≤ u) : ConvexOn ℝ (Ici 0) (branch13 u) := by
  let a : ℝ := (1 / 13) * (13 / 2 : ℝ) ^ (5 / 9 : ℝ)
  let b := (1 + u) ^ (- (9 / 5 : ℝ))
  let c := u ^ 3 / (1 + u)
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hV : ConvexOn ℝ (Ici 0) (fun R : ℝ =>
      (b / 2) * R + ((2 + b * c) * a / 2) * R ^ (14 / 9 : ℝ) +
        (b * c ^ 2 * a ^ 2 / 4) * R ^ (19 / 9 : ℝ)) := by
    have h₀ := ((convexOn_id (convex_Ici (0 : ℝ))).smul (show 0 ≤ b / 2 by positivity))
    have h₁ := (convexOn_rpow (by norm_num : (1 : ℝ) ≤ 14 / 9)).smul
      (show 0 ≤ (2 + b * c) * a / 2 by positivity)
    have h₂ := (convexOn_rpow (by norm_num : (1 : ℝ) ≤ 19 / 9)).smul
      (show 0 ≤ b * c ^ 2 * a ^ 2 / 4 by positivity)
    simpa only [id_eq,Pi.smul_apply,smul_eq_mul,Pi.add_apply] using (h₀.add h₁).add h₂
  have hV' : ConvexOn ℝ (Ici 0) (fun R : ℝ => R / 2) := by
    convert (convexOn_id (convex_Ici (0 : ℝ))).smul (by norm_num : (0 : ℝ) ≤ 1 / 2) using 1
    funext R
    simp only [Pi.smul_apply,id_eq,smul_eq_mul]
    ring
  apply (hV'.sup hV).congr
  intro R hR
  have hR₀ : 0 ≤ R := hR
  have hY : floor13Reciprocal R = a * R ^ (5 / 9 : ℝ) := by
    unfold floor13Reciprocal a
    rw [show 13 * R / 2 = (13 / 2) * R by ring,Real.mul_rpow (by norm_num) hR₀]
    ring
  have h₁ : R * R ^ (5 / 9 : ℝ) = R ^ (14 / 9 : ℝ) := by
    conv_lhs => left; rw [← Real.rpow_one R]
    rw [← Real.rpow_add' hR₀ (by norm_num : (1 : ℝ) + 5 / 9 ≠ 0)]
    norm_num
  have h₂ : R * (R ^ (5 / 9 : ℝ)) ^ 2 = R ^ (19 / 9 : ℝ) := by
    rw [← Real.rpow_natCast (R ^ (5 / 9 : ℝ)) 2,← Real.rpow_mul hR₀]
    norm_num only [Nat.cast_ofNat,show (5 / 9 : ℝ) * 2 = 10 / 9 by norm_num]
    conv_lhs => left; rw [← Real.rpow_one R]
    rw [← Real.rpow_add' hR₀ (by norm_num : (1 : ℝ) + 10 / 9 ≠ 0)]
    norm_num
  have hB : R / 2 * pressureNeighbor (9 / 5) u (floor13Reciprocal R) =
      (b / 2) * R + ((2 + b * c) * a / 2) * R ^ (14 / 9 : ℝ) +
        (b * c ^ 2 * a ^ 2 / 4) * R ^ (19 / 9 : ℝ) := by
    rw [hY,← h₁,← h₂]
    unfold pressureNeighbor b c
    ring
  change max _ _ = branch13 u R
  unfold branch13
  rw [mul_max_of_nonneg _ _ (show 0 ≤ R / 2 by positivity),mul_one,hB]

theorem pressureFloor13_branch_lt {u R : ℝ} (hu : 1 ≤ u) (hu₃ : u ^ 3 ≤ 3)
    (hR : 0 ≤ R) (hR₄ : R ≤ 4) :
    R / 2 * max 1 (pressureNeighbor (9 / 5) u (floor13Reciprocal R)) <
      max (7 / 5) (R - 23 / 20) := by
  change branch13 u R < _
  by_cases h : R ≤ 51 / 20
  · have hY := floor13Reciprocal_mono hR h
    have hB := pressureNeighbor_mono (p := 9 / 5) hu (floor13Reciprocal_nonneg hR) hY
    have hM : branch13 u R ≤ branch13 u (51 / 20) := by
      unfold branch13
      exact mul_le_mul (by linarith only [h]) (max_le_max le_rfl hB) (by positivity) (by norm_num)
    exact (hM.trans_lt (branch13_first_lt hu hu₃)).trans_le (le_max_left _ _)
  · let x : ℝ := (4 - R) / (4 - 51 / 20)
    let y : ℝ := (R - 51 / 20) / (4 - 51 / 20)
    have hx : 0 ≤ x := div_nonneg (sub_nonneg.mpr hR₄) (by norm_num)
    have hy : 0 < y := by dsimp only [y]; exact div_pos (sub_pos.mpr (lt_of_not_ge h)) (by norm_num)
    have hxy : x + y = 1 := by dsimp only [x,y]; ring
    have hE : x * (51 / 20) + y * 4 = R := by dsimp only [x,y]; ring
    have hC := (branch13_convex hu).2
      (show (51 / 20 : ℝ) ∈ Ici 0 from mem_Ici.mpr (by norm_num))
      (show (4 : ℝ) ∈ Ici 0 from mem_Ici.mpr (by norm_num)) hx hy.le hxy
    simp only [smul_eq_mul,hE] at hC
    have hF := mul_le_mul_of_nonneg_left (branch13_first_lt hu hu₃).le hx
    have hL := mul_lt_mul_of_pos_left (branch13_last_lt hu hu₃) hy
    have hStrict : branch13 u R < R - 23 / 20 := by
      have hK : x * (7 / 5) + y * (57 / 20) = R - 23 / 20 := by
        dsimp only [x,y]
        ring
      linarith only [hC,hF,hL,hK]
    exact hStrict.trans_le (le_max_right _ _)

end ACS12.Pressure


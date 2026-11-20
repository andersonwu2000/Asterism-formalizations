import ACS12.ShiftedPowerTail
import ACS12.JointFarValue
import ACS12.JointLowerKnownTail

/-! Complete left-row third bound on the entire middle exponent band. -/
namespace ACS12.GammaMeasure

open Set

private theorem farLeft_two_mono :
    MonotoneOn (fun p : ℝ => p * (p + 1) * (15 / 8 : ℝ) ^ (-p - 2)) (Icc 1 (9 / 5)) := by
  let x : ℝ := 15 / 8
  let f (p : ℝ) := p * (p + 1) * x ^ (-p - 2)
  have hx : 0 < x := by norm_num [x]
  have hD (p : ℝ) (hp : 0 < p) :
      HasDerivAt f (f p * (p⁻¹ + (p + 1)⁻¹ - Real.log x)) p := by
    have hI := hasDerivAt_id p
    have hP := (((hI.neg.sub_const 2).mul_const (Real.log x))).exp
    have hE : (fun p : ℝ => Real.exp ((-p - 2) * Real.log x)) =
        fun p => x ^ (-p - 2) := by
      funext q
      rw [Real.rpow_def_of_pos hx,mul_comm]
    have hQ : HasDerivAt (fun p => x ^ (-p - 2)) (-(Real.log x) * x ^ (-p - 2)) p := by
      rw [← hE]
      rw [Real.rpow_def_of_pos hx,mul_comm (Real.log x) (-p - 2)]
      convert hP using 1
      change -Real.log x * Real.exp ((-p - 2) * Real.log x) =
        Real.exp ((-p - 2) * Real.log x) * (-1 * Real.log x)
      ring
    convert ((hI.mul (hI.add_const 1)).mul hQ) using 1
    simp only [f,id_eq,mul_one,Pi.mul_apply]
    field_simp [hp.ne',(add_pos hp zero_lt_one).ne']
    ring
  have hlog : Real.log x < 7 / 10 := by
    have h := Real.log_le_log hx (show x ≤ 2 by norm_num [x])
    linarith only [h,Real.log_two_lt_d9]
  change MonotoneOn f _
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · intro p hp
    exact (hD p (zero_lt_one.trans_le hp.1)).continuousAt.continuousWithinAt
  · intro p hp
    exact (hD p (zero_lt_one.trans_le (interior_subset hp).1)).differentiableAt.differentiableWithinAt
  · intro p hp
    have hpI := interior_subset hp
    have hp₀ := zero_lt_one.trans_le hpI.1
    rw [(hD p hp₀).deriv]
    have ha := inv_anti₀ hp₀ hpI.2
    have hb := inv_anti₀ (add_pos hp₀ zero_lt_one)
      (show p + 1 ≤ 9 / 5 + 1 from add_le_add hpI.2 le_rfl)
    have hN : 0 ≤ p⁻¹ + (p + 1)⁻¹ - Real.log x := by
      norm_num at ha hb
      linarith only [ha,hb,hlog]
    exact mul_nonneg (by unfold f; positivity) hN

private theorem farLeft_three_mono :
    MonotoneOn (fun p : ℝ => p * (p + 1) * (p + 2) * (15 / 8 : ℝ) ^ (-p - 3)) (Icc 1 (9 / 5)) := by
  have hE (p : ℝ) : p * (p + 1) * (p + 2) * (15 / 8 : ℝ) ^ (-p - 3) =
      (p * (p + 1) * (15 / 8 : ℝ) ^ (-p - 2)) * ((p + 2) / (15 / 8)) := by
    rw [show -p - 3 = -p - 2 - 1 by ring,Real.rpow_sub_one (by norm_num : (15 / 8 : ℝ) ≠ 0)]
    ring
  intro p hp q hq hpq
  change p * (p + 1) * (p + 2) * (15 / 8 : ℝ) ^ (-p - 3) ≤
    q * (q + 1) * (q + 2) * (15 / 8 : ℝ) ^ (-q - 3)
  rw [hE,hE]
  exact mul_le_mul (farLeft_two_mono hp hq hpq)
    (div_le_div_of_nonneg_right (add_le_add hpq le_rfl) (by norm_num))
    (by have : 1 ≤ p := hp.1; positivity) (by have : 1 ≤ q := hq.1; positivity)

theorem farLeft_third_lt {p δ : ℝ} (hp : 1 ≤ p) (hpP : p ≤ 9 / 5)
    (_hδ : 0 ≤ δ) (hδU : δ ≤ 1 / 8) :
    -lowerKnownSum 3 p (1 - δ) < 3 / 2 := by
  let x : ℝ := 15 / 8
  let q := p + 3
  let X := 2 - δ
  have hx : 1 ≤ x := by norm_num [x]
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hX : x ≤ X := by unfold x X; linarith only [hδU]
  have hq : 1 < q := by unfold q; linarith only [hp]
  have hq₀ := zero_lt_one.trans hq
  have hT : shiftedPowerTail q X ≤ shiftedPowerTail q x := by
    unfold shiftedPowerTail
    apply (shiftedPowerTail_summable hq (hx.trans hX)).tsum_le_tsum _
      (shiftedPowerTail_summable hq hx)
    intro n
    exact Real.rpow_le_rpow_of_nonpos (add_pos_of_pos_of_nonneg hx₀ (Nat.cast_nonneg _))
      (add_le_add hX le_rfl) (neg_nonpos.mpr hq₀.le)
  have hE : -lowerKnownSum 3 p (1 - δ) = p * (p + 1) * (p + 2) * shiftedPowerTail q X := by
    unfold lowerKnownSum shiftedPowerTail
    change -(∑' j : ℕ, -(p * (p + 1) * (p + 2)) * (1 + (j : ℝ) + (1 - δ)) ^ (-p - 3)) = _
    rw [tsum_mul_left,neg_mul,neg_neg]
    congr 1
    apply tsum_congr
    intro n
    rw [show 1 + (n : ℝ) + (1 - δ) = X + (n : ℝ) by unfold X; ring,show -p - 3 = -q by unfold q; ring]
  have hGuard : (1 / 2 : ℝ) + q / (12 * x) ≤ 1 := by
    apply (le_of_mul_le_mul_right _ (show 0 < 12 * x by positivity))
    unfold q x
    norm_num
    linarith only [hpP]
  have hB := (shiftedPowerTail_bernoulli hq hx).2
  have hT' : shiftedPowerTail q x ≤ x ^ (-q) + x ^ (1 - q) / (q - 1) := by
    have hB' := mul_le_mul_of_nonneg_right hGuard (Real.rpow_nonneg hx₀.le (-q))
    rw [Real.rpow_sub_one hx₀.ne'] at hB
    simp only [one_mul] at hB'
    have hEq : q * (x ^ (-q) / x) / 12 = (q / (12 * x)) * x ^ (-q) := by ring
    rw [hEq] at hB
    linarith only [hB,hB']
  have hK := mul_le_mul_of_nonneg_left (hT.trans hT') (show 0 ≤ p * (p + 1) * (p + 2) by positivity)
  have hQ : p * (p + 1) * (p + 2) * (x ^ (-q) + x ^ (1 - q) / (q - 1)) =
      p * (p + 1) * (p + 2) * x ^ (-p - 3) + p * (p + 1) * x ^ (-p - 2) := by
    unfold q
    rw [show -(p + 3) = -p - 3 by ring,show 1 - (p + 3) = -p - 2 by ring,
      show p + 3 - 1 = p + 2 by ring,mul_add]
    field_simp [(show 0 < p + 2 by positivity).ne']
  rw [hQ,← hE] at hK
  have hpI : p ∈ Icc (1 : ℝ) (9 / 5) := ⟨hp,hpP⟩
  have hP : (9 / 5 : ℝ) ∈ Icc (1 : ℝ) (9 / 5) := by norm_num
  have hA := farLeft_two_mono hpI hP hpP
  have hB' := farLeft_three_mono hpI hP hpP
  have hPwr : (15 / 8 : ℝ) ^ (-(9 : ℝ) / 5) < 323 / 1000 :=
    fifth_rpow_upper (k := 9) (by norm_num) (by norm_num) (by norm_num)
  have hC (k : ℕ) : (15 / 8 : ℝ) ^ (-(9 / 5 : ℝ) - (k : ℝ)) =
      (15 / 8 : ℝ) ^ (-(9 : ℝ) / 5) / (15 / 8 : ℝ) ^ k := by
    rw [Real.rpow_sub_natCast (by norm_num),neg_div]
  simp only at hA hB'
  rw [← Nat.cast_ofNat (R := ℝ) (n := 2),hC 2] at hA
  rw [← Nat.cast_ofNat (R := ℝ) (n := 3),hC 3] at hB'
  unfold x at hK
  norm_num at hA hB'
  nlinarith only [hK,hA,hB',hPwr]

end ACS12.GammaMeasure


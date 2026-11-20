import ACS12.JointLogEndpoint
import ACS12.JointCanonicalMoments

/-! Whole-band first moments and the complete P curvature in W22. -/
namespace ACS12.GammaMeasure

open Set

noncomputable def pureZPrime (p : ℝ) : ℝ :=
  powerTail (p + 1) 1 - p * powerLogTail (p + 1) 1 1

noncomputable def pureZSecond (p : ℝ) : ℝ :=
  p * powerLogTail (p + 1) 2 1 - 2 * powerLogTail (p + 1) 1 1

theorem pureZPrime_derivative {p : ℝ} (hp : 0 < p) : HasDerivAt pureZPrime (pureZSecond p) p :=
  pureZ_second_hasDerivAt hp

theorem pureZ_derivative {p : ℝ} (hp : 0 < p) : HasDerivAt pureZ (pureZPrime p) p :=
  pureZ_hasDerivAt hp

theorem pureZPrime_one_bounds : (7069 / 10000 : ℝ) < pureZPrime 1 ∧ pureZPrime 1 < 708 / 1000 := by
  have hZ := pureZ_one_gt
  have hU : pureZ 1 < (1645 / 1000 : ℝ) := by
    rw [pureZ_one_eq]
    have h := pow_lt_pow_left₀ Real.pi_lt_d6 Real.pi_pos.le (by decide : 2 ≠ 0)
    linarith only [h]
  have hL := logMoment_two_bounds
  norm_num [pureZ] at hZ hU
  norm_num [pureZPrime]
  exact ⟨by linarith only [hZ,hL.2],by linarith only [hU,hL.1]⟩

private theorem pureZPrime_mono : MonotoneOn pureZPrime (Icc 1 (9 / 5)) := by
  have hD (p : ℝ) (hp : p ∈ Icc (1 : ℝ) (9 / 5)) := pureZPrime_derivative (zero_lt_one.trans_le hp.1)
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · exact fun p hp => (hD p hp).continuousAt.continuousWithinAt
  · exact fun p hp => (hD p (interior_subset hp)).differentiableAt.differentiableWithinAt
  · intro p hp
    have hp' : p ∈ Icc (1 : ℝ) (9 / 5) := interior_subset hp
    rw [(hD p hp').deriv]
    exact (by norm_num : (0 : ℝ) ≤ 37 / 500).trans (pureZ_second_bounds hp'.1 hp'.2).1.le

theorem pureZPrime_bounds {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    (7 / 10 : ℝ) < pureZPrime p ∧ pureZPrime p < 708 / 1000 + (1 / 8) * (p - 1) := by
  have h1 : (1 : ℝ) ∈ Icc 1 (9 / 5) := ⟨le_rfl,by norm_num⟩
  have hM := pureZPrime_mono h1 ⟨hp,hP⟩ hp
  let f (p : ℝ) := pureZPrime p - (p - 1) / 8
  have hD (p : ℝ) (hp : p ∈ Icc (1 : ℝ) (9 / 5)) :
      HasDerivAt f (pureZSecond p - 1 / 8) p := by
    simpa only [f] using (pureZPrime_derivative (zero_lt_one.trans_le hp.1)).sub
      (((hasDerivAt_id p).sub_const 1).div_const 8)
  have hF : AntitoneOn f (Icc 1 (9 / 5)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · exact fun p hp => (hD p hp).continuousAt.continuousWithinAt
    · exact fun p hp => (hD p (interior_subset hp)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Icc (1 : ℝ) (9 / 5) := interior_subset hx
      rw [(hD x hx').deriv]
      exact sub_nonpos.mpr (pureZ_second_bounds hx'.1 hx'.2).2
  have hB := hF h1 ⟨hp,hP⟩ hp
  dsimp only [f] at hB
  exact ⟨by linarith only [hM,pureZPrime_one_bounds.1],by linarith only [hB,pureZPrime_one_bounds.2]⟩

private theorem pureZ_convex : ConvexOn ℝ (Icc 1 (9 / 5)) pureZ := by
  have hD (p : ℝ) (hp : p ∈ Icc (1 : ℝ) (9 / 5)) := pureZ_derivative (zero_lt_one.trans_le hp.1)
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
    (fun p hp => (hD p hp).continuousAt.continuousWithinAt)
    (fun p hp => (hD p (interior_subset hp)).hasDerivWithinAt)
    (fun p hp => (pureZPrime_derivative (zero_lt_one.trans_le (show p ∈ Icc (1 : ℝ) (9 / 5) from interior_subset hp).1)).hasDerivWithinAt)
  intro p hp
  have hp' : p ∈ Icc (1 : ℝ) (9 / 5) := interior_subset hp
  exact (by norm_num : (0 : ℝ) ≤ 37 / 500).trans (pureZ_second_bounds hp'.1 hp'.2).1.le

theorem pureZ_band_bounds {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    (16449 / 10000 : ℝ) + (7 / 10) * (p - 1) < pureZ p ∧
    pureZ p < 1645 / 1000 + (3 / 4) * (p - 1) := by
  let f (q : ℝ) := pureZ q - (7 / 10) * (q - 1)
  have hD (q : ℝ) (hq : q ∈ Icc (1 : ℝ) (9 / 5)) : HasDerivAt f (pureZPrime q - 7 / 10) q := by
    simpa only [f,mul_one] using (pureZ_derivative (zero_lt_one.trans_le hq.1)).sub
      (((hasDerivAt_id q).sub_const 1).const_mul (7 / 10))
  have hM : MonotoneOn f (Icc 1 (9 / 5)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun q hq => (hD q hq).continuousAt.continuousWithinAt
    · exact fun q hq => (hD q (interior_subset hq)).differentiableAt.differentiableWithinAt
    · intro q hq
      have hq' : q ∈ Icc (1 : ℝ) (9 / 5) := interior_subset hq
      rw [(hD q hq').deriv]
      exact sub_nonneg.mpr (pureZPrime_bounds hq'.1 hq'.2).1.le
  have h₁ : (1 : ℝ) ∈ Icc 1 (9 / 5) := ⟨le_rfl,by norm_num⟩
  have h₂ : (9 / 5 : ℝ) ∈ Icc 1 (9 / 5) := ⟨by norm_num,le_rfl⟩
  constructor
  · have h := hM h₁ ⟨hp,hP⟩ hp
    dsimp only [f] at h
    linarith only [h,pureZ_one_gt]
  · let t := (5 / 4) * (p - 1)
    have ht : 0 ≤ t := by dsimp only [t]; linarith only [hp]
    have ht' : t ≤ 1 := by dsimp only [t]; linarith only [hP]
    have h := pureZ_convex.2 h₁ h₂ (sub_nonneg.mpr ht') ht (sub_add_cancel 1 t)
    have hArg : (1 - t) • (1 : ℝ) + t • (9 / 5 : ℝ) = p := by
      simp only [smul_eq_mul,t]
      ring
    rw [hArg] at h
    simp only [smul_eq_mul] at h
    have hOne : pureZ 1 < (1645 / 1000 : ℝ) := by
      rw [pureZ_one_eq]
      have h := pow_lt_pow_left₀ Real.pi_lt_d6 Real.pi_pos.le (by decide : 2 ≠ 0)
      linarith only [h]
    have hP' : pureZ (9 / 5) < (2245 / 1000 : ℝ) := pureZ_upperEndpoint_upper.trans (by norm_num)
    have hPos : 0 < (1 - t) * ((1645 / 1000) - pureZ 1) +
        t * ((2245 / 1000) - pureZ (9 / 5)) := by
      rcases lt_or_eq_of_le ht' with hT | hT
      · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hT) (sub_pos.mpr hOne))
          (mul_nonneg ht (sub_nonneg.mpr hP'.le))
      · rw [hT]
        simpa only [sub_self,zero_mul,one_mul,zero_add] using sub_pos.mpr hP'
    have hEq : (1 - t) * (1645 / 1000) + t * (2245 / 1000) =
        1645 / 1000 + (3 / 4) * (p - 1) := by dsimp only [t]; ring
    linarith only [h,hPos,hEq]

theorem pureP_eq (p : ℝ) : pureP p = (p - 1) * pureZ p := by
  unfold pureP pureZ
  ring

noncomputable def purePPrime (p : ℝ) : ℝ := pureZ p + (p - 1) * pureZPrime p

noncomputable def purePSecond (p : ℝ) : ℝ := 2 * pureZPrime p + (p - 1) * pureZSecond p

theorem pureP_derivative {p : ℝ} (hp : 0 < p) : HasDerivAt pureP (purePPrime p) p := by
  rw [show pureP = (fun p => (p - 1) * pureZ p) from funext pureP_eq]
  simpa only [purePPrime,one_mul] using ((hasDerivAt_id p).sub_const 1).mul (pureZ_derivative hp)

theorem purePPrime_derivative {p : ℝ} (hp : 0 < p) : HasDerivAt purePPrime (purePSecond p) p := by
  convert (pureZ_derivative hp).add (((hasDerivAt_id p).sub_const 1).mul (pureZPrime_derivative hp)) using 1
  simp only [purePSecond,one_mul,id_eq]
  ring

theorem purePPrime_bounds {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    (16449 / 10000 : ℝ) + (7 / 5) * (p - 1) < purePPrime p ∧
    purePPrime p < 1645 / 1000 + (729 / 500) * (p - 1) + (1 / 8) * (p - 1) ^ 2 := by
  obtain ⟨hZ,hZ'⟩ := pureZ_band_bounds hp hP
  obtain ⟨hD,hD'⟩ := pureZPrime_bounds hp hP
  have ht := sub_nonneg.mpr hp
  have hA := mul_le_mul_of_nonneg_left hD.le ht
  have hB := mul_le_mul_of_nonneg_left hD'.le ht
  unfold purePPrime
  exact ⟨by nlinarith only [hZ,hA],by nlinarith only [hZ',hB]⟩

theorem purePSecond_bounds {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    (7 / 5 : ℝ) < purePSecond p ∧ purePSecond p < 429 / 250 := by
  obtain ⟨hD,hD'⟩ := pureZPrime_bounds hp hP
  obtain ⟨hE,hE'⟩ := pureZ_second_bounds hp hP
  change pureZSecond p ≤ 1 / 8 at hE'
  have ht := sub_nonneg.mpr hp
  have hA : 0 ≤ (p - 1) * pureZSecond p :=
    mul_nonneg ht ((by norm_num : (0 : ℝ) ≤ 37 / 500).trans hE.le)
  have hB := mul_le_mul_of_nonneg_left hE' ht
  unfold purePSecond
  exact ⟨by linarith only [hD,hA],by linarith only [hD',hB,hP]⟩

end ACS12.GammaMeasure

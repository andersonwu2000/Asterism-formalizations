import ACS12.JointLowerHeadZero
import ACS12.JointLowerHeadOne
import ACS12.JointDiagonalQuotient

/-! The complete third derivative along the original lower diagonal. -/
namespace ACS12.GammaMeasure

open Set CenteredCircle.AllN

private noncomputable def lowerNativePolynomial (k : ℕ) (p d : ℝ) : ℝ :=
  let a := (6 / 25) * p
  let b := 1 + a - pureZ p
  match k with
  | 0 => (1 - d) * (b - a * d ^ 2)
  | 1 => -b - 2 * a * d + 3 * a * d ^ 2
  | 2 => -2 * a + 6 * a * d
  | _ => 6 * a

private theorem lowerNativePolynomial_deriv {k : ℕ} (hk : k < 3) (p d : ℝ) :
    HasDerivAt (lowerNativePolynomial k p) (lowerNativePolynomial (k + 1) p d) d := by
  let a := (6 / 25) * p
  let b := 1 + a - pureZ p
  have h := hasDerivAt_id d
  interval_cases k
  · convert (h.const_sub 1).mul (((h.pow 2).const_mul a).const_sub b) using 1
    simp only [lowerNativePolynomial,a,b,Pi.pow_apply,id_eq,mul_one]
    ring
  · convert (((h.const_mul (-(2 * a))).sub_const b).add ((h.pow 2).const_mul (3 * a))) using 1
    · funext x
      unfold lowerNativePolynomial a b
      simp only [Pi.pow_apply,id_eq,Pi.add_apply]
      ring
    · simp only [lowerNativePolynomial,a,id_eq,mul_one]
      ring
  · convert ((h.const_mul (6 * a)).sub_const (2 * a)) using 1
    · funext x
      unfold lowerNativePolynomial a
      simp only [id_eq]
      ring
    · change 6 * ((6 / 25) * p) = 6 * a * 1
      simp only [a,mul_one]

private noncomputable def lowerAdjacentResponse (k : ℕ) (p d : ℝ) : ℝ :=
  let known := match k with
    | 0 => lowerDiagonalKnown p d
    | 1 => lowerDiagonalKnownD1 p d
    | 2 => lowerDiagonalKnownD2 p d
    | _ => lowerKnownFiniteD3 p d - lowerKnownSum 3 p (1 - d)
  let right := match k with
    | 0 => lowerDiagonalRight p d
    | 1 => lowerDiagonalRightD1 p d
    | 2 => lowerDiagonalRightD2 p d
    | _ => p * (p + 1) * lowerDiagonalMass d ^ (-p - 2) *
      lowerRightResponseTotal p (lowerDiagonalRatio d)
  known + right

private theorem lowerAdjacentResponse_deriv {k : ℕ} (hk : k < 3) {p d : ℝ}
    (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hd : d ∈ Icc (0 : ℝ) (1 / 8)) :
    HasDerivAt (lowerAdjacentResponse k p) (lowerAdjacentResponse (k + 1) p d) d := by
  interval_cases k
  · exact (lowerDiagonalKnown_deriv1 hp hp₂ hd.1 hd.2).add (lowerDiagonalRight_deriv1 hp hp₂ hd.1 hd.2)
  · exact (lowerDiagonalKnown_deriv2 hp hp₂ hd.1 hd.2).add (lowerDiagonalRight_deriv2 hp hp₂ hd.1 hd.2)
  · exact (lowerDiagonalKnown_deriv3 hp hp₂ hd.1 hd.2).add (lowerDiagonalRight_deriv3 hp hp₂ hd.1 hd.2)

noncomputable def lowerDiagonalResponse (k : ℕ) (p d : ℝ) : ℝ :=
  lowerNativePolynomial k p d + lowerNativeStream k p d +
    (jointPureLambda - jointCanonicalMu) * lowerAdjacentResponse k p d +
    jointCanonicalMu * lowerSourcePair k p d

theorem lowerDiagonalResponse_deriv {k : ℕ} (hk : k < 3) {p d : ℝ}
    (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hd : d ∈ Icc (0 : ℝ) (1 / 8)) :
    HasDerivAt (lowerDiagonalResponse k p) (lowerDiagonalResponse (k + 1) p d) d := by
  have hd' : d ∈ Ioo (-(1 / 4) : ℝ) (1 / 4) := ⟨by linarith only [hd.1],by linarith only [hd.2]⟩
  exact (((lowerNativePolynomial_deriv hk p d).add (lowerNativeStream_hasDerivAt hk hp hd')).add
    ((lowerAdjacentResponse_deriv hk hp hp₂ hd).const_mul (jointPureLambda - jointCanonicalMu))).add
    ((lowerSourcePair_deriv hk hp hp₂ hd.1 hd.2).const_mul jointCanonicalMu)

theorem lowerDiagonalResponse_zero_eq {p L d : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hL : 0 < L)
    (hd : d ∈ Icc (0 : ℝ) (1 / 8)) :
    lowerDiagonalResponse 0 p d = jointPureValue p L (1 - d) (lowerDiagonalMass d)
      (lowerDiagonalMass d) jointCanonicalMu := by
  let m := lowerDiagonalMass d
  let u := 1 - d
  have hm : 0 < m := by unfold m lowerDiagonalMass; linarith only [hd.2]
  have hu : 0 < u := by unfold u; linarith only [hd.2]
  have hN : adjacentLawSignedValue p L 0 u m = lowerNativePolynomial 0 p d + lowerNativeStream 0 p d := by
    rw [adjacentLawSignedValue,middleLawBase_zero hp hp₂ hL,lawRightTest_zero hp hp₂ hL hu]
    have hSeries : Summable (fun j : ℕ => pureRight p u (u + (j : ℝ) * m)) := by
      obtain ⟨A,hA,hB⟩ := lowerNativeSite_dominated (k := 0) (by decide) hp
      have hd' : d ∈ Icc (-(1 / 4) : ℝ) (1 / 4) := ⟨by linarith only [hd.1],by linarith only [hd.2]⟩
      have h := (powerTail_summable (q := 2) (by norm_num) 1).mul_left A
      have hD : Summable (fun j : ℕ => lowerNativeSite 0 p (j : ℝ) d) :=
        Summable.of_norm_bounded h (fun j => by simpa only [Nat.cast_one] using hB j d hd')
      have hE (j : ℕ) : pureRight p u (u + (j : ℝ) * m) = m⁻¹ * lowerNativeSite 0 p (j : ℝ) d := by
        rw [lowerNativeSite_zero]
        change _ = m⁻¹ * (m * _)
        rw [inv_mul_cancel_left₀ hm.ne']
      exact (hD.mul_left m⁻¹).congr (fun j => (hE j).symm)
    have hE : samplingTail (lawRightTest p L 0 u) u m = m * ∑' j : ℕ, pureRight p u (u + ((j + 1 : ℕ) : ℝ) * m) := by
      unfold samplingTail
      congr 1
      apply tsum_congr
      intro j
      exact lawRightTest_zero hp hp₂ hL (by positivity)
    have hSeries' : pureRight p u u + (∑' j : ℕ, pureRight p u (u + ((j + 1 : ℕ) : ℝ) * m)) =
        ∑' j : ℕ, pureRight p u (u + (j : ℝ) * m) := by
      simpa only [Nat.cast_zero,zero_mul,add_zero] using hSeries.tsum_eq_zero_add.symm
    rw [hE,add_assoc,← mul_add,hSeries']
    have hNative : lowerNativeStream 0 p d = m * ∑' j : ℕ, pureRight p u (u + (j : ℝ) * m) := by
      unfold lowerNativeStream
      rw [← tsum_mul_left]
      exact tsum_congr (fun j => lowerNativeSite_zero)
    rw [hNative]
    unfold lowerNativePolynomial middleA u pureZ
    ring
  have hA := lowerDiagonal_adjacent_source_eq hp hp₂ hL hd.1 hd.2
  have hP := lowerSourcePair_zero_eq hp hp₂ hL hd.1 hd.2
  have hAdj : lowerAdjacentResponse 0 p d = adjacentDiagonal p L 0 u m := hA.symm
  unfold lowerDiagonalResponse jointPureValue adjacentDiagonal at *
  change lowerNativePolynomial 0 p d + lowerNativeStream 0 p d +
    (jointPureLambda - jointCanonicalMu) * lowerAdjacentResponse 0 p d +
    jointCanonicalMu * lowerSourcePair 0 p d =
      adjacentLawSignedValue p L 0 u m + jointPureLambda * adjacentSourceLaw p L 0 u m m m +
        jointCanonicalMu * fourthSourceRow p L 0 u m m m
  rw [← hN,hAdj,hP]
  ring

theorem lowerDiagonalResponse_third_gt {p d : ℝ} (hp : 1 ≤ p) (hpP : p ≤ 9 / 5)
    (hd : d ∈ Icc (0 : ℝ) (1 / 8)) :
    (8 / 100 : ℝ) * (p * (p + 1) * lowerDiagonalMass d ^ (-p - 2)) <
      lowerDiagonalResponse 3 p d := by
  let m := lowerDiagonalMass d
  let A := m ^ (p + 2) / (p * (p + 1))
  let N := p * (p + 1) * m ^ (-p - 2)
  have hp₀ := zero_lt_one.trans_le hp
  have hp₁ : 0 < p + 1 := by positivity
  have hm : 0 < m := by unfold m lowerDiagonalMass; linarith only [hd.2]
  have hA : 0 < A := by unfold A; positivity
  have hN : 0 < N := by unfold N; positivity
  have hAN : A * N = 1 := by
    unfold A N
    rw [show -p - 2 = -(p + 2) by ring,Real.rpow_neg hm.le]
    field_simp [hp₀.ne',hp₁.ne',(Real.rpow_pos_of_pos hm (p + 2)).ne']
  have h₀ := lowerNative_head_zero_third hp hpP hd
  have h₁ := lowerNative_head_one_third hp hpP hd
  have hT := lowerNative_tail_third hp hpP hd
  obtain ⟨M,hM,hB⟩ := lowerNativeSite_dominated (k := 3) le_rfl hp
  have hd' : d ∈ Icc (-(1 / 4) : ℝ) (1 / 4) := ⟨by linarith only [hd.1],by linarith only [hd.2]⟩
  have hS : Summable (fun j : ℕ => lowerNativeSite 3 p (j : ℝ) d) :=
    Summable.of_norm_bounded ((powerTail_summable (q := 2) (by norm_num) 1).mul_left M)
      (fun j => by simpa only [Nat.cast_one] using hB j d hd')
  have hSum := hS.sum_add_tsum_nat_add 2
  norm_num [Finset.sum_range_succ] at hSum
  change lowerNativeSite 3 p 0 d + lowerNativeSite 3 p 1 d + _ = lowerNativeStream 3 p d at hSum
  have hA₀ := lowerDiagonal_adjacent_third_gt hp hpP hd.1 hd.2
  change (803 / 100 + 5 * (p - 1)) * N < lowerAdjacentResponse 3 p d at hA₀
  have hA' := mul_lt_mul_of_pos_left hA₀ hA
  rw [show A * ((803 / 100 + 5 * (p - 1)) * N) = 803 / 100 + 5 * (p - 1) by
    rw [show A * ((803 / 100 + 5 * (p - 1)) * N) = (803 / 100 + 5 * (p - 1)) * (A * N) by ring,hAN,mul_one]] at hA'
  have hPair := lowerSourcePair_third_pos hp hpP hd.1 hd.2
  have hMu : 0 < jointCanonicalMu := by linarith only [jointCanonicalMu_bounds.1]
  have hCoeff : (1573 / 10000 : ℝ) ≤ jointPureLambda - jointCanonicalMu := by
    unfold jointPureLambda
    linarith only [jointCanonicalMu_bounds.2]
  have hPaid : (1573 / 10000 : ℝ) * (803 / 100 + 5 * (p - 1)) ≤
      (jointPureLambda - jointCanonicalMu) * (A * lowerAdjacentResponse 3 p d) :=
    mul_le_mul hCoeff hA'.le (by linarith only [hp]) (by linarith only [hCoeff])
  have hPos := mul_pos hMu (mul_pos hA hPair)
  change (7 / 25) * p ^ 2 - (71 / 25) * p + 4 - 3 / 40 - (5 / 13) * (9 / 5) * (9 / 5 - p) ≤
    A * ((36 / 25) * p + lowerNativeSite 3 p 0 d) at h₀
  change -(1 / 10 : ℝ) < A * lowerNativeSite 3 p 1 d at h₁
  change _ < A * (∑' j : ℕ, lowerNativeSite 3 p (j + 2 : ℕ) d) at hT
  simp_rw [Nat.cast_add,Nat.cast_ofNat] at hT
  have hFinal : (8 / 100 : ℝ) < A * lowerDiagonalResponse 3 p d := by
    unfold lowerDiagonalResponse
    rw [show lowerNativePolynomial 3 p d = (36 / 25) * p by unfold lowerNativePolynomial; ring]
    rw [← hSum]
    nlinarith only [h₀,h₁,hT,hPaid,hPos,sq_nonneg (p - 1),hp]
  apply lt_of_mul_lt_mul_left _ hA.le
  change A * ((8 / 100) * N) < A * lowerDiagonalResponse 3 p d
  rw [show A * ((8 / 100) * N) = (8 / 100) * (A * N) by ring,hAN,mul_one]
  exact hFinal

end ACS12.GammaMeasure

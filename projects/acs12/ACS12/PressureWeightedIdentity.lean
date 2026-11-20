import ACS12.PressureEntropyIdentity

/-! The weighted finite-mass entropy identity and its strict remainder. -/

namespace ACS12.Pressure

open Set

noncomputable def weightedPressureEntropy (lam p σ x y : ℝ) : ℝ :=
  p * pressureTau p σ * (entropyExp (pressureB p * x) + entropyExp (pressureB p * y)) +
    2 * (p + 1) * (lam + pressureTau p σ) * entropyExp (pressureC p * (-(x + y) / 2)) +
    lam * (p + 1) * (entropyExp (pressureBeta p * x) + entropyExp (pressureBeta p * y)) -
    lam * (entropyExp x + entropyExp y)

theorem weightedPressureEntropy_mean_eq {n : ℕ} {p : ℝ} (hp : 0 < p) (hn : 2 ≤ n) (F : Configuration n p) (lam : ℝ) :
    let m := sortedPressureMass F
    let g := massGeometricMean m
    let X := centeredLogMass m
    let σ := -Real.log g
    let Q := pairFlatTotal F
    let K := centeredMoment m (pressureBeta p)
    let L := centeredMoment m (pressureB p)
    let t := centeredMoment m 1
    let τ := pressureTau p σ
    (1 / (p + 1)) / 2 *
      (∑ i, ∑ j, originalPairLaw F i j * weightedPressureEntropy lam p σ (X i) (X j)) =
      pressureBeta p * τ * (L - 1) + (lam + τ) * (Q - 1) -
        lam * (1 / (p + 1)) * (t - 1) + lam * (K - 1) := by
  dsimp only
  let m := sortedPressureMass F
  let X := centeredLogMass m
  let σ := -Real.log (massGeometricMean m)
  let π := originalPairLaw F
  let Q := pairFlatTotal F
  let β := pressureBeta p
  let b := pressureB p
  let c := pressureC p
  let τ := pressureTau p σ
  let a := 1 / (p + 1)
  have hn₀ : 0 < n := by omega
  have hm (i : Fin n) : 0 < m i := F.mass_pos _
  obtain ⟨_,hL,hR⟩ := originalPairLaw_marginals hp hn F
  change ∀ i, ∑ j, π i j = massWeight m i at hL
  change ∀ j, ∑ i, π i j = massWeight m j at hR
  have hBoth (u : Fin n → ℝ) : (∑ i, ∑ j, π i j * (u i + u j)) =
      2 * ∑ i, massWeight m i * u i := by
    simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hL]
    rw [Finset.sum_comm (f := fun i j => π i j * u j)]
    simp only [← Finset.sum_mul,hR,two_mul]
  have hE (c : ℝ) : (∑ i, ∑ j, π i j * (entropyExp (c * X i) + entropyExp (c * X j))) =
      2 * (centeredMoment m c - 1) := by
    rw [hBoth (fun i => entropyExp (c * X i)),centeredEntropy_eq hn₀ hm]
  have hW : ∑ i, ∑ j, π i j = 1 := by
    simp only [hL,massWeight_sum_one hn₀ hm]
  have hZ : (∑ i, ∑ j, π i j * (c * (-(X i + X j) / 2))) = 0 := by
    calc
      _ = (-c / 2) * ∑ i, ∑ j, π i j * (X i + X j) := by
        simp_rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
      _ = _ := by rw [hBoth X,show (∑ i, massWeight m i * X i) = 0 from centeredLogMass_mean_zero hn₀ hm,mul_zero,mul_zero]
  have hTilt : (∑ i, ∑ j, π i j * entropyExp (c * (-(X i + X j) / 2))) = Q - 1 := by
    unfold entropyExp
    simp only [mul_sub,Finset.sum_sub_distrib,mul_one,hW,hZ,sub_zero]
    unfold Q pairFlatTotal
    simp only [pairFlatWeight_eq_tilt]
    rfl
  have hB : (∑ i, ∑ j, π i j * weightedPressureEntropy lam p σ (X i) (X j)) =
      p * τ * (2 * (centeredMoment m b - 1)) + 2 * (p + 1) * (lam + τ) * (Q - 1) +
      lam * (p + 1) * (2 * (centeredMoment m β - 1)) - lam * (2 * (centeredMoment m 1 - 1)) := by
    rw [← hE b,← hE β,← hE 1,← hTilt]
    simp_rw [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    unfold weightedPressureEntropy β b c τ
    simp only [one_mul]
    ring
  change a / 2 * (∑ i, ∑ j, π i j * weightedPressureEntropy lam p σ (X i) (X j)) =
    β * τ * (centeredMoment m b - 1) + (lam + τ) * (Q - 1) -
      lam * a * (centeredMoment m 1 - 1) + lam * (centeredMoment m β - 1)
  rw [hB]
  unfold a β pressureBeta
  field_simp [show p + 1 ≠ 0 by positivity] <;> ring

theorem weightedPressureEntropy_strict_remainder {n : ℕ} {p : ℝ} (hp : 1 < p) (hp₂ : p ≤ 2)
    (hn : 2 ≤ n) (F : Configuration n p) {lam : ℝ} (hlam : 0 < lam) (hWord : ∃ i j, sortedPressureMass F i ≠ sortedPressureMass F j) :
    let m := sortedPressureMass F
    let X := centeredLogMass m
    let σ := -Real.log (massGeometricMean m)
    let a := 1 / (p + 1)
    let U := pressureMeanPower p m
    (a / 2) * (∑ i, ∑ j, originalPairLaw F i j * weightedPressureEntropy lam p σ (X i) (X j)) <
      pressureEntropyScale p m *
        (pairFlatTotal F * (lam * Rank.meanRoot p m + U) - (lam + U ^ a) * pressureW F) := by
  dsimp only
  let m := sortedPressureMass F
  let g := massGeometricMean m
  let Q := pairFlatTotal F
  let A := Rank.meanRoot p m
  let U := pressureMeanPower p m
  let W := pressureW F
  let Wf := pressureWFlat F
  let σ := -Real.log g
  let a := 1 / (p + 1)
  let β := pressureBeta p
  let b := pressureB p
  let κ := pressureEntropyScale p m
  let t := centeredMoment m 1
  let K := centeredMoment m β
  let L := centeredMoment m b
  let τ := pressureTau p σ
  have hp₀ := zero_lt_one.trans hp
  have hn₀ : 0 < n := by omega
  have hm (i : Fin n) : 0 < m i := F.mass_pos _
  have hg : 0 < g := Real.exp_pos _
  have ht₁ : 1 < t := centeredMoment_one_gt_one hn₀ hm hWord
  have ht := zero_lt_one.trans ht₁
  have hK : 1 ≤ K := centeredMoment_ge_one hn₀ hm β
  have hL : 1 ≤ L := centeredMoment_ge_one hn₀ hm b
  have hL₀ := zero_lt_one.trans_le hL
  have hQ : 1 ≤ Q := pairFlatTotal_ge_one hp₀ hn F
  have hτ : 0 < τ := Real.exp_pos _
  have ha : 0 < a := by unfold a; positivity
  have ha₁ : a < 1 := (div_lt_one (by positivity)).mpr (by linarith only [hp])
  have hA : A = g ^ a * K / t := meanRoot_centered_eq hn₀ hp₀ hm
  have hU : U = g ^ (1 / p) * L / t := pressureMeanPower_eq_moment hn₀ hp₀ hm
  have hU₀ : 0 < U := by rw [hU]; positivity
  have hκ : 0 < κ := div_pos ht (Real.rpow_pos_of_pos hg a)
  have hE : τ = g ^ ((1 / p) * a) := by
    unfold τ pressureTau σ a
    rw [Real.rpow_def_of_pos hg,neg_neg]
    congr 1
    field_simp [hp₀.ne',show p + 1 ≠ 0 by positivity]
  have hβa : β + a = 1 := by unfold β pressureBeta a; field_simp [show p + 1 ≠ 0 by positivity]
  have hκA : κ * A = K := by
    change (t / g ^ a) * A = _
    rw [hA]
    field_simp [ht.ne',(Real.rpow_pos_of_pos hg a).ne']
  have hκU : κ * U = τ * L := by
    change (t / g ^ a) * U = _
    rw [hU,hE]
    have hExp : 1 / p - a = (1 / p) * a := by unfold a; field_simp [hp₀.ne',show p + 1 ≠ 0 by positivity]; ring
    rw [← hExp,Real.rpow_sub hg]
    field_simp [ht.ne',(Real.rpow_pos_of_pos hg a).ne']
  have hκW : κ * Wf = t ^ a := by
    change (t / g ^ a) * (g ^ a / t ^ β) = _
    have hT : t ^ β * t ^ a = t := by rw [← Real.rpow_add ht,hβa,Real.rpow_one]
    calc
      _ = t / t ^ β := by field_simp [(Real.rpow_pos_of_pos hg a).ne']
      _ = _ := (div_eq_iff (Real.rpow_pos_of_pos ht β).ne').mpr (by rw [mul_comm (t ^ a),hT])
  have hUA : U ^ a = τ * L ^ a / t ^ a := by
    rw [hU,Real.div_rpow (by positivity) ht.le,Real.mul_rpow (Real.rpow_nonneg hg.le _) hL₀.le,
      ← Real.rpow_mul hg.le,hE]
  have hRW : κ * ((lam + U ^ a) * Wf) = lam * t ^ a + τ * L ^ a := by
    rw [mul_left_comm,hκW,hUA]
    field_simp [(Real.rpow_pos_of_pos ht a).ne'] <;> ring
  have hScale : κ * (Q * (lam * A + U)) = Q * (lam * K + τ * L) := by
    calc
      _ = Q * (lam * (κ * A) + κ * U) := by ring
      _ = _ := by rw [hκA,hκU]
  have hT : t ^ a < 1 + a * (t - 1) := by
    have h := rpow_one_add_lt_one_add_mul_self (s := t - 1) (by linarith only [ht₁])
      (sub_ne_zero.mpr ht₁.ne') ha ha₁
    rwa [show 1 + (t - 1) = t by ring] at h
  have hT' : L ^ a ≤ 1 + a * (L - 1) := by
    have h := rpow_one_add_le_one_add_mul_self (s := L - 1) (by linarith only [hL]) ha.le ha₁.le
    rwa [show 1 + (L - 1) = L by ring] at h
  have hPos : 0 ≤ (Q - 1) * (lam * (K - 1) + τ * (L - 1)) :=
    mul_nonneg (sub_nonneg.mpr hQ) (add_nonneg (mul_nonneg hlam.le (sub_nonneg.mpr hK)) (mul_nonneg hτ.le (sub_nonneg.mpr hL)))
  have h₁ := weightedPressureEntropy_mean_eq hp₀ hn F lam
  have hTwo := add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hT hlam)
    (mul_le_mul_of_nonneg_left hT' hτ.le)
  have hNum : β * τ * (L - 1) + (lam + τ) * (Q - 1) - lam * a * (t - 1) + lam * (K - 1) <
      Q * (lam * K + τ * L) - (lam * t ^ a + τ * L ^ a) := by
    have hEq : β = 1 - a := by linarith only [hβa]
    rw [hEq]
    nlinarith only [hPos,hTwo]
  have hW' : κ * ((lam + U ^ a) * W) ≤ κ * ((lam + U ^ a) * Wf) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (pressureW_le_flat hp hp₂ hn F)
        (add_nonneg hlam.le (Real.rpow_nonneg hU₀.le _))) hκ.le
  change (a / 2) * (∑ i, ∑ j, originalPairLaw F i j *
    weightedPressureEntropy lam p σ (centeredLogMass m i) (centeredLogMass m j)) <
      κ * (Q * (lam * A + U) - (lam + U ^ a) * W)
  rw [show (a / 2) * (∑ i, ∑ j, originalPairLaw F i j *
      weightedPressureEntropy lam p σ (centeredLogMass m i) (centeredLogMass m j)) =
        β * τ * (L - 1) + (lam + τ) * (Q - 1) - lam * a * (t - 1) + lam * (K - 1) from h₁,mul_sub κ (Q * (lam * A + U)) ((lam + U ^ a) * W),hScale]
  rw [hRW] at hW'
  exact hNum.trans_le (sub_le_sub_left hW' _)

end ACS12.Pressure

import ACS12.PressureWeightedSupport
import ACS12.PressureRankAverage

/-! The weighted rank profile and the whole-support entropy on the original pair law. -/

namespace ACS12.Pressure

open Set CenteredCircle.AllN

theorem weightedPressure_normalized_regular {n : ℕ} {p : ℝ} (hp : 9 / 5 ≤ p) (hp₂ : p ≤ 2)
    (hn : 2 ≤ n) (F : Configuration n p) (hFloor : ∀ i, 1 / 13 ≤ F.mass i)
    (hCap : ∀ i, F.mass i ≤ 1) : IsEqualMassRegular F := by
  letI : NeZero n := ⟨by omega⟩
  let m := sortedPressureMass F
  let g := massGeometricMean m
  let σ := -Real.log g
  let X := centeredLogMass m
  let a := 1 / (p + 1)
  let Q := pairFlatTotal F
  let A := Rank.meanRoot p m
  let U := pressureMeanPower p m
  let W := pressureW F
  let κ := pressureEntropyScale p m
  let lam : ℝ := 28 / 27
  have hp₁ : 1 < p := by linarith only [hp]
  have hp₀ := zero_lt_one.trans hp₁
  have hn₀ : 0 < n := by omega
  have hm (i : Fin n) : 0 < m i := F.mass_pos _
  have hg : 0 < g := Real.exp_pos _
  have hFloor' (i : Fin n) : 1 / 13 ≤ m i := hFloor _
  have hCap' (i : Fin n) : m i ≤ 1 := hCap _
  by_cases hWord : ∃ i j, m i ≠ m j
  · have hσ₀ : 0 ≤ σ := neg_nonneg.mpr (Real.log_nonpos hg.le (massGeometricMean_le_one hn₀ hm hCap'))
    have hM := massTotal_pos hn₀ hm
    have hw (i : Fin n) : 0 ≤ massWeight m i := div_nonneg (hm i).le hM.le
    have hLogs (i : Fin n) : -Real.log 13 ≤ Real.log (m i) := by
      rw [← Real.log_inv,← one_div]
      exact Real.log_le_log (by norm_num) (hFloor' i)
    have hg' : -Real.log 13 ≤ Real.log g := by
      unfold g massGeometricMean
      rw [Real.log_exp]
      have h := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
        mul_le_mul_of_nonneg_left (hLogs i) (hw i)
      rw [← Finset.sum_mul,massWeight_sum_one hn₀ hm,one_mul] at h
      exact h
    have hσL : σ ≤ Real.log 13 := by unfold σ; linarith only [hg']
    have hSupport (i : Fin n) : X i ∈ Icc (-σ) (Real.log 13 - σ) := by
      unfold X centeredLogMass σ
      rw [Real.log_div hg.ne' (hm i).ne']
      exact ⟨by linarith only [Real.log_nonpos (hm i).le (hCap' i)],by linarith only [hLogs i]⟩
    have hPair := (originalPairLaw_marginals hp₀ hn F).1
    have hB : 0 ≤ (a / 2) * ∑ i, ∑ j, originalPairLaw F i j * weightedPressureEntropy lam p σ (X i) (X j) := by
      apply mul_nonneg (by unfold a; positivity)
      exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (hPair i j)
        (weightedPressureEntropy_nonneg hp hσ₀ hσL (hSupport i) (hSupport j))
    have hGap (i j : Fin n) : originalGapD p (m i) (m j) ≤ lam * originalGapG p (m i) (m j) :=
      originalGapD_le_weighted hp hp₂ ((by norm_num : (1 / 16 : ℝ) ≤ 1 / 13).trans (hFloor' i))
        ((by norm_num : (1 / 16 : ℝ) ≤ 1 / 13).trans (hFloor' j)) (hCap' i) (hCap' j)
    have hArc (k : Fin n) : (∑ i, halfArc (sortedPressureAngle F) i (i + k)) =
        (n : ℝ) * regularRankArc k := Rank.halfArc_rank_sum n (sortedPressureAngle F) k
    have hRank : Q * (lam * A + U) ≤ (lam + U ^ a) * W :=
      weightedPressureRank_necessary hp₁ hp₂ (by norm_num [lam]) hn F hArc hGap
    have hEnt := weightedPressureEntropy_strict_remainder hp₁ hp₂ hn F
      (show 0 < lam by norm_num [lam]) hWord
    have hκ : 0 ≤ κ := div_nonneg (zero_le_one.trans (centeredMoment_ge_one hn₀ hm 1))
      (Real.rpow_nonneg hg.le _)
    have hN : κ * (Q * (lam * A + U) - (lam + U ^ a) * W) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hκ (sub_nonpos.mpr hRank)
    exact False.elim ((hEnt.trans_le hN).not_ge hB)
  · have hEqual (i j : Fin n) : m i = m j := by
      by_contra h
      exact hWord ⟨i,j,h⟩
    let i₀ : Fin n := 0
    apply F.equal_mass_regular hn hp₀.le (hm i₀)
    intro i
    have h := hEqual ((Tuple.sort F.phase).symm i) i₀
    simpa only [m,sortedPressureMass,Function.comp_apply,Equiv.apply_symm_apply] using h

end ACS12.Pressure

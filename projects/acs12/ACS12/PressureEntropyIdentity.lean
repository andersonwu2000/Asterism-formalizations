import ACS12.PressureWordCoefficient
import ACS12.PressureEntropyMotion

/-! The actual two-marginal entropy identity and its unspent strict root remainder. -/
namespace ACS12.Pressure

open Set

noncomputable def pressurePairTilt {n : ℕ} {p : ℝ} (F : Configuration n p) (i j : Fin n) : ℝ :=
  let X := centeredLogMass (sortedPressureMass F)
  Real.exp (pressureC p * (-(X i + X j) / 2))

theorem pairFlatWeight_eq_tilt {n : ℕ} {p : ℝ} (F : Configuration n p) (i j : Fin n) :
    pairFlatWeight F i j = originalPairLaw F i j * pressurePairTilt F i j := by
  unfold pairFlatWeight pressurePairTilt pressureC
  dsimp only
  congr 2
  rw [show (p - 1) / (2 * (p + 1)) = (p - 1) / (p + 1) / 2 by
    rw [div_div,mul_comm (p + 1)]]
  ring

noncomputable def pressureEntropyScale {n : ℕ} (p : ℝ) (m : Fin n → ℝ) : ℝ :=
  centeredMoment m 1 / massGeometricMean m ^ (1 / (p + 1))

theorem centeredMoment_one_gt_one {n : ℕ} (hn : 0 < n) {m : Fin n → ℝ} (hm : ∀ i, 0 < m i)
    (hWord : ∃ i j, m i ≠ m j) : 1 < centeredMoment m 1 := by
  let X := centeredLogMass m
  have hg : 0 < massGeometricMean m := Real.exp_pos _
  have hM := massTotal_pos hn hm
  obtain ⟨i,j,hij⟩ := hWord
  have hX : X i ≠ X j := by
    unfold X centeredLogMass
    rw [Real.log_div hg.ne' (hm i).ne',Real.log_div hg.ne' (hm j).ne']
    exact fun e => hij (Real.log_injOn_pos (hm i) (hm j) (sub_right_injective e))
  have hE := strictConvexOn_exp.map_sum_lt (t := Finset.univ) (w := massWeight m) (p := X)
    (fun i _ => div_pos (hm i) hM) (massWeight_sum_one hn hm) (fun _ _ => Set.mem_univ _)
    ⟨i,Finset.mem_univ i,j,Finset.mem_univ j,hX⟩
  simpa only [smul_eq_mul,X,centeredLogMass_mean_zero hn hm,Real.exp_zero,centeredMoment,one_mul] using hE

theorem centeredEntropy_eq {n : ℕ} (hn : 0 < n) {m : Fin n → ℝ} (hm : ∀ i, 0 < m i) (c : ℝ) :
    (∑ i, massWeight m i * entropyExp (c * centeredLogMass m i)) = centeredMoment m c - 1 := by
  have hX : (∑ i, massWeight m i * (c * centeredLogMass m i)) = 0 := by
    rw [show (∑ i, massWeight m i * (c * centeredLogMass m i)) =
        c * ∑ i, massWeight m i * centeredLogMass m i by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring),
      centeredLogMass_mean_zero hn hm,mul_zero]
  simp only [entropyExp,mul_sub,Finset.sum_sub_distrib,mul_one,massWeight_sum_one hn hm,hX,sub_zero]
  rfl

end ACS12.Pressure

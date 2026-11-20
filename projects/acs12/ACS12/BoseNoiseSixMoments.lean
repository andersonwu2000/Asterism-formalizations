import ACS12.BoseNoiseMoments
import ACS12.BoseBernoulliCoefficients

/-! The complete Bose law's six exact moments; no sampled or truncated ranks. -/
namespace ACS12.NativeCells
open MeasureTheory
open GammaMeasure (powerTail)
set_option maxRecDepth 3000
set_option maxHeartbeats 800000

theorem scaledBoseMoment_0 : scaledBoseMoment 0 = (1:ℝ) := by
  have hZ := powerTail_even_bernoulli (k:=1) (by decide)
  have hB : bernoulli 2 = (1/6:ℚ) := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
    exact cubicBernoulli_2
  norm_num [hB,Nat.factorial] at hZ
  have hTwo := powerTail_even_bernoulli (k:=1) (by decide)
  have hBTwo : bernoulli 2 = (1/6:ℚ) := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
    exact cubicBernoulli_2
  norm_num [hBTwo,Nat.factorial] at hTwo
  rw [scaledBoseMoment_formula]
  norm_num [hZ,hTwo,Nat.factorial]
  all_goals field_simp [Real.pi_ne_zero]
  <;> ring

theorem scaledBoseMoment_1 : scaledBoseMoment 1 = (1:ℝ) := by
  have hZ := powerTail_even_bernoulli (k:=2) (by decide)
  have hB : bernoulli 4 = (-1/30:ℚ) := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
    exact cubicBernoulli_4
  norm_num [hB,Nat.factorial] at hZ
  have hTwo := powerTail_even_bernoulli (k:=1) (by decide)
  have hBTwo : bernoulli 2 = (1/6:ℚ) := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
    exact cubicBernoulli_2
  norm_num [hBTwo,Nat.factorial] at hTwo
  rw [scaledBoseMoment_formula]
  norm_num [hZ,hTwo,Nat.factorial]
  all_goals field_simp [Real.pi_ne_zero]
  <;> ring

theorem scaledBoseMoment_2 : scaledBoseMoment 2 = (20/7:ℝ) := by
  have hZ := powerTail_even_bernoulli (k:=3) (by decide)
  have hB : bernoulli 6 = (1/42:ℚ) := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
    exact cubicBernoulli_6
  norm_num [hB,Nat.factorial] at hZ
  have hTwo := powerTail_even_bernoulli (k:=1) (by decide)
  have hBTwo : bernoulli 2 = (1/6:ℚ) := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
    exact cubicBernoulli_2
  norm_num [hBTwo,Nat.factorial] at hTwo
  rw [scaledBoseMoment_formula]
  norm_num [hZ,hTwo,Nat.factorial]
  all_goals field_simp [Real.pi_ne_zero]
  <;> ring

theorem scaledBoseMoment_3 : scaledBoseMoment 3 = (90/7:ℝ) := by
  have hZ := powerTail_even_bernoulli (k:=4) (by decide)
  have hB : bernoulli 8 = (-1/30:ℚ) := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
    exact cubicBernoulli_8
  norm_num [hB,Nat.factorial] at hZ
  have hTwo := powerTail_even_bernoulli (k:=1) (by decide)
  have hBTwo : bernoulli 2 = (1/6:ℚ) := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
    exact cubicBernoulli_2
  norm_num [hBTwo,Nat.factorial] at hTwo
  rw [scaledBoseMoment_formula]
  norm_num [hZ,hTwo,Nat.factorial]
  all_goals field_simp [Real.pi_ne_zero]
  <;> ring

theorem scaledBoseMoment_4 : scaledBoseMoment 4 = (6000/77:ℝ) := by
  have hZ := powerTail_even_bernoulli (k:=5) (by decide)
  have hB : bernoulli 10 = (5/66:ℚ) := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
    exact cubicBernoulli_10
  norm_num [hB,Nat.factorial] at hZ
  have hTwo := powerTail_even_bernoulli (k:=1) (by decide)
  have hBTwo : bernoulli 2 = (1/6:ℚ) := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
    exact cubicBernoulli_2
  norm_num [hBTwo,Nat.factorial] at hTwo
  rw [scaledBoseMoment_formula]
  norm_num [hZ,hTwo,Nat.factorial]
  all_goals field_simp [Real.pi_ne_zero]
  <;> ring

theorem scaledBoseMoment_5 : scaledBoseMoment 5 = (4146000/7007:ℝ) := by
  have hZ := powerTail_even_bernoulli (k:=6) (by decide)
  have hB : bernoulli 12 = (-691/2730:ℚ) := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
    exact cubicBernoulli_12
  norm_num [hB,Nat.factorial] at hZ
  have hTwo := powerTail_even_bernoulli (k:=1) (by decide)
  have hBTwo : bernoulli 2 = (1/6:ℚ) := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
    exact cubicBernoulli_2
  norm_num [hBTwo,Nat.factorial] at hTwo
  rw [scaledBoseMoment_formula]
  norm_num [hZ,hTwo,Nat.factorial]
  all_goals field_simp [Real.pi_ne_zero]
  <;> ring

theorem scaledBoseMoment_6 : scaledBoseMoment 6 = (5400000/1001:ℝ) := by
  have hZ := powerTail_even_bernoulli (k:=7) (by decide)
  have hB : bernoulli 14 = (7/6:ℚ) := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
    exact cubicBernoulli_14
  norm_num [hB,Nat.factorial] at hZ
  have hTwo := powerTail_even_bernoulli (k:=1) (by decide)
  have hBTwo : bernoulli 2 = (1/6:ℚ) := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
    exact cubicBernoulli_2
  norm_num [hBTwo,Nat.factorial] at hTwo
  rw [scaledBoseMoment_formula]
  norm_num [hZ,hTwo,Nat.factorial]
  all_goals field_simp [Real.pi_ne_zero]
  <;> ring

end ACS12.NativeCells

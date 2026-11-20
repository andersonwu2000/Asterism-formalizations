import ACS12.HighMaximumRadial
import ACS12.HighInverseScale
import ACS12.HighMaximumMoments

/-! The actual maximum pressure coordinate and inverse minimum scale remain correlated. -/
namespace ACS12.Pressure

open Set CenteredCircle.AllN
open GammaMeasure

theorem high_massPotential_le_unit {p L Q : ℝ} (hp : 2 ≤ p) (hL : 0 < L) (hQ : 1 ≤ Q) :
    Q * imagePotential p L Q ≤ imagePotential p L 1 := by
  have hp₀ : 0 < p := by linarith only [hp]
  have hQ₀ := zero_lt_one.trans_le hQ
  have hK := imagePotential_pos hp₀ hL zero_lt_one
  have h := mul_le_mul_of_nonneg_left (high_imagePotential_scaled_upper hp hL zero_lt_one hQ) hQ₀.le
  have hE : Q * ((1 / Q) ^ 2 * imagePotential p L 1) = imagePotential p L 1 / Q := by field_simp [hQ₀.ne']
  rw [hE] at h
  exact h.trans (div_le_self hK.le hQ)

theorem high_original_pressure_range {n : ℕ} {p : ℝ} (hn : 2 ≤ n) (hp : 2 ≤ p)
    (F : Configuration n p) (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi)) (i : Fin n)
    (hMax : ∀ j, C.source.mass j ≤ C.source.mass i) :
    let S := C.source
    let Q := S.mass i
    let D := Q * imagePotential p S.period Q
    let c := F.chartRadialScale C * (2 * F.coefficient * F.radius ^ 2)
    D < c ∧ 1 < (c + Q * imageSelf p S.period) / D ∧
      (c + Q * imageSelf p S.period) / D < 33 / 10 := by
  let S := C.source
  let Q := S.mass i
  let D := Q * imagePotential p S.period Q
  let c := F.chartRadialScale C * (2 * F.coefficient * F.radius ^ 2)
  have hp₀ : 0 < p := by linarith only [hp]
  have hQ := S.mass_pos i
  have hQ₁ : 1 ≤ Q := by rw [← S.mass_root]; exact hMax _
  have hD : 0 < D := mul_pos hQ (imagePotential_pos hp₀ S.period_pos hQ)
  have hC : D < c := (high_massPotential_le_unit hp S.period_pos hQ₁).trans_lt
    (chartLevel_gt_potential_one hp₀ F C)
  have hSelf := imageSelf_pos hp₀ S.period_pos
  refine ⟨hC,(one_lt_div hD).mpr (hC.trans (lt_add_of_pos_right c (mul_pos hQ hSelf))),?_⟩
  have h := high_original_maximum_radial_bound hn hp F C i hMax
  change c + Q * imageSelf p S.period ≤ 2 * D * powerTail 2 1 at h
  have hZeta : 2 * powerTail 2 1 < (33 / 10 : ℝ) := by
    have hZ : powerTail 2 1 = Real.pi ^ 2 / 6 := by
      simpa only [pureZ,show (1 : ℝ) + 1 = 2 by norm_num,one_mul] using pureZ_one_eq
    rw [hZ]
    have hPi := pow_lt_pow_left₀ Real.pi_lt_d6 Real.pi_pos.le (by decide : 2 ≠ 0)
    linarith only [hPi]
  apply (div_lt_iff₀ hD).mpr
  have h' := mul_lt_mul_of_pos_right hZeta hD
  nlinarith only [h,h']

theorem high_inverseMinimum_square {p L a Q t x c : ℝ} (hp : 2 ≤ p) (hL : 0 < L)
    (ha : 0 < a) (hQ : 0 < Q) (ht : 0 < t) (hSmall : 2 * a < Q)
    (hC : Q * imagePotential p L Q < c)
    (hT : imagePotential p L t = c / (2 * a))
    (hX : c = x * (Q * imagePotential p L Q)) :
    (a / t) ^ 2 ≤ (a / Q) * x / 2 := by
  let k := imagePotential p L
  have hp₀ : 0 < p := by linarith only [hp]
  have hK := imagePotential_pos hp₀ hL hQ
  change k t = c / (2 * a) at hT
  change Q * k Q < c at hC
  change c = x * (Q * k Q) at hX
  change 0 < k Q at hK
  have hQT : k Q < k t := by
    rw [hT]
    apply (lt_div_iff₀ (mul_pos (by norm_num) ha)).mpr
    simpa only [mul_comm] using (mul_lt_mul_of_pos_right hSmall hK).trans hC
  have htQ : t ≤ Q := by
    by_contra! h
    exact (high_imagePotential_strictAnti hp hL hQ ht h).not_ge hQT.le
  have hS := high_imagePotential_scaled_upper hp hL ht htQ
  change k Q ≤ (t / Q) ^ 2 * k t at hS
  rw [hT,hX] at hS
  have hPay : 2 * a ≤ (t / Q) ^ 2 * (x * Q) := by
    apply (mul_le_mul_iff_right₀ hK).mp
    have h := (le_div_iff₀ (show 0 < 2 * a by positivity)).mp
      (show k Q ≤ ((t / Q) ^ 2 * (x * (Q * k Q))) / (2 * a) by
        simpa only [mul_div_assoc] using hS)
    nlinarith only [h]
  have hXQ : 2 * a * Q ≤ t ^ 2 * x := by
    have h := mul_le_mul_of_nonneg_right hPay hQ.le
    have hE : (t / Q) ^ 2 * (x * Q) * Q = t ^ 2 * x := by field_simp [hQ.ne']
    rwa [hE] at h
  rw [div_pow]
  apply (div_le_iff₀ (pow_pos ht 2)).mpr
  have h := mul_le_mul_of_nonneg_left hXQ (show 0 ≤ a / (2 * Q) by positivity)
  convert h using 1 <;> field_simp [hQ.ne'] <;> ring

end ACS12.Pressure

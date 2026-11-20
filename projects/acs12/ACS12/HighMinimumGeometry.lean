import ACS12.HighInverseScale
import ACS12.PressureMinimumGeometry

/-! The original minimum torque retains its actual high-exponent neighbor quantum. -/
namespace ACS12.Pressure

open Set CenteredCircle.AllN
open GammaMeasure

theorem high_minimumTorque_quantum {n : ℕ} {p L t : ℝ} (hp : 2 ≤ p) (hL : 0 < L)
    (ht : 0 < t) (m d e : Fin n → ℝ) (hm : ∀ j, 0 < m j) (hd : ∀ j, 0 < d j) (he : ∀ j, 0 < e j)
    {i j : Fin n} (hj : j ≠ i) (hMin : ∀ k, m i ≤ m k)
    (hR : nonselfRayRow L m d i (imagePotential p L) ≤ m i * imagePotential p L t)
    (hT : nonselfRayRow L m d i (imageSlope p L) = nonselfRayRow L m e i (imageSlope p L)) :
    (∀ k, k ≠ i → t ≤ d k) ∧ t * (m j / m i) ^ (1 / (p + 1) : ℝ) ≤ e j := by
  let k := imagePotential p L
  let U := imageSlope p L
  let a := m i
  let r := m j
  let g := e j
  have hp₀ := (by linarith only [hp] : 0 < p)
  have ha := hm i
  have hr := hm j
  have hg := he j
  have hK (x : ℝ) (hx : 0 < x) : 0 < k x := imagePotential_pos hp₀ hL hx
  have hU (x : ℝ) (hx : 0 < x) : 0 < U x := imageSlope_pos hp₀ hL hx
  have hD (l : Fin n) (hl : l ≠ i) : t ≤ d l := by
    have h := nonselfRayRow_point_le hL m d (fun j => (hm j).le) hd hl
      (fun x hx => (hK x hx).le) (imagePotential_samples_summable hp₀ hL (hd l))
    have hC := (mul_le_mul_of_nonneg_right (hMin l) (hK _ (hd l)).le).trans (h.trans hR)
    have hB := (mul_le_mul_iff_right₀ ha).mp hC
    by_contra! h'
    exact (high_imagePotential_strictAnti hp hL (hd l) ht h').not_ge hB
  refine ⟨hD,?_⟩
  have hTS : nonselfRayRow L m d i U ≤ (U t / k t) * nonselfRayRow L m d i k := by
    unfold nonselfRayRow
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l hl
    rw [mul_left_comm (U t / k t)]
    apply mul_le_mul_of_nonneg_left _ (hm l).le
    unfold imageTail
    rw [← tsum_mul_left]
    apply (imageSlope_samples_hasSum hp₀ hL (hd l)).summable.tsum_le_tsum _
      ((imagePotential_samples_summable hp₀ hL (hd l)).mul_left _)
    intro q
    let x := d l + (q : ℝ) * L
    have hx : t ≤ x := (hD l (Finset.mem_erase.mp hl).1).trans
      (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg q) hL.le))
    have h := imageSlope_mul_potential_le hp₀ hL ht hx
    apply (mul_le_mul_iff_left₀ (hK t ht)).mp
    have hE : U t / k t * k x * k t = U t * k x := by field_simp [(hK t ht).ne']
    rw [hE]
    exact h
  have hOpp := nonselfRayRow_point_le hL m e (fun j => (hm j).le) he hj
    (fun x hx => (hU x hx).le) (imageSlope_samples_hasSum hp₀ hL hg).summable
  have hPay : r * U g ≤ a * U t := by
    have h := hOpp.trans (hT ▸ hTS)
    have h' := mul_le_mul_of_nonneg_left hR (div_nonneg (hU t ht).le (hK t ht).le)
    have hE : U t / k t * (a * k t) = a * U t := by field_simp [(hK t ht).ne']
    exact h.trans (h'.trans_eq hE)
  have htG : t ≤ g := by
    by_contra! h
    have hA := imageSlope_mul_potential_le hp₀ hL hg h.le
    have hB := high_imagePotential_strictAnti hp hL hg ht h
    have hC := mul_lt_mul_of_pos_left hB (hU g hg)
    have hD := lt_of_mul_lt_mul_right (hA.trans_lt hC) (hK g hg).le
    exact ((mul_lt_mul_of_pos_left hD ha).trans_le (mul_le_mul_of_nonneg_right (hMin j) (hU g hg).le)).not_ge hPay
  have h := high_imageSlope_scaled_lower hp hL ht htG
  have h₁ := mul_le_mul_of_nonneg_left h hr.le
  have h₂ : r * (t / g) ^ (p + 1) ≤ a := by
    apply (mul_le_mul_iff_left₀ (hU t ht)).mp
    linarith only [h₁,hPay]
  let u := (r / a) ^ (1 / (p + 1) : ℝ)
  have hP : 0 < p + 1 := by linarith only [hp]
  have hCube : u ^ (p + 1) = r / a := by
    unfold u
    rw [← Real.rpow_mul (div_nonneg hr.le ha.le),one_div_mul_cancel hP.ne',Real.rpow_one]
  change t * u ≤ g
  by_contra! hBad
  have hBad₃ := Real.rpow_lt_rpow hg.le hBad hP
  rw [Real.mul_rpow ht.le (Real.rpow_pos_of_pos (div_pos hr ha) _).le,hCube] at hBad₃
  rw [Real.div_rpow ht.le hg.le] at h₂
  have h₂' : r * t ^ (p + 1) ≤ a * g ^ (p + 1) := by
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hg _)).mp
    simpa only [mul_div_assoc] using h₂
  have hBad' := (lt_div_iff₀ ha).mp
    (show g ^ (p + 1) < (t ^ (p + 1) * r) / a by simpa only [mul_div_assoc] using hBad₃)
  nlinarith only [h₂',hBad']

end ACS12.Pressure

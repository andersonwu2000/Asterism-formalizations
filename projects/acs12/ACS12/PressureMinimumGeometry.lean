import ACS12.PressureInverseScale
import ACS12.PressureOccupiedPacking

/-! The original minimum torque fixes the opposite-neighbor force scale. -/
namespace ACS12.Pressure

open Set CenteredCircle.AllN
open GammaMeasure (imagePotential imagePotential_pos imagePotential_samples_summable
  imageSlope imageSlope_samples_hasSum imageSelf imageSelf_eq_tail)

noncomputable def nonselfRayRow {n : ℕ} (L : ℝ) (m d : Fin n → ℝ) (i : Fin n)
    (K : ℝ → ℝ) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, m j * imageTail K L (d j)

theorem rayRow_split_self {n : ℕ} {L : ℝ} (m d : Fin n → ℝ) (i : Fin n) (K : ℝ → ℝ)
    (h : d i = L) :
    (∑ j, m j * imageTail K L (d j)) = nonselfRayRow L m d i K + m i * imageTail K L L := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),h]
  rfl

private theorem rayRow_nonneg {n : ℕ} {L : ℝ} (hL : 0 < L) {m d : Fin n → ℝ}
    (hm : ∀ j, 0 ≤ m j) (hd : ∀ j, 0 < d j) (i : Fin n) {K : ℝ → ℝ}
    (hK : ∀ x > 0, 0 ≤ K x) : 0 ≤ nonselfRayRow L m d i K := by
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (hm j) (tsum_nonneg fun q =>
    hK _ (add_pos_of_pos_of_nonneg (hd j) (mul_nonneg (Nat.cast_nonneg q) hL.le)))

theorem original_nonself_rows {n : ℕ} {p : ℝ} (hp : 0 < p) (F : Configuration n p)
    (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi)) (i : Fin n) :
    let S := C.source
    let L := S.period
    let C₀ := F.chartRadialScale C * (2 * F.coefficient * F.radius ^ 2)
    let R (d : Fin n → ℝ) (K : ℝ → ℝ) := nonselfRayRow L S.mass d i K
    R (S.forwardDistance i) (imagePotential p L) + R (fun j => S.forwardDistance j i) (imagePotential p L) = C₀ ∧
      R (S.forwardDistance i) (imageSlope p L) = R (fun j => S.forwardDistance j i) (imageSlope p L) := by
  let S := C.source
  let L := S.period
  have hR := F.chart_radial_images C hp i
  have hT := F.chart_torque_images C hp i
  unfold AnchoredCircleSource.forwardExterior AnchoredCircleSource.backwardExterior at hR hT
  have hF (K : ℝ → ℝ) := rayRow_split_self S.mass (S.forwardDistance i) i K (S.forwardDistance_self i)
  have hB (K : ℝ → ℝ) := rayRow_split_self S.mass (fun j => S.forwardDistance j i) i K (S.forwardDistance_self i)
  change (∑ j, S.mass j * imageTail (imagePotential p L) L (S.forwardDistance i j)) +
    (∑ j, S.mass j * imageTail (imagePotential p L) L (S.forwardDistance j i)) = _ at hR
  change (∑ j, S.mass j * imageTail (imageSlope p L) L (S.forwardDistance i j)) -
    (∑ j, S.mass j * imageTail (imageSlope p L) L (S.forwardDistance j i)) = _ at hT
  rw [hF,hB,imageSelf_eq_tail] at hR
  rw [hF,hB] at hT
  constructor
  · dsimp only
    linarith only [hR]
  · dsimp only
    linarith only [hT]

theorem nonselfRayRow_point_le {n : ℕ} {L : ℝ} (hL : 0 < L) (m d : Fin n → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hd : ∀ j, 0 < d j) {i j : Fin n} (hj : j ≠ i) {K : ℝ → ℝ}
    (hK : ∀ x > 0, 0 ≤ K x) (hS : Summable (fun q : ℕ => K (d j + (q : ℝ) * L))) :
    m j * K (d j) ≤ nonselfRayRow L m d i K := by
  have hTerm : K (d j) ≤ imageTail K L (d j) := by
    have h := hS.le_tsum 0 (fun q _ =>
      hK _ (add_pos_of_pos_of_nonneg (hd j) (mul_nonneg (Nat.cast_nonneg q) hL.le)))
    simpa only [imageTail,Nat.cast_zero,zero_mul,add_zero] using h
  apply (mul_le_mul_of_nonneg_left hTerm (hm j)).trans
  apply Finset.single_le_sum _ (Finset.mem_erase.mpr ⟨hj,Finset.mem_univ _⟩)
  intro k _
  exact mul_nonneg (hm k) (tsum_nonneg fun q =>
    hK _ (add_pos_of_pos_of_nonneg (hd k) (mul_nonneg (Nat.cast_nonneg q) hL.le)))

theorem minimumTorque_quantum {n : ℕ} {p L t : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hL : 0 < L)
    (ht : 0 < t) (m d e : Fin n → ℝ) (hm : ∀ j, 0 < m j) (hd : ∀ j, 0 < d j) (he : ∀ j, 0 < e j)
    {i j : Fin n} (hj : j ≠ i) (hMin : ∀ k, m i ≤ m k)
    (hR : nonselfRayRow L m d i (imagePotential p L) ≤ m i * imagePotential p L t)
    (hT : nonselfRayRow L m d i (imageSlope p L) = nonselfRayRow L m e i (imageSlope p L)) :
    (∀ k, k ≠ i → t ≤ d k) ∧ t * (m j / m i) ^ (1 / 3 : ℝ) ≤ e j := by
  let k := imagePotential p L
  let U := imageSlope p L
  let a := m i
  let r := m j
  let g := e j
  have hp₀ := zero_lt_one.trans_le hp
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
    exact (imagePotential_strictAnti hp hp₂ hL (hd l) ht h').not_ge hB
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
    have hB := imagePotential_strictAnti hp hp₂ hL hg ht h
    have hC := mul_lt_mul_of_pos_left hB (hU g hg)
    have hD := lt_of_mul_lt_mul_right (hA.trans_lt hC) (hK g hg).le
    exact ((mul_lt_mul_of_pos_left hD ha).trans_le (mul_le_mul_of_nonneg_right (hMin j) (hU g hg).le)).not_ge hPay
  have h := imageSlope_scaled_lower hp₀ hp₂ hL ht htG
  have h₁ := mul_le_mul_of_nonneg_left h hr.le
  have h₂ : r * (t / g) ^ 3 ≤ a := by
    apply (mul_le_mul_iff_left₀ (hU t ht)).mp
    linarith only [h₁,hPay]
  let u := (r / a) ^ (1 / 3 : ℝ)
  have hCube : u ^ 3 = r / a := by
    unfold u
    rw [← Real.rpow_natCast,← Real.rpow_mul (div_nonneg hr.le ha.le)]
    norm_num [r,a]
  change t * u ≤ g
  by_contra! hBad
  have hBad₃ := pow_lt_pow_left₀ hBad hg.le (by decide : (3 : ℕ) ≠ 0)
  rw [mul_pow,hCube] at hBad₃
  rw [div_pow] at h₂
  have h₂' : r * t ^ 3 ≤ a * g ^ 3 := by
    apply (div_le_iff₀ (pow_pos hg 3)).mp
    simpa only [mul_div_assoc] using h₂
  have hBad' := (lt_div_iff₀ ha).mp (show g ^ 3 < (t ^ 3 * r) / a by simpa only [mul_div_assoc] using hBad₃)
  nlinarith only [h₂',hBad']

end ACS12.Pressure

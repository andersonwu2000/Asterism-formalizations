import ACS12.OuterAdjacentComparison
import ACS12.PureNativeBasics

/-! Exact pure Peano kernels and normalized adjacent source. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set
open GammaDeficit (lineDensity)

noncomputable def purePeanoA (p u x : ℝ) : ℝ :=
  x ^ (-p) - (x + u) ^ (-p) - u * p * (x + u) ^ (-(p + 1))

noncomputable def purePeanoB (p u x : ℝ) : ℝ :=
  u * p * x ^ (-(p + 1)) - x ^ (-p) + (x + u) ^ (-p)

theorem lawPeanoKernel_zero {p L u x : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hu : 0 < u) (hx : 0 < x) :
    lawPeanoKernel p L 0 u .a x = purePeanoA p u x ∧
      lawPeanoKernel p L 0 u .b x = purePeanoB p u x := by
  let w := lineDensity p
  let A (s : ℝ) := w s * Real.exp (-s * x)
  let B (s : ℝ) := w s * s * Real.exp (-s * x)
  let C (s : ℝ) := w s * Real.exp (-s * (x + u))
  let D (s : ℝ) := w s * s * Real.exp (-s * (x + u))
  have hp₀ := zero_lt_one.trans_le hp
  have hθ : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have hx' := add_pos hx hu
  have hI (t : ℝ) (ht : 0 < t) :
      IntegrableOn (fun s => w s * Real.exp (-s * t)) (Ioi 0) ∧
        IntegrableOn (fun s => w s * s * Real.exp (-s * t)) (Ioi 0) := by
    constructor
    · simpa only [w, lawDensity, sub_zero, one_mul, zero_mul, add_zero, pow_zero, mul_one] using
        lawMoment_integrable hp hp₂ hL hθ ht 0
    · simpa only [w, lawDensity, sub_zero, one_mul, zero_mul, add_zero, pow_one] using
        lawMoment_integrable hp hp₂ hL hθ ht 1
  have hRad (t : ℝ) (ht : 0 < t) : (∫ s : ℝ in Ioi 0, w s * Real.exp (-s * t)) = t ^ (-p) := by
    simpa only [w, lawMoment, lawDensity, sub_zero, one_mul, zero_mul, add_zero, pow_zero, mul_one] using
      lawMoment_zero_radial (L := L) hp₀ ht
  have hSlope (t : ℝ) (ht : 0 < t) :
      (∫ s : ℝ in Ioi 0, w s * s * Real.exp (-s * t)) = p * t ^ (-(p + 1)) := by
    simpa only [w, lawMoment, lawDensity, sub_zero, one_mul, zero_mul, add_zero, pow_one] using
      lawMoment_zero_slope (L := L) hp₀ ht
  have hA : IntegrableOn A (Ioi 0) := (hI x hx).1
  have hB : IntegrableOn B (Ioi 0) := (hI x hx).2
  have hC : IntegrableOn C (Ioi 0) := (hI (x + u) hx').1
  have hD : IntegrableOn D (Ioi 0) := (hI (x + u) hx').2
  have hExp (s : ℝ) : Real.exp (-s * (x + u)) = Real.exp (-(u * s)) * Real.exp (-s * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  constructor
  · have hEq (s : ℝ) : lawPeanoDensity p L 0 u .a s * Real.exp (-s * x) =
        A s - C s - u * D s := by
      simp only [A, C, D, w, lawPeanoDensity, lawDensity, sub_zero, one_mul, zero_mul, add_zero,
        densityPolynomial, polyA, hExp]
      ring
    have hAC : IntegrableOn (fun s => A s - C s) (Ioi 0) := hA.sub hC
    rw [lawPeanoKernel, signedLaplace, setIntegral_congr_fun measurableSet_Ioi (fun s _ => hEq s),
      integral_sub hAC (hD.const_mul u), integral_sub hA hC, integral_const_mul]
    change (∫ s : ℝ in Ioi 0, w s * Real.exp (-s * x)) -
      (∫ s : ℝ in Ioi 0, w s * Real.exp (-s * (x + u))) -
      u * (∫ s : ℝ in Ioi 0, w s * s * Real.exp (-s * (x + u))) = _
    rw [hRad x hx, hRad (x + u) hx', hSlope (x + u) hx', purePeanoA]
    ring
  · have hEq (s : ℝ) : lawPeanoDensity p L 0 u .b s * Real.exp (-s * x) =
        u * B s - A s + C s := by
      simp only [A, B, C, w, lawPeanoDensity, lawDensity, sub_zero, one_mul, zero_mul, add_zero,
        densityPolynomial, polyB, hExp]
      ring
    have hBA : IntegrableOn (fun s => u * B s - A s) (Ioi 0) := (hB.const_mul u).sub hA
    rw [lawPeanoKernel, signedLaplace, setIntegral_congr_fun measurableSet_Ioi (fun s _ => hEq s),
      integral_add hBA hC, integral_sub (hB.const_mul u) hA, integral_const_mul]
    change u * (∫ s : ℝ in Ioi 0, w s * s * Real.exp (-s * x)) -
      (∫ s : ℝ in Ioi 0, w s * Real.exp (-s * x)) +
      (∫ s : ℝ in Ioi 0, w s * Real.exp (-s * (x + u))) = _
    rw [hRad x hx, hRad (x + u) hx', hSlope x hx, purePeanoB]
    ring

theorem purePeanoA_scale {p u x : ℝ} (hu : 0 < u) (hx : 0 < x) :
    purePeanoA p u (u * x) = u ^ (-p) * purePeanoA p 1 x := by
  unfold purePeanoA
  rw [show u * x + u = u * (x + 1) by ring,
    Real.mul_rpow hu.le hx.le, Real.mul_rpow hu.le (by positivity : 0 ≤ x + 1),
    Real.mul_rpow hu.le (by positivity : 0 ≤ x + 1),
    show -(p + 1) = -p - 1 by ring, Real.rpow_sub_one hu.ne']
  field_simp [hu.ne']

theorem pureAdjacent_normalized {p L u m : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hL : 0 < L)
    (hu : 0 < u) (hm : 0 < m) :
    u ^ (p - 1) * adjacentDiagonal p L 0 u m =
      samplingHead (purePeanoA p 1) (m / u) (m / u) +
      u ^ (p - 1) * samplingTail (purePeanoB p u) 0 1 + 1 - (p + 1) * (m / u) := by
  have hp₀ := zero_lt_one.trans_le hp
  have hA : samplingHead (lawPeanoKernel p L 0 u .a) m m =
      u ^ (-p) * u * samplingHead (purePeanoA p 1) (m / u) (m / u) := by
    have hP (j : ℕ) : lawPeanoKernel p L 0 u .a (m + j * m) =
        u ^ (-p) * purePeanoA p 1 (m / u + j * (m / u)) := by
      have hJ : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
      have h := (lawPeanoKernel_zero hp hp₂ hL hu (show 0 < m + j * m by positivity)).1
      rw [h, show m + j * m = u * (m / u + j * (m / u)) by field_simp [hu.ne']]
      exact purePeanoA_scale hu (by positivity)
    unfold samplingHead
    simp_rw [hP, tsum_mul_left]
    field_simp [hu.ne']
  have hB : samplingTail (lawPeanoKernel p L 0 u .b) 0 1 =
      samplingTail (purePeanoB p u) 0 1 := by
    unfold samplingTail
    apply congrArg ((1 : ℝ) * ·)
    apply tsum_congr
    intro j
    exact (lawPeanoKernel_zero hp hp₂ hL hu (by positivity)).2
  have hW : u ^ (p - 1) * u ^ (-p) = u⁻¹ := by
    rw [← Real.rpow_add hu, show p - 1 + -p = -1 by ring, Real.rpow_neg_one]
  have hD := lawMoment_zero_radial (L := L) hp₀ hu
  have hU := lawMoment_zero_slope (L := L) hp₀ hu
  rw [adjacentDiagonal, adjacentSourceLaw, hA, hB, hD, hU, lawSelf, zero_mul, add_zero]
  rw [show u ^ (-(p + 1)) = u ^ (-p) / u by
    rw [show -(p + 1) = -p - 1 by ring, Real.rpow_sub_one hu.ne']]
  have hW' : u * (p * (u ^ (-p) / u)) = p * u ^ (-p) := by field_simp [hu.ne']
  rw [hW', show p * u ^ (-p) + u ^ (-p) = (p + 1) * u ^ (-p) by ring]
  calc
    _ = u ^ (p - 1) * samplingTail (purePeanoB p u) 0 1 + (u ^ (p - 1) * u ^ (-p)) *
        (u - m * (p + 1) + u * samplingHead (purePeanoA p 1) (m / u) (m / u)) := by ring
    _ = _ := by rw [hW]; field_simp [hu.ne']; ring

end ACS12.GammaMeasure

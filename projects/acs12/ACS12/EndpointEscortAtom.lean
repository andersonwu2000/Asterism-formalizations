import ACS12.AffineEscortEntropy

/-! The endpoint-adapted escort and its exact rational curvature. -/
namespace ACS12.NativeCells

set_option backward.isDefEq.respectTransparency false

noncomputable def endpointEscortCoefficient (P : ℝ) : ℝ := 1 / (P - 1 - 2 / 7)
noncomputable def endpointEscortDensity (P u : ℝ) : ℝ := escortDensity (endpointEscortCoefficient P) u
noncomputable def endpointEscortAtom (P u : ℝ) : ℝ :=
  escortAtom P (endpointEscortCoefficient P) (nativeEntropyCost P) u

noncomputable def endpointEscortSlope (P u : ℝ) : ℝ :=
  nativeEntropyCostSlope P u + endpointEscortCoefficient P * Real.log u +
    endpointEscortDensity P u / u -
    P * endpointEscortCoefficient P * Real.log (endpointEscortDensity P u) - 1

noncomputable def endpointEscortRawCurvature (P u : ℝ) : ℝ :=
  nativeEntropyCostCurvature P u + 2 * endpointEscortCoefficient P / u -
    endpointEscortDensity P u / u ^ (2 : ℕ) -
    P * endpointEscortCoefficient P ^ (2 : ℕ) / endpointEscortDensity P u

noncomputable def endpointEscortBaseNumerator (P u : ℝ) : ℝ :=
  (1 - endpointEscortCoefficient P) * u - (1 - endpointEscortCoefficient P) ^ (2 : ℕ) -
    (2/7) * endpointEscortCoefficient P ^ 2 * u ^ (2 : ℕ)

noncomputable def endpointEscortTail (P u : ℝ) : ℝ :=
  u * endpointEscortDensity P u * (1 - u ^ (2 : ℕ)) / (1 + u ^ (2 : ℕ)) ^ (2 : ℕ)

noncomputable def endpointEscortNumerator (P u : ℝ) : ℝ :=
  endpointEscortBaseNumerator P u + (P - 3) * endpointEscortTail P u

theorem endpointEscortCoefficient_bounds {P : ℝ} (hP : 3 ≤ P) (hP₅ : P ≤ 5) :
    (7 / 26 : ℝ) ≤ endpointEscortCoefficient P ∧ endpointEscortCoefficient P ≤ (7 / 12 : ℝ) := by
  have hDen : 0 < P - 1 - 2 / 7 := by linarith only [hP]
  unfold endpointEscortCoefficient
  constructor
  · apply (le_div_iff₀ hDen).mpr
    linarith only [hP₅]
  · apply (div_le_iff₀ hDen).mpr
    linarith only [hP]

theorem endpointEscortDensity_lower {P u : ℝ} (hP : 3 ≤ P) (hP₅ : P ≤ 5) (hu : 0 ≤ u) :
    (5 / 12 : ℝ) ≤ endpointEscortDensity P u := by
  have hc := endpointEscortCoefficient_bounds hP hP₅
  have hc₀ : 0 ≤ endpointEscortCoefficient P := by linarith only [hc.1]
  unfold endpointEscortDensity escortDensity
  nlinarith only [mul_nonneg hc₀ hu,hc.2]

theorem endpointEscortDensity_unit (P : ℝ) : endpointEscortDensity P 1 = 1 := by
  unfold endpointEscortDensity escortDensity
  ring

theorem endpointEscortAtom_unit (P : ℝ) : endpointEscortAtom P 1 = 0 := by
  unfold endpointEscortAtom escortAtom
  change nativeEntropyCost P 1 + endpointEscortDensity P 1 * Real.log 1 -
    P * endpointEscortDensity P 1 * Real.log (endpointEscortDensity P 1) -
    (1 - P * endpointEscortCoefficient P) * (1 - 1) = 0
  rw [endpointEscortDensity_unit,nativeEntropyCost_unit]
  norm_num

theorem endpointEscortSlope_unit (P : ℝ) : endpointEscortSlope P 1 = 0 := by
  unfold endpointEscortSlope
  rw [endpointEscortDensity_unit,nativeEntropyCostSlope_unit]
  norm_num

theorem endpointEscortDensity_deriv (P u : ℝ) :
    HasDerivAt (endpointEscortDensity P) (endpointEscortCoefficient P) u := by
  convert ((hasDerivAt_id u).const_mul (endpointEscortCoefficient P)).add_const (1 - endpointEscortCoefficient P) using 1
  simp only [mul_one]

theorem endpointEscortAtom_deriv {P u : ℝ} (hu : 0 < u) (hRho : 0 < endpointEscortDensity P u) :
    HasDerivAt (endpointEscortAtom P) (endpointEscortSlope P u) u := by
  have hDensity := endpointEscortDensity_deriv P u
  have hOne := hDensity.mul (Real.hasDerivAt_log hu.ne')
  have hTwo := (hDensity.mul (hDensity.log hRho.ne')).const_mul P
  have hAffine := ((hasDerivAt_id u).sub_const 1).const_mul (1 - P * endpointEscortCoefficient P)
  have h := (((nativeEntropyCost_deriv P hu).add hOne).sub hTwo).sub hAffine
  convert h using 1
  · funext x
    simp only [endpointEscortAtom,escortAtom,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,id_eq,endpointEscortDensity]
    ring
  · simp only [endpointEscortSlope,id_eq,mul_one,one_mul]
    field_simp [hu.ne',hRho.ne']
    <;> ring

theorem endpointEscortSlope_deriv {P u : ℝ} (hu : 0 < u) (hRho : 0 < endpointEscortDensity P u) :
    HasDerivAt (endpointEscortSlope P) (endpointEscortRawCurvature P u) u := by
  have hDensity := endpointEscortDensity_deriv P u
  have hOne := (Real.hasDerivAt_log hu.ne').const_mul (endpointEscortCoefficient P)
  have hRatio := hDensity.div (hasDerivAt_id u) hu.ne'
  have hTwo := (hDensity.log hRho.ne').const_mul (P * endpointEscortCoefficient P)
  have h := ((((nativeEntropyCostSlope_deriv P hu).add hOne).add hRatio).sub hTwo).sub_const 1
  unfold endpointEscortSlope endpointEscortRawCurvature
  convert h using 1
  simp only [id_eq,mul_one,one_mul]
  field_simp [hu.ne',hRho.ne']
  <;> ring

theorem endpointEscort_curvature_numerator {P u : ℝ} (hP : 3 ≤ P) (hP₅ : P ≤ 5) (hu : 0 < u) :
    u ^ (2 : ℕ) * endpointEscortDensity P u * endpointEscortRawCurvature P u =
      endpointEscortNumerator P u := by
  have hRho := endpointEscortDensity_lower hP hP₅ hu.le
  have hRho₀ : 0 < endpointEscortDensity P u := by linarith only [hRho]
  have hP₁ : P - 1 - 2 / 7 ≠ 0 := by linarith only [hP]
  have hDen : 1 + u ^ (2 : ℕ) ≠ 0 := by positivity
  unfold endpointEscortRawCurvature endpointEscortNumerator endpointEscortBaseNumerator endpointEscortTail
  generalize hDensityValue : endpointEscortDensity P u = r at hRho₀ ⊢
  unfold nativeEntropyCostCurvature endpointEscortCoefficient
  field_simp [hu.ne',hRho₀.ne',hDen,hP₁]
  rw [← hDensityValue]
  unfold endpointEscortDensity escortDensity endpointEscortCoefficient
  field_simp [hP₁]
  ring_nf
  rw [show (81-P*126+P^2*49)=(-9+P*7)^2 by ring]
  have hD : (-9+P*7)≠0 := by linarith only [hP]
  field_simp [hD]
  <;>ring

end ACS12.NativeCells

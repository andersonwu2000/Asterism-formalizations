import ACS12.PureAdjacentValueData
import ACS12.JointPureUpperStream

/-! The canonical complete endpoint moments and pure-value coefficients in G23–24. -/
namespace ACS12.GammaMeasure

noncomputable def jointPureB (p : ℝ) : ℝ := p ^ 2 + 3 * p + 1 + pureP p - 2 * pureQ p

noncomputable def jointPureD (p : ℝ) : ℝ := pureQ p - pureP p

noncomputable def jointCanonicalMu : ℝ :=
  jointPureLambda * jointPureB (9 / 5) / jointPureD (9 / 5)

noncomputable def jointPureMismatch (p : ℝ) : ℝ :=
  jointCanonicalMu * jointPureD p - jointPureLambda * jointPureB p

theorem jointPure_endpoint_moments :
    (179572464 / 100000000 : ℝ) < pureP (9 / 5) ∧
    pureP (9 / 5) < 179572525 / 100000000 ∧
    (5531453047 / 1000000000 : ℝ) < pureQ (9 / 5) ∧
    pureQ (9 / 5) < 5531453306 / 1000000000 := by
  have hpL := pureZ_upperEndpoint_lower
  have hpU := pureZ_upperEndpoint_tight
  have hqL := powerTail_second_endpoint.1
  have hqU := powerTail_second_endpoint.2
  norm_num [pureZ] at hpL hpU
  norm_num [pureP,pureQ]
  exact ⟨by linarith only [hpL],by linarith only [hpU],
    by linarith only [hqL],by linarith only [hqU]⟩

theorem jointPure_endpoint_coefficients :
    (3735726 / 1000000 : ℝ) < jointPureD (9 / 5) ∧
    jointPureD (9 / 5) < 373573 / 100000 ∧
    (372816 / 1000000 : ℝ) < jointPureB (9 / 5) ∧
    jointPureB (9 / 5) < 372821 / 1000000 := by
  obtain ⟨hP,hP',hQ,hQ'⟩ := jointPure_endpoint_moments
  norm_num [jointPureD,jointPureB]
  exact ⟨by linarith only [hP',hQ],by linarith only [hP,hQ'],
    by linarith only [hP,hQ'],by linarith only [hP',hQ]⟩

theorem jointCanonicalMu_bounds :
    (17762 / 1000000 : ℝ) < jointCanonicalMu ∧ jointCanonicalMu < 17765 / 1000000 := by
  obtain ⟨hD,hD',hB,hB'⟩ := jointPure_endpoint_coefficients
  have h : 0 < jointPureD (9 / 5) := by linarith only [hD]
  unfold jointCanonicalMu jointPureLambda
  exact ⟨(lt_div_iff₀ h).mpr (by linarith only [hD',hB]),
    (div_lt_iff₀ h).mpr (by linarith only [hD,hB'])⟩

theorem jointPureMismatch_endpoint : jointPureMismatch (9 / 5) = 0 := by
  have h : 0 < jointPureD (9 / 5) := by linarith only [jointPure_endpoint_coefficients.1]
  unfold jointPureMismatch jointCanonicalMu
  rw [div_mul_cancel₀ _ h.ne',sub_self]

end ACS12.GammaMeasure

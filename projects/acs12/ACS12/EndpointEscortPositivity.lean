import ACS12.EndpointEscortQuotients
import ACS12.EndpointEscortEndpoints
import ACS12.SingleCrossingSupport

/-! Both positive endpoints and the two curvature crossings close the complete support box. -/
namespace ACS12.NativeCells
open Set
set_option backward.isDefEq.respectTransparency false

theorem endpointEscortAtom_pos {P u : ℝ} (hP : 3≤P) (hP₅ : P≤5)
    (hu : u∈Icc (1/nativeSupportRatio P) (nativeSupportRatio P)) (hu₁ : u≠1) :
    0<endpointEscortAtom P u := by
  obtain ⟨c,hc,hc₀,hLow,hCentral⟩:=endpointEscortNumerator_lower_quotient_crossing hP hP₅
  obtain ⟨b,hb,hMiddle,hHigh⟩:=endpointEscortNumerator_upper_quotient_crossing hP hP₅
  have hR : 1≤nativeSupportRatio P:=by unfold nativeSupportRatio;linarith only [hP]
  have hRho (x : ℝ) (hx : 0<x) : 0<endpointEscortDensity P x := by
    have h:=endpointEscortDensity_lower hP hP₅ hx.le
    linarith only [h]
  have hDen (x : ℝ) (hx : 0<x) : 0<x^2*endpointEscortDensity P x:=
    mul_pos (sq_pos_of_pos hx) (hRho x hx)
  apply ACS12.double_crossing_support_positive
    (div_pos zero_lt_one (nativeSupportRatio_pos hP)) ((div_le_one (nativeSupportRatio_pos hP)).mpr hR)
    hc.1 hc.2 hb hR
    (fun x hx=>endpointEscortAtom_deriv hx.1 (hRho x hx.1))
    (fun x hx=>endpointEscortSlope_deriv hx.1 (hRho x hx.1))
    (hq₁:=endpointEscortAtom_unit P) (hd₁:=endpointEscortSlope_unit P)
    (hqa:=endpointEscortAtom_low_endpoint_pos hP)
    (hqR:=endpointEscortAtom_upper_endpoint_pos hP hP₅) (hx:=hu) (hx₁:=hu₁)
  · intro x hx
    apply nonpos_of_mul_nonpos_right (a:=x^2*endpointEscortDensity P x) _ (hDen x hx.1)
    rw [endpointEscort_curvature_numerator hP hP₅ hx.1]
    exact hLow x ⟨hx.1.le,hx.2⟩
  · intro x hx
    have hx₀ : 0<x:=hc.1.trans hx.1
    apply (mul_pos_iff_of_pos_left (hDen x hx₀)).mp
    rw [endpointEscort_curvature_numerator hP hP₅ hx₀]
    by_cases hx₁ : x≤1
    · exact hCentral x ⟨hx.1,hx₁⟩
    · exact hMiddle x ⟨lt_of_not_ge hx₁,hx.2.trans_le (min_le_right _ _)⟩
  · intro x hx
    have hx₀ : 0<x:=zero_lt_one.trans (hb.trans hx.1)
    apply nonpos_of_mul_nonpos_right (a:=x^2*endpointEscortDensity P x) _ (hDen x hx₀)
    rw [endpointEscort_curvature_numerator hP hP₅ hx₀]
    exact hHigh x hx.1.le

theorem endpointEscortAtom_nonneg {P u : ℝ} (hP : 3≤P) (hP₅ : P≤5)
    (hu : u∈Icc (1/nativeSupportRatio P) (nativeSupportRatio P)) :
    0≤endpointEscortAtom P u := by
  by_cases h : u=1
  · rw [h,endpointEscortAtom_unit]
  · exact (endpointEscortAtom_pos hP hP₅ hu h).le

end ACS12.NativeCells

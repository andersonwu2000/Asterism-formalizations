import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Fatou returns a measurable limit with a uniform integral bound on an arbitrary sample space. -/
namespace ACS12
open MeasureTheory Filter

theorem integrable_of_ae_tendsto_bounded_integrals {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {F : ℕ → Ω → ℝ} {f : Ω → ℝ} {C : ℝ}
    (hF : ∀ n, Integrable (F n) μ) (hf : AEStronglyMeasurable f μ)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => F n ω) atTop (nhds (f ω)))
    (hBound : ∀ n, (∫ ω, ‖F n ω‖ ∂μ) ≤ C) : Integrable f μ := by
  have hLim : (∫⁻ ω, ‖f ω‖ₑ ∂μ) ≤ liminf (fun n => ∫⁻ ω, ‖F n ω‖ₑ ∂μ) atTop := by
    have hEq : (fun ω => liminf (fun n => ‖F n ω‖ₑ) atTop) =ᵐ[μ] fun ω => ‖f ω‖ₑ :=
      hlim.mono fun ω hω => hω.enorm.liminf_eq
    rw [← lintegral_congr_ae hEq]
    exact lintegral_liminf_le' fun n => (hF n).aestronglyMeasurable.enorm
  have hB (n : ℕ) : (∫⁻ ω, ‖F n ω‖ₑ ∂μ) ≤ ENNReal.ofReal C := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hF n)]
    exact ENNReal.ofReal_le_ofReal (hBound n)
  have hEvent : ∀ᶠ n : ℕ in atTop, (∫⁻ ω, ‖F n ω‖ₑ ∂μ) ≤ ENNReal.ofReal C :=
    Eventually.of_forall hB
  have hL := liminf_le_of_frequently_le' hEvent.frequently
  exact ⟨hf,lt_of_le_of_lt (hLim.trans hL) ENNReal.ofReal_lt_top⟩

end ACS12

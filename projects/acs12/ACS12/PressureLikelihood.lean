import CenteredCircle.IntegralProductComparison

/-! Whole-ray expectation comparison under a monotone likelihood ratio. -/
namespace ACS12.Pressure

open Set Filter MeasureTheory CenteredCircle.AllN

theorem likelihood_test_mono {d₁ d₂ T : ℝ → ℝ}
    (h₁ : IntegrableOn d₁ (Ioi 0)) (h₂ : IntegrableOn d₂ (Ioi 0))
    (hT₁ : IntegrableOn (fun s => d₁ s * T s) (Ioi 0))
    (hT₂ : IntegrableOn (fun s => d₂ s * T s) (Ioi 0))
    (hP : ∀ s > 0, 0 < d₁ s)
    (hRatio : MonotoneOn (fun s => d₂ s / d₁ s) (Ioi 0)) (hT : MonotoneOn T (Ioi 0)) :
    (∫ s : ℝ in Ioi 0, d₁ s * T s) * (∫ s : ℝ in Ioi 0, d₂ s) ≤
      (∫ s : ℝ in Ioi 0, d₂ s * T s) * (∫ s : ℝ in Ioi 0, d₁ s) := by
  let F (s : ℝ) := d₂ s * T s
  let H (s : ℝ) := d₁ s * T s
  let μ := volume.restrict (Ioi (0 : ℝ))
  have hOrdered (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (h : s ≤ t) :
      0 ≤ F s * d₁ t + F t * d₁ s - H s * d₂ t - H t * d₂ s := by
    have h₀ := hRatio hs ht h
    have h₁ := (div_le_div_iff₀ (hP s hs) (hP t ht)).mp h₀
    have hR : 0 ≤ d₁ s * d₂ t - d₁ t * d₂ s := by linarith only [h₁]
    have hS := sub_nonneg.mpr (hT hs ht h)
    have hE : (T t - T s) * (d₁ s * d₂ t - d₁ t * d₂ s) =
        F s * d₁ t + F t * d₁ s - H s * d₂ t - H t * d₂ s := by
      dsimp only [F,H]
      ring
    exact hE ▸ mul_nonneg hS hR
  have hPair : ∀ᵐ s ∂μ, ∀ᵐ t ∂μ, 0 ≤ F s * d₁ t + F t * d₁ s - H s * d₂ t - H t * d₂ s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rcases le_total s t with h | h
    · exact hOrdered s t hs ht h
    · linarith only [hOrdered t s ht hs h]
  exact integral_product_comparison hT₂ h₁ hT₁ h₂ hPair

theorem likelihood_test_anti {d₁ d₂ T : ℝ → ℝ}
    (h₁ : IntegrableOn d₁ (Ioi 0)) (h₂ : IntegrableOn d₂ (Ioi 0))
    (hT₁ : IntegrableOn (fun s => d₁ s * T s) (Ioi 0))
    (hT₂ : IntegrableOn (fun s => d₂ s * T s) (Ioi 0))
    (hP : ∀ s > 0, 0 < d₁ s)
    (hRatio : MonotoneOn (fun s => d₂ s / d₁ s) (Ioi 0)) (hT : AntitoneOn T (Ioi 0)) :
    (∫ s : ℝ in Ioi 0, d₂ s * T s) * (∫ s : ℝ in Ioi 0, d₁ s) ≤
      (∫ s : ℝ in Ioi 0, d₁ s * T s) * (∫ s : ℝ in Ioi 0, d₂ s) := by
  have hT₁' : IntegrableOn (fun s => d₁ s * (-T s)) (Ioi 0) := by simpa only [mul_neg] using hT₁.neg
  have hT₂' : IntegrableOn (fun s => d₂ s * (-T s)) (Ioi 0) := by simpa only [mul_neg] using hT₂.neg
  have h := likelihood_test_mono h₁ h₂ hT₁' hT₂' hP hRatio (fun s hs t ht h => neg_le_neg (hT hs ht h))
  simp only [mul_neg,integral_neg,neg_mul] at h
  exact neg_le_neg_iff.mp h

end ACS12.Pressure

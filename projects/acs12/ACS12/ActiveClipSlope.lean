import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Order.Compact

/-! An exponent slope budget survives every positive-part contact. -/

namespace ACS12

open Set

theorem max_zero_le_add_of_activeSlope {f f' : ℝ → ℝ} {p q c : ℝ}
    (hpq : p ≤ q) (hc : 0 ≤ c) (hf : ∀ x, HasDerivAt f (f' x) x)
    (h : ∀ x ∈ Icc p q, 0 < f x → -c ≤ f' x) :
    max 0 (f p) ≤ max 0 (f q) + c * (q - p) := by
  rcases le_or_gt (f p) 0 with hp | hp
  · rw [max_eq_left hp]
    exact add_nonneg (le_max_left _ _) (mul_nonneg hc (sub_nonneg.mpr hpq))
  let g (x : ℝ) := f x + c * x
  have hC : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hD (x : ℝ) : HasDerivAt g (f' x + c) x := by
    simpa only [g, id_eq, mul_one, Pi.add_apply] using (hf x).add ((hasDerivAt_id x).const_mul c)
  have hMono (s : ℝ) (hs : s ∈ Icc p q) (hPos : ∀ x ∈ Ioo p s, 0 < f x) : g p ≤ g s := by
    have hA : MonotoneOn g (Icc p s) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      · exact fun x _ => (hD x).continuousAt.continuousWithinAt
      · exact fun x _ => (hD x).differentiableAt.differentiableWithinAt
      · intro x hx
        have hx' : x ∈ Ioo p s := by simpa only [interior_Icc] using hx
        have hX := h x ⟨hx'.1.le, hx'.2.le.trans hs.2⟩ (hPos x hx')
        rw [(hD x).deriv]
        linarith only [hX]
    exact hA ⟨le_rfl, hs.1⟩ ⟨hs.1, le_rfl⟩ hs.1
  let S := Icc p q ∩ f ⁻¹' Iic 0
  by_cases hs : S.Nonempty
  · have hS : IsCompact S := isCompact_Icc.inter_right (isClosed_Iic.preimage hC)
    obtain ⟨s, hS⟩ := hS.exists_isLeast hs
    have hs' : s ∈ Icc p q := hS.1.1
    have hNeg : f s ≤ 0 := hS.1.2
    have hL := hMono s hs' (fun x hx => by
      by_contra! hn
      exact hx.2.not_ge (hS.2 (show x ∈ S from ⟨⟨hx.1.le, hx.2.le.trans hs'.2⟩, hn⟩)))
    have hQ := mul_le_mul_of_nonneg_left hs'.2 hc
    rw [max_eq_right hp.le]
    dsimp only [g] at hL
    nlinarith only [hL, hNeg, hQ, le_max_left 0 (f q)]
  · have hL := hMono q ⟨hpq, le_rfl⟩ (fun x hx => by
      by_contra! hn
      exact hs ⟨x, ⟨⟨hx.1.le, hx.2.le⟩, hn⟩⟩)
    rw [max_eq_right hp.le]
    dsimp only [g] at hL
    nlinarith only [hL, le_max_right 0 (f q)]

end ACS12

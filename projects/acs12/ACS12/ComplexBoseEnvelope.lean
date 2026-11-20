import ACS12.ComplexBoseBounds
import ACS12.BosePolynomialTail

/-! The original complex Bose integrand has one integrable envelope on each compact positive-shape rectangle. -/
namespace ACS12.NativeCells
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

theorem complexBose_rect_uniform_envelope {a b T N : ℝ} (ha : 0 < a)
    (hT : 0 ≤ T) (hN : 0 < N) :
    ∃ G : ℝ → ℝ, IntegrableOn G (Ioi 0) ∧
      ∀ α : ℂ, α.re/2 ∈ Icc a b → |α.im/2| ≤ T →
        ∀ ξ : ℝ, 0 < ξ → ‖complexBoseKernel N α ξ‖ ≤ G ξ := by
  obtain ⟨B,hB,hGamma⟩ := GammaMeasure.realGamma_compact_bound (b:=b) ha
  obtain ⟨C,hC,k,hTail⟩ := complexGammaPair_rect_tail (b:=b) ha hT
  let L := T+1
  let d := 2*Real.pi/N
  let A := B^2*(Real.pi*Real.exp (Real.pi*L)/d)
  let D := C*(1-Real.exp (-d*L))⁻¹
  let G (ξ : ℝ) := if ξ ≤ L then A else D*(1+ξ)^k*Real.exp (-d*ξ)
  have hL : 0 < L := by dsimp only [L]; linarith only [hT]
  have hL₁ : 1 ≤ L := by dsimp only [L]; linarith only [hT]
  have hd : 0 < d := by dsimp only [d]; positivity
  have hNear : IntegrableOn G (Ioc 0 L) := by
    have hI : IntegrableOn (fun _ : ℝ => A) (Ioc 0 L) := integrableOn_const (by simp)
    apply hI.congr_fun _ measurableSet_Ioc
    intro ξ hξ
    dsimp only [G]
    rw [if_pos hξ.2]
  have hFar : IntegrableOn G (Ioi L) := by
    have hSub : Ioi L ⊆ Ioi (1:ℝ) := by
      intro ξ hξ
      exact hL₁.trans_lt hξ
    have hI : IntegrableOn (fun ξ : ℝ => D*((1+ξ)^k*Real.exp (-d*ξ))) (Ioi L) :=
      ((integrableOn_bosePolynomialTail hd k).mono_set hSub).const_mul D
    apply hI.congr_fun _ measurableSet_Ioi
    intro ξ hξ
    dsimp only [G]
    rw [if_neg (not_le.mpr hξ)]
    ring
  have hG : IntegrableOn G (Ioi 0) := by
    rw [←Ioc_union_Ioi_eq_Ioi hL.le,integrableOn_union]
    exact ⟨hNear,hFar⟩
  refine ⟨G,hG,?_⟩
  intro α hα hIm ξ hξ
  by_cases hξL : ξ ≤ L
  · dsimp only [G]
    rw [if_pos hξL]
    exact complexBoseKernel_origin_bound hN hξ hξL (sq_nonneg B)
      (complexGammaPair_norm_bound ha hα hGamma ξ)
  · dsimp only [G]
    rw [if_neg hξL]
    simpa only [D,d,mul_assoc] using
      complexBoseKernel_tail_bound k hN hL (le_of_not_ge hξL) hC.le
        (hTail α hα hIm ξ (le_of_not_ge hξL))

end ACS12.NativeCells
